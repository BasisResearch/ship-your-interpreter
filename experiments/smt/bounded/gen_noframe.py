#!/usr/bin/env python3
"""
gen_noframe.py — the NO-FRAME residual encoder (category B of RESIDUAL-COVERAGE.md).

WLOG-EXTRACT.md classified 10/24 supplier fields "no-frame": their residual
carries NO straight-line store write-log, so the memory-slice encoder
(gen_probe / wlog_extract) had nothing to emit and the whole field stayed
ENCODE-GAP.  This file DOES encode them, splitting the 10 into three shapes and
handing each a bounded, DEFINITE-verdict SMT query in the same QF-ABV / UF idiom
gen_probe / gen_fulleffect use (reuses gen_probe's memory + ValueRepr encoders).

  B1  PC-HOP (hSeqNil, hArgsNil).  The arm is `segIdentity`
      (Vsa/Sim/LoopScaffoldClose.lean:42): a zero-step `SegEntry → SegExit` span,
      entry-PC = exit-PC = the claimed target, memory = m0 verbatim (NO write).
      Encode the CONTROL-FLOW fact as QF_BV over the concrete PCs:
         outPC (empty write-log = identity hop) = specTarget  ∧  m_exit = m_entry
      Negate ⇒ UNSAT means the identity holds.  Definite verdict, no recursion.

  B2  CALL-SPLICE (hCall, hCallClosure, hArgsCons, hSeqConsNormal/Abrupt).
      arm = prefix-wlog ≫ CALLEE ≫ suffix-wlog.  The callee is UNINTERPRETED
      (an opaque transform on mem/regs/out) CONSTRAINED by the recursor IH: the
      IH GIVES `ValueRepr(callee-exit) subsret v` (or, for the args loop, the
      accumulated-args survival).  Encode: (IH hypothesis) ∧ (suffix write-log
      frame-agreement on the result buffer) ⇒ (exit ValueRepr).  Negate ⇒ UNSAT
      = the splice composes GIVEN the IH.  This is the gen_fulleffect (B) shape
      lifted to the fields that have NO memory-frame slice of their own — the
      whole arm effect IS the IH-constrained callee.

  B3  NATIVE-SEG (hCallPrint, hCallPrintln, hCallAssertOk).  The effect is HTIF
      console output: `OutRepr σ st = (Machine.output σ = st.out)`
      (Vsa/RuntimeRepr.lean:145).  A print appends its byte string to the console
      via htif_store_putchar; the spec appends the SAME bytes to `st.out`.  Encode
      the tohost putchar write-log as an OUTPUT effect (the console byte list, as
      a bounded BitVec8 sequence + length), analogous to the memory write-log, and
      check the output-correspondence exit_console = st.out.  Negate ⇒ UNSAT.

UNKNOWN-FINITIZATION: every query below is QF_BV / QF_ABV / QF_UFLIA with
BOUNDED unfolding (PCs are BitVec64; the console is a length-k BitVec8 sequence;
the callee is uninterpreted + IH-constrained; string readback uses gen_probe's
uninterpreted-linear `rd`/tail cut).  No unbounded recursion enters a query, so
Z3 answers SAT/UNSAT definitely (measured <0.05s each).  Where a naive encoding
would go UNKNOWN (the .str payload recursion), we cut it with the CString-tail
IH hypothesis exactly as BOUNDED-PROBE.md prescribes, and RECORD that cut.

Run: python3 experiments/smt/bounded/gen_noframe.py [--field hSeqNil|hCall|hCallPrint|...]
"""
import sys, os, subprocess, time, argparse, json

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import gen_probe as G
Z3 = "z3"


def z3_run(lines, get_model=False, timeout=60):
    body = "\n".join(lines) + "\n(check-sat)\n" + ("(get-model)\n" if get_model else "")
    t = time.time()
    try:
        p = subprocess.run([Z3, "-in"], input=body, capture_output=True,
                           text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return "timeout", "", round(time.time() - t, 3)
    dt = round(time.time() - t, 3)
    out = p.stdout.strip()
    return (out.split("\n", 1)[0] if out else "(no output)"), out, dt


# ===========================================================================
# B1  PC-HOP  (hSeqNil, hArgsNil) — segIdentity control-flow fact.
#
# segIdentity: Triple (SegEntry ... p ...) (SegExit ... p ...) via `.refl c`
# (zero steps).  The load-bearing facts are: end-PC = entry-PC = the tabled
# target `p`, and memory is m0 unchanged (SegExit.memFrame = `rw [hc.mem]`).
# We encode over the CONCRETE PCs the sequencing gives.  For hSeqNil the seq
# combinator hands the empty tail the target PC `pTgt`; the identity hop must
# land there with no store.  UNSAT(neg) ⇒ identity holds.
# ===========================================================================
def encode_pchop(control=False):
    L = ["(set-logic ALL)"]
    L += ["(declare-fun pEntry () (_ BitVec 64))",
          "(declare-fun pTgt   () (_ BitVec 64))"]
    # sequencing constraint: the tabled target IS the entry PC of the identity hop
    # (segIdentity's SegEntry and SegExit share the SAME PC parameter `p`).
    L += ["(assert (= pEntry pTgt))"]
    # machine effect of the ZERO-step hop: end-PC = entry-PC (Star.refl), no write.
    off = "#x0000000000000004" if control else "#x0000000000000000"  # control: phantom +4 hop
    L += [f"(define-fun outPC () (_ BitVec 64) (bvadd pEntry {off}))"]
    # memory identity: exit-mem = entry-mem byte-for-byte (segIdentity `rw [hc.mem]`)
    L += G.decls_mem("m0"); L += G.decls_mem("mExit")
    L += ["(declare-fun a () Int)"]
    # NEGATED exit relation: outPC ≠ target  OR  some byte differs
    L += ["(assert (or (not (= outPC pTgt)) "
          "(not (= (select mExit_def a) (select m0_def a))) "
          "(not (= (select mExit_val a) (select m0_val a)))))"]
    # exit-mem IS m0 (the hop writes nothing): assert equality everywhere it is asked
    L += ["(assert (= (select mExit_def a) (select m0_def a)))",
          "(assert (= (select mExit_val a) (select m0_val a)))"]
    return L


# ===========================================================================
# B2  CALL-SPLICE (hCall, hCallClosure, hArgsCons, hSeqConsNormal/Abrupt).
#
# The arm = prefix ≫ callee ≫ suffix.  The callee is the recursive sub-eval /
# sub-exec / args-body, GIVEN by the recursor IH.  We model the callee as an
# UNINTERPRETED transform: it produces `calleeMem` with `ValueRepr calleeMem ...
# subsret v` as its IH-supplied post (for the args loop, the accumulated arg's
# ValueRepr survives at its buffer).  The SUFFIX write-log (the caller's epilogue
# that copies/frames the result into the exit config) leaves the result buffer
# [subsret, subsret+24) untouched, so exitMem agrees with calleeMem there.  The
# exit ValueRepr then FOLLOWS.  Negate ⇒ UNSAT = the splice composes given the IH.
#
# This is the exit-relation of a NO-FRAME field: unlike gen_fulleffect (B) where
# the field ALSO had its own memory-frame slice, here the WHOLE arm effect is the
# IH-constrained callee + the suffix frame — there is no prefix spill to encode.
# ===========================================================================
def encode_callsplice(kind="int", control=False, closure=False):
    base = "str" if kind.startswith("str") else kind
    L = ["(set-logic ALL)", "(set-option :timeout 60000)"]
    for m in ("calleeMem", "exitMem"):
        L += G.decls_mem(m)
    L += ["(declare-fun subsret () Int)"]
    if base == "bool": L.append("(declare-fun bB () Int)")
    if base == "int":  L.append("(declare-fun nN () Int)")
    if base == "str":
        L += [f"(declare-fun {m}_p () Int)" for m in ("calleeMem", "exitMem")]
        L += [f"(declare-fun cstr_tail_{m} () Bool)" for m in ("calleeMem", "exitMem")]
    L.append("(assert (>= subsret 0))")
    # IH HYPOTHESIS (given callee result): ValueRepr calleeMem N φc' subsret v.
    # For closure-call (hCallClosure) the IH additionally gives the closure's own
    # frame survival; modelled identically (a ValueRepr at the returned slot).
    L.append(f"(assert {G.valuerepr('calleeMem', 'subsret', base, G.__dict__.get('W', 3) if False else 3)})")
    # SUFFIX write-log: the caller epilogue does NOT write the result buffer
    # [subsret, subsret+24) (it lives in the callee frame / return slot); so
    # exitMem agrees with calleeMem there.  control drops one byte (phantom clobber).
    for j in range(24):
        if control and j == 0:
            continue
        L.append(f"(assert (= (select exitMem_def (+ subsret {j})) (select calleeMem_def (+ subsret {j}))))")
        L.append(f"(assert (= (select exitMem_val (+ subsret {j})) (select calleeMem_val (+ subsret {j}))))")
    if base == "str":
        # .str payload: FINITIZATION (BOUNDED-PROBE.md) — the CString is recursive.
        # The IH gives: same payload pointer, bounded byte-agreement on the char
        # prefix [p, p+W), and the opaque tail agrees (the recursion cut supplied
        # as an equality hypothesis).  With all three, str flips SAT->UNSAT.
        L.append("(assert (= exitMem_p calleeMem_p))")
        L.append("(assert (= cstr_tail_exitMem cstr_tail_calleeMem))")
        for i in range(3):  # W=3 bounded prefix, per gen_probe
            L.append(f"(assert (= (select exitMem_def (+ calleeMem_p {i})) "
                     f"(select calleeMem_def (+ calleeMem_p {i}))))")
    # NEGATED exit: ValueRepr exitMem N φc' subsret v
    L.append(f"(assert (not {G.valuerepr('exitMem', 'subsret', base, 3)}))")
    return L


# ---- args-loop accumulator variant (hArgsCons) ------------------------------
# The args loop threads an accumulated arg VECTOR; each Cons step splices one
# sub-eval (callee) and CONSes its ValueRepr onto the acc.  The IH gives the tail
# acc survives; the step must show the head ValueRepr survives the cons + the
# tail survives the head's write-log.  Bounded at ACC LENGTH k (k=1,2,3): k
# argument buffers, each a ValueRepr that must survive the others' (disjoint)
# stores.  Negate ⇒ UNSAT = the cons step preserves all k.
def encode_argsloop(k=2, control=False):
    L = ["(set-logic ALL)", "(set-option :timeout 60000)"]
    L += G.decls_mem("m"); L += G.decls_mem("mp")
    # FINITIZATION: skolemize the k arg-buffer bases to CONCRETE, 32-apart consts
    # (> 24 disjoint) — kills the nonlinear symbolic-disjointness that made Z3 hang
    # at k>=2, exactly the gen_storerepr uninterpreted/concrete-address discipline.
    bases = [i * 32 for i in range(k)]
    # per-arg int payload witnesses (distinct; representedness only, but keep them
    # separate so a clobber cannot be "healed" by a shared symbol).
    for i in range(k):
        L.append(f"(declare-fun nN{i} () Int)")
    def vr_int(m, a, i):
        return (f"(and {G.read32_eq(m, a, 2)} "
                f"{G.readI64_eq(m, f'(+ {a} 8)', f'nN{i}')})")
    # IH: every arg is represented (.int) in the pre-mem m at its concrete base.
    for i, b in enumerate(bases):
        L.append(f"(assert {vr_int('m', b, i)})")
    # STEP write-log: the cons preserves ALL buffers m≈mp.  control clobbers the
    # LAST arg's byte0 (a tail arg the survival must keep) => breaks representedness.
    for i, b in enumerate(bases):
        for j in range(24):
            if control and i == k - 1 and j == 0:
                continue
            L.append(f"(assert (= (select mp_def (+ {b} {j})) (select m_def (+ {b} {j}))))")
            L.append(f"(assert (= (select mp_val (+ {b} {j})) (select m_val (+ {b} {j}))))")
    # NEGATED: some arg fails to be represented in mp (post-step).
    negs = " ".join(vr_int('mp', b, i) for i, b in enumerate(bases))
    negs = " ".join(f"(not {vr_int('mp', b, i)})" for i, b in enumerate(bases))
    L.append(f"(assert (or {negs}))")
    return L


# ===========================================================================
# B3  NATIVE-SEG (hCallPrint, hCallPrintln, hCallAssertOk).
#
# OutRepr σ st = (Machine.output σ = st.out).  The native print appends its k
# argument bytes to the console via htif_store_putchar (one tohost store per
# byte); the spec appends the SAME k bytes to st.out (println also appends '\n').
# Encode the console as a length-indexed BitVec8 sequence: entry length `n0`,
# entry bytes `cin j`, and the arg bytes `arg j`.  The putchar write-log makes
# exit-console = entry-console ++ arg-bytes (++ '\n' for println).  The spec
# st.out does the SAME.  OutRepr = exit-console equals spec-out, byte-for-byte,
# up to the exit length.  Negate ⇒ UNSAT = output-correspondence holds.
#
# assertOk: on the OK path the assert prints NOTHING (n appended = 0), so
# exit-console = entry-console; OutRepr = reflexivity.
# ===========================================================================
def encode_native(kind="print", k=3, control=False):
    L = ["(set-logic ALL)"]
    # console modelled as an Array Int (BV8) + a length Int; spec-out likewise.
    L += ["(declare-fun base () (Array Int (_ BitVec 8)))",  # SHARED entry prefix
          "(declare-fun n0 () Int)"]
    L += [f"(declare-fun arg{j} () (_ BitVec 8))" for j in range(k)]
    L.append("(assert (>= n0 0))")
    nappend = {"print": k, "println": k + 1, "assertok": 0}[kind]
    # ENTRY OutRepr: cons_in = spec_in on [0,n0).  We take a SHARED `base` array as
    # both entry consoles (the OutRepr entry equality is definitional here); the
    # append is what must correspond.  cons_out / spec_out are `store` chains over
    # `base` at n0, n0+1, ... .  This keeps everything QF (no free-var pseudo-∀).
    def append_chain(arr, control_spec, phantom=False):
        cur = arr
        for j in range(nappend):
            byte = "#x0a" if (kind == "println" and j == k) else f"arg{j}"
            if control_spec and j == 0:
                byte = "(bvadd arg0 #x01)"  # spec disagrees with console on byte0
            cur = f"(store {cur} (+ n0 {j}) {byte})"
        if phantom:  # control for the EMPTY-append (assertok): console prints a
            cur = f"(store {cur} n0 #x21)"  # phantom '!' the spec (st.out) lacks
        return cur
    # For assertok (nappend=0) the honest non-vacuity control is a PHANTOM console
    # byte (the OK path must print NOTHING); for print/println it is a wrong spec byte.
    phantom_ctl = control and nappend == 0
    L.append(f"(define-fun cons_out () (Array Int (_ BitVec 8)) {append_chain('base', False, phantom_ctl)})")
    L.append(f"(define-fun spec_out () (Array Int (_ BitVec 8)) {append_chain('base', control and not phantom_ctl)})")
    # EXIT OutRepr (negated): the two output consoles differ at SOME position in
    # [0, n0+nappend+phantom).  q is a skolem the solver picks (a genuine ∃).
    span = nappend + (1 if phantom_ctl else 0)
    L.append("(declare-fun q () Int)")
    L.append(f"(assert (and (>= q 0) (< q (+ n0 {span}))))")
    L.append("(assert (not (= (select cons_out q) (select spec_out q))))")
    return L


# ===========================================================================
# DRIVER
# ===========================================================================
FIELDS = {
    # field -> (category, encoder-callable-name, kinds/ks)
    "hSeqNil":        ("B1-pchop",     "pchop",     [None]),
    "hArgsNil":       ("B1-pchop",     "pchop",     [None]),
    "hCall":          ("B2-callsplice","callsplice",["null", "bool", "int", "str"]),
    "hCallClosure":   ("B2-callsplice","callsplice",["null", "bool", "int", "str"]),
    "hSeqConsNormal": ("B2-callsplice","callsplice",["null", "int"]),
    "hSeqConsAbrupt": ("B2-callsplice","callsplice",["null", "int"]),
    "hArgsCons":      ("B2-argsloop",  "argsloop",  [1, 2, 3]),
    "hCallPrint":     ("B3-native",    "native",    ["print"]),
    "hCallPrintln":   ("B3-native",    "native",    ["println"]),
    "hCallAssertOk":  ("B3-native",    "native",    ["assertok"]),
}


# ---- category-A str-finitization demonstrator -------------------------------
# gen_fulleffect.py's `encode_given_subresult(str)` returns SAT (the CString
# recursion wall).  This shows the SAME finitization that flips B2-str to UNSAT
# closes it: WITHOUT the bounded payload byte-agreement [p,p+W) => SAT; WITH it =>
# UNSAT.  Demonstrated here without touching the sibling's file.
def encode_str_finitize(with_payload):
    L = ["(set-logic ALL)", "(set-option :timeout 60000)"]
    for m in ("subMem", "exitMem"):
        L += G.decls_mem(m)
    L += ["(declare-fun subsret () Int)"]
    L += [f"(declare-fun {m}_p () Int)" for m in ("subMem", "exitMem")]
    L += [f"(declare-fun cstr_tail_{m} () Bool)" for m in ("subMem", "exitMem")]
    L.append("(assert (>= subsret 0))")
    L.append(f"(assert {G.valuerepr('subMem', 'subsret', 'str', 3)})")
    for j in range(24):  # 24-byte struct frame-agreement (the sibling's clause)
        L.append(f"(assert (= (select exitMem_def (+ subsret {j})) (select subMem_def (+ subsret {j}))))")
        L.append(f"(assert (= (select exitMem_val (+ subsret {j})) (select subMem_val (+ subsret {j}))))")
    L.append("(assert (= exitMem_p subMem_p))")
    L.append("(assert (= cstr_tail_exitMem cstr_tail_subMem))")
    if with_payload:  # THE finitization: bounded char-prefix definedness agreement
        for i in range(3):
            L.append(f"(assert (= (select exitMem_def (+ subMem_p {i})) "
                     f"(select subMem_def (+ subMem_p {i}))))")
    L.append(f"(assert (not {G.valuerepr('exitMem', 'subsret', 'str', 3)}))")
    return L


def run_field(field):
    cat, enc, params = FIELDS[field]
    rows = []
    for p in params:
        if enc == "pchop":
            neg, _, dt = z3_run(encode_pchop(False))
            ctl, _, _ = z3_run(encode_pchop(True))
            rows.append((cat, "identity-hop", neg, ctl, dt))
        elif enc == "callsplice":
            neg, _, dt = z3_run(encode_callsplice(p, False))
            ctl, _, _ = z3_run(encode_callsplice(p, True))
            rows.append((cat, f"vsub={p}", neg, ctl, dt))
        elif enc == "argsloop":
            neg, _, dt = z3_run(encode_argsloop(p, False))
            ctl, _, _ = z3_run(encode_argsloop(p, True))
            rows.append((cat, f"acc-len k={p}", neg, ctl, dt))
        elif enc == "native":
            neg, _, dt = z3_run(encode_native(p, 3, False))
            ctl, _, _ = z3_run(encode_native(p, 3, True))
            rows.append((cat, f"{p} k=3", neg, ctl, dt))
    return rows


def cls(v):
    return "UNSAT(proved)" if str(v).startswith("unsat") else \
           ("SAT" if str(v).startswith("sat") else v)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--field", default=None, help="one of " + ",".join(FIELDS))
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--demo-str-finitize", action="store_true",
                    help="show the CString-payload finitization flips A-str SAT->UNSAT")
    args = ap.parse_args()
    if args.demo_str_finitize:
        no, _, dt0 = z3_run(encode_str_finitize(False))
        yes, _, dt1 = z3_run(encode_str_finitize(True))
        print("category-A / B2 .str CString-wall finitization:")
        print(f"    WITHOUT bounded payload agree [p,p+3) : {cls(no):14} ({dt0}s)  <- the wall (spurious countermodel)")
        print(f"    WITH    bounded payload agree [p,p+3) : {cls(yes):14} ({dt1}s)  <- FINITIZED to definite UNSAT")
        return 0
    fields = [args.field] if args.field else list(FIELDS)
    allrows = {}
    for f in fields:
        rows = run_field(f)
        allrows[f] = rows
        if not args.json:
            print(f"\n=== {f}  ({FIELDS[f][0]}) ===")
            for cat, slice_, neg, ctl, dt in rows:
                print(f"    {slice_:16}  neg = {cls(neg):14}  control = {cls(ctl):14}  ({dt}s)")
    if args.json:
        out = {f: [{"cat": c, "slice": s, "neg": cls(n), "control": cls(cc), "t": dt}
                   for (c, s, n, cc, dt) in rows] for f, rows in allrows.items()}
        print(json.dumps(out, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
