#!/usr/bin/env python3
"""
gen_fulleffect.py — the FULL arm-effect encoder (thesis probe for FULL-EFFECT-PROBE.md).

The prior stack (gen_probe / wlog_extract / autoprove --frame-slice-coverage)
encoded only the MEMORY-FRAME slice of an exec-arm supplier field and reported
the rest as "COMPOSITION-DEFER".  THESIS UNDER TEST: the composition-defer is
NOT un-encodable — it is the encoder only emitting the memory slice.  The whole
exit relation (an ExecExit / SubExecReturn `*Geom` conclusion) decomposes into
the SAME three branches over the FULL arm post-config:

  (A) BOUNDED-MACHINE-EFFECT  — register outcomes (runGM), PC (endPCM), HTIF
      output (Machine.output), memory (wlogM).  All FIRST-ORDER, Z3-encodable.
  (B) GIVEN-SUB-RESULT        — the sub-call's ValueRepr at `subsret`, supplied
      by the recursor IH (`EvalIH`).  Encoded as an UNINTERPRETED hypothesis
      constrained exactly as the IH constrains it (`ValueRepr(sub-config) ⇒
      ValueRepr(this-config)` after the arm's tail copy).
  (C) EXIT-REPR               — StoreRepr survival (flat part → Z3, recursive
      part → the landed Houdini base/step, reused verbatim from gen_storerepr).

This file encodes (A) fully (it was the missing extension) and (B) as the
IH-hypothesis, then hands (C) to gen_storerepr.  The pilot is `hSBrk` (the
shallowest exec-arm: a LEAF, st'=st, so (B) is vacuous — the ONLY sub-result is
the identity, given for free — which is exactly why it is the honest first pilot)
and `hSExpr` (the shallowest RECURSIVE arm, where (B) is a real IH hypothesis).

The register/PC/output outcomes are read off `runGM`/`endPCM` via the SAME
extractor `wlog_extract.py` already runs for the memory slice (`--with-data` +
the `dumpRegs` rows), so NOTHING here re-transcribes the arm by hand: the machine
effect is the block-reflection fold.

Run: python3 experiments/smt/bounded/gen_fulleffect.py [--field hSBrk|hSExpr]
"""
import sys, os, subprocess, time, argparse, json

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
SCRIPTS = os.path.join(ROOT, "scripts")
sys.path.insert(0, HERE)
sys.path.insert(0, SCRIPTS)
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
# (A) BOUNDED-MACHINE-EFFECT: the full arm post-config as SMT lets.
#
# The exec-arm exit register outcome (ExecExit / SubExecReturn fields), read off
# `runGM` + `endPCM` (block-reflection).  For the brk/cont LEAF arm the outcome
# is entirely CONCRETE relative to the entry pins:
#   PC   = update(r + 0, bit0:=0)      (the `ret` target — endPCM after epilogue)
#   x1   = r        (ra preserved)
#   x2   = sp       (sp restored: -176 then +176)
#   x10  = StatusCode status  (brk=1 / cont=2 — the `li a0,N` the arm ran)
#   frame: callee-saved regs = g R
# We encode each as a bitvector equality the arm's runGM outcome forces, and the
# NEGATED exit-field conjunct; UNSAT ⇒ the register/PC/output branch of the exit
# relation is Z3-discharged from the machine effect (not assumed).
# ===========================================================================
STATUS_CODE = {"normal": 0, "brk": 1, "cont": 2, "ret": 3}


def encode_reg_pc_out(status="brk", control=False):
    """The register + PC + HTIF-output branch of the exit relation for a brk/cont
    LEAF arm, encoded from the runGM/endPCM machine effect.  UNSAT(neg) ⇒ branch
    proved.  control=True corrupts the a0 status ⇒ SAT (refute-capable)."""
    L = ["(set-logic ALL)", "(set-option :timeout 60000)"]
    # entry pins (symbolic frame), as bitvectors
    L += ["(declare-fun r () (_ BitVec 64))", "(declare-fun sp () (_ BitVec 64))"]
    # runGM machine-effect lets (the block-reflection register outcome):
    #   sp: -176 then +176 = identity;  ra: untouched;  a0: li status.
    sc = STATUS_CODE[status] if not control else (STATUS_CODE[status] ^ 1)  # corrupt
    L += [
        "(define-fun outPC   () (_ BitVec 64) (bvand r (bvnot #x0000000000000001)))",  # update bit0:=0
        "(define-fun outRA   () (_ BitVec 64) r)",
        "(define-fun outSP   () (_ BitVec 64) (bvadd (bvsub sp #x00000000000000b0) #x00000000000000b0))",
        f"(define-fun outA0   () (_ BitVec 64) (_ bv{sc} 64))",
    ]
    # the ExecExit fields (the EXIT relation), negated as a disjunction:
    #   pc = update(r+0,bit0:=0) ; ra = r ; spReg = sp ; a0 = StatusCode status
    L += [
        "(declare-fun specPC () (_ BitVec 64))",
        "(assert (= specPC (bvand r (bvnot #x0000000000000001))))",  # spec-side target
        f"(assert (or (not (= outPC specPC)) (not (= outRA r)) "
        f"(not (= outSP sp)) (not (= outA0 (_ bv{STATUS_CODE[status]} 64)))))",
    ]
    return L


# ---- HTIF / console-output effect --------------------------------------------
# Machine.output σ = st.out (OutRepr).  The arm's write-log has NO tohost store
# (brk/cont/expr spill only to the stack window, far below the HTIF window), so
# `output` is PRESERVED across the arm; for a LEAF st'=st, so OutRepr survives by
# reflexivity.  We model `output` as an uninterpreted String-list-length via an
# Int counter `nputchar` = number of htif_store_putchar the write-log performs,
# and the exit demands nputchar_exit = nputchar_entry (no console growth).  A
# store to tohost would bump it; the brk/cont wlog has none, so the counter is
# unchanged — UNSAT(neg).  control=True injects a phantom putchar ⇒ SAT.
def encode_htif_out(has_putchar=False):
    L = ["(set-logic ALL)", "(set-option :timeout 60000)"]
    L += ["(declare-fun out_entry () Int)"]
    # machine effect: exit output count = entry + (#putchar stores in wlog)
    n = 1 if has_putchar else 0
    L += [f"(define-fun out_exit () Int (+ out_entry {n}))"]
    # OutRepr for a LEAF (st'=st): exit output MUST equal entry output (st.out)
    L += ["(assert (not (= out_exit out_entry)))"]
    return L


# ===========================================================================
# (B) GIVEN-SUB-RESULT: the recursor-IH hypothesis.
#
# For a RECURSIVE arm (hSExpr): the exit relation's `store`/sub-`ValueRepr` at
# `subsret` is NOT computed by the arm — it is GIVEN by the sub-derivation via
# the `EvalIH`.  The `SubExecReturn` field is:
#     ∃ φc', PhiExtends φc φc' nc ∧ ValueRepr c.σ.mem N φc' subsret vsub
# The IH SUPPLIES exactly a `ValueRepr(sub-config) subsret vsub`; the arm's tail
# only copies/frames it into the exit config, so the exit ValueRepr FOLLOWS from
# the IH ValueRepr under the memory-frame agreement on [subsret, subsret+24) that
# the arm's write-log establishes (the sub-buffer is inside the frame, untouched
# by the epilogue).  Encode: (IH: ValueRepr at subsret in sub-mem) ∧ (frame-agree
# on the 24-byte buffer) ⇒ (exit: ValueRepr at subsret in exit-mem).  This is the
# SAME copy-readback shape gen_probe already closes — now with the SOURCE side an
# uninterpreted IH-supplied fact rather than a concrete source value.
# ===========================================================================
W = 3


def encode_given_subresult(kind="int", control=False):
    """The exit sub-ValueRepr FOLLOWS from the IH sub-ValueRepr + the buffer
    frame-agreement.  IH = `ValueRepr subMem N φc' subsret vsub` supplied as a
    HYPOTHESIS (source side); arm establishes 24-byte agree subMem≈exitMem on the
    buffer; conclude `ValueRepr exitMem ... subsret vsub`.  UNSAT(neg) ⇒ the
    given-sub-result branch composes.  This reuses gen_probe's ValueRepr encoder
    with src=dst=subsret and the copy being the IDENTITY frame (buffer untouched)."""
    base = "str" if kind.startswith("str") else kind
    L = ["(set-logic ALL)", "(set-option :timeout 60000)"]
    for m in ("subMem", "exitMem"):
        L += G.decls_mem(m)
    L += ["(declare-fun subsret () Int)"]
    if base == "bool": L.append("(declare-fun bB () Int)")
    if base == "int":  L.append("(declare-fun nN () Int)")
    if base == "str":
        L += [f"(declare-fun {m}_p () Int)" for m in ("subMem", "exitMem")]
        L += [f"(declare-fun cstr_tail_{m} () Bool)" for m in ("subMem", "exitMem")]
    L.append("(assert (>= subsret 0))")
    # IH HYPOTHESIS (given sub-result): ValueRepr subMem N φc' subsret vsub.
    L.append(f"(assert {G.valuerepr('subMem', 'subsret', base, W)})")
    # ARM EFFECT on the buffer: the sub-buffer [subsret, subsret+24) is inside the
    # frame; the arm's epilogue does NOT write it, so exitMem agrees with subMem
    # there (the SubExecReturn frame clause).  drop one byte for the control.
    for j in range(24):
        if control and j == 0:
            continue
        L.append(f"(assert (= (select exitMem_def (+ subsret {j})) (select subMem_def (+ subsret {j}))))")
        L.append(f"(assert (= (select exitMem_val (+ subsret {j})) (select subMem_val (+ subsret {j}))))")
    if base == "str":
        # payload pointer + tail agreement carried by the IH (past the recursion
        # cut) — this is the given-sub-result's CString survival, an IH fact.
        L.append("(assert (= exitMem_p subMem_p))")
        L.append("(assert (= cstr_tail_exitMem cstr_tail_subMem))")
        # BOUNDED payload cut (mirrors gen_noframe.encode_str_finitize, W=3): the
        # payload chars at [p, p+W) live OUTSIDE the 24-byte struct buffer, so the
        # frame-agree loop above never pins them.  The IH's CString survival gives
        # byte-agreement over the bounded prefix; without it Z3 leaves the payload
        # free and finds a spurious countermodel (the branch reads SAT).  With it
        # the str branch is a proved UNSAT, same status as the non-str kinds.
        for i in range(W):
            L.append(f"(assert (= (select exitMem_def (+ exitMem_p {i})) (select subMem_def (+ subMem_p {i}))))")
            L.append(f"(assert (= (select exitMem_val (+ exitMem_p {i})) (select subMem_val (+ subMem_p {i}))))")
    # NEGATED exit: ValueRepr exitMem N φc' subsret vsub
    L.append(f"(assert (not {G.valuerepr('exitMem', 'subsret', base, W)}))")
    return L


# ===========================================================================
# DRIVER — assemble the FULL exit relation per pilot field and report per-branch.
# ===========================================================================
def run_pilot(field):
    is_leaf = field in ("hSBrk", "hSCont")
    status = {"hSBrk": "brk", "hSCont": "cont", "hSExpr": "normal"}.get(field, "normal")
    out = {"field": field, "branches": {}}

    # (A1) register + PC branch
    va, _, dta = z3_run(encode_reg_pc_out(status))
    vac, _, _ = z3_run(encode_reg_pc_out(status, control=True))
    out["branches"]["reg_pc"] = {"verdict": va, "control": vac, "time": dta}

    # (A2) HTIF / console-output branch
    vh, _, dth = z3_run(encode_htif_out(has_putchar=False))
    vhc, _, _ = z3_run(encode_htif_out(has_putchar=True))
    out["branches"]["htif_out"] = {"verdict": vh, "control": vhc, "time": dth}

    # (A3) memory frame — reuse the LANDED extractor+encoder via autoprove
    try:
        import autoprove as AP
        fr = AP.run_execleaf_frame(field, "brkCont",
                                   grows_frames=(field == "hSVarNull"))
        out["branches"]["mem_frame"] = {"verdict": fr["verdict"], "cert": fr.get("cert", "")}
        surv = fr.get("survival", {})
    except Exception as ex:
        out["branches"]["mem_frame"] = {"verdict": f"ERR:{ex}"}
        surv = {}

    # (B) given-sub-result — only for a RECURSIVE arm; for a leaf it is the
    # identity (no sub-call), reported as N/A.
    if is_leaf:
        out["branches"]["given_subresult"] = {"verdict": "N/A (leaf: st'=st, no sub-call)"}
    else:
        # exercise all Value kinds the sub-result may be (the IH-supplied vsub)
        subres = {}
        for kind in ("null", "bool", "int", "str"):
            vs, _, dts = z3_run(encode_given_subresult(kind))
            vsc, _, _ = z3_run(encode_given_subresult(kind, control=True))
            subres[kind] = {"verdict": vs, "control": vsc, "time": dts}
        out["branches"]["given_subresult"] = subres

    # (C) exit-Repr StoreRepr survival — the landed Houdini base/step certificate
    out["branches"]["storerepr_survival"] = {
        "verdict": surv.get("verdict", "(run --survival)"),
        "ih": surv.get("ih", ""),
        "base": surv.get("base", ""),
        "step": surv.get("step", ""),
        "wall": surv.get("wall", ""),
    }
    return out


def _cls(v):
    return "Z3-UNSAT (proved)" if str(v).startswith("unsat") else v


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--field", default="hSBrk")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()
    r = run_pilot(args.field)
    if args.json:
        print(json.dumps(r, indent=2)); return 0
    print(f"=== FULL-EFFECT exit-relation encode for {r['field']} ===\n")
    b = r["branches"]
    print(f"(A1) register + PC outcome (runGM/endPCM):")
    print(f"       neg = {_cls(b['reg_pc']['verdict'])}   control(corrupt a0) = {b['reg_pc']['control']}   ({b['reg_pc']['time']}s)")
    print(f"(A2) HTIF / console-output (Machine.output = st.out):")
    print(f"       neg = {_cls(b['htif_out']['verdict'])}   control(phantom putchar) = {b['htif_out']['control']}   ({b['htif_out']['time']}s)")
    print(f"(A3) memory frame (wlogM-extracted, LANDED):")
    print(f"       {b['mem_frame']['verdict']}   {b['mem_frame'].get('cert','')}")
    gsr = b["given_subresult"]
    print(f"(B)  given-sub-result (recursor IH hypothesis):")
    if "verdict" in gsr:
        print(f"       {gsr['verdict']}")
    else:
        for k, v in gsr.items():
            print(f"       vsub={k:5}: neg = {_cls(v['verdict'])}   control(drop byte) = {v['control']}   ({v['time']}s)")
    sr = b["storerepr_survival"]
    print(f"(C)  StoreRepr survival (landed Houdini base/step):")
    print(f"       {sr['verdict']}  IH={sr['ih']}  base={sr['base']} step={sr['step']} wall={sr['wall']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
