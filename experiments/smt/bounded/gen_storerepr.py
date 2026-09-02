#!/usr/bin/env python3
"""
Bounded-SMT encoder for the *StoreRepr survival* obligation, structurally
mirroring gen_probe.py's ValueRepr-copy encoder but for the RECURSIVE Repr cone
`StoreRepr → FrameRepr → {ValueRepr, CString, φf-parent} → …`.

GROUND TRUTH (Vsa/Sim/ReprSurvival.lean):
  storeRepr_agreeP : AgreeP P m m' → (per-object footprint P covers header/slots/
    strings/parent) → StoreRepr m … s → StoreRepr m' … s
  factored as frames-field ∘ frameRepr_agreeP ∘ {valueRepr_agreeP, cstring_agreeP}
  with φf_inj/φc_inj/arena transferred VERBATIM (memory-independent).

The obligation this file encodes (the brk/cont exec-leaf StoreRepr survival, an
arm that KEEPS the frame — no Store.define): given the arm's write-log confined
to the stack window [SL.lo, sp), and StoreRepr in the source memory m, prove
StoreRepr in the destination m'.  The arena/AST/string footprints are DISJOINT
from the stack window (frames_arena / closures_arena put every object in the
arena; strings live outside the C stack).  So the "true" survival fact is
AgreeP over the complement of [SL.lo, sp), which covers every Repr byte.

DEPTH AXIS (mirrors gen_probe's k, but now over the StoreRepr cone):
  L0 : FLAT header only — the 32-byte Env header [e,e+32) of ONE frame.
       (analogue of ValueRepr null/bool/int: finite, non-recursive.)
  L1 : L0 + the per-binding VALUE slots (ValueRepr, 24-byte header) — still
       finite for null/int values; but a .str value drags in CString (recursion).
  L2 : L1 + the NAME strings (CString) + the value inner strings (CString) —
       the CString recursion, the SAME wall as the .str pilot.
  L3 : L2 + the PARENT-frame link φf pa — the StoreRepr-INTERNAL recursion into
       ANOTHER frame (the nested-frame wall unique to StoreRepr, absent in the
       flat ValueRepr copy pilot).

We keep ONE frame in the bounded store (nb=1 binding) and encode agreement as
the write-log window model (writelog_smt.py): m' = writeLog m log, log confined
to [SL.lo, sp); every Repr byte address is asserted OUTSIDE that window (the
disjointness the arena/AST layout supplies).  Reads (read32/read64) reuse
gen_probe's byte-unfold.
"""
import sys, os, subprocess, time
Z3 = "z3"
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import gen_probe as G  # decls_mem, byte_defined/val

# ---------------------------------------------------------------------------
# READ MODEL (survival-oriented, LINEAR).
#
# gen_probe.py reconstructs read32/read64 as Σ byte·256^j (Int), which is
# NONLINEAR and makes Z3 diverge once several pointer reads are chained (as the
# StoreRepr cone does).  For a *survival* obligation we never need the numeric
# value of a read — only that (a) the window is defined and (b) the read RESULT
# is preserved iff its bytes agree.  So we model each width-w read at addr `a`
# with an UNINTERPRETED function `rd_w(mem_val_array, a)` returning Int, plus:
#   * definedness = all w bytes' `def` flags true;
#   * a byte-agreement → read-equality axiom is NOT needed as a global axiom;
#     instead, whenever the caller supplies AgreeP on [a,a+w) we can conclude
#     rd_w m a = rd_w m' a via a functional-congruence lemma the encoder emits
#     on demand (`read_eq_of_window`).  This keeps everything in QF/linear +
#     UF, which Z3 decides instantly.
# ---------------------------------------------------------------------------
def rd(width, m, a):
    """uninterpreted read of `width` bytes at `a` from memory `m` (its val array)."""
    return f"(rd{width} {m}_val {a})"

def rd_defined(width, m, a):
    return "(and " + " ".join(G.byte_defined(m, f"(+ {a} {j})") for j in range(width)) + ")"

def read_eq_of_window(width, a):
    """emit the assertion: (∀j<w, m_val[a+j]=mp_val[a+j]) → rd_w m a = rd_w mp a.
    This is the functional-congruence consequence of AgreeP on the window; it is
    the SMT image of readLE_agreeP.  Returned as an implication term."""
    ante = "(and " + " ".join(
        f"(= (select m_val (+ {a} {j})) (select mp_val (+ {a} {j})))" for j in range(width)) + ")"
    return f"(=> {ante} (= {rd(width,'m',a)} {rd(width,'mp',a)}))"

# ---------------------------------------------------------------------------
# window model: m' agrees with m OUTSIDE [sllo, sp).  We assert the Repr byte
# addresses are outside the window (arena/AST disjointness), and the survival
# fact "m'[a]?=m[a]? for a outside window" is the AgreeP the arm supplies.
# For the UN-STRENGTHENED goal we supply agreement ONLY on the bytes the flat
# header reads; the IH must add the deeper windows.
# ---------------------------------------------------------------------------

def decls():
    L = ["(set-logic ALL)", "(set-option :timeout 60000)"]
    # uninterpreted reads (linear + UF): rd4/rd8 : (Array Int BV8) × Int → Int
    L += ["(declare-fun rd4 ((Array Int (_ BitVec 8)) Int) Int)",
          "(declare-fun rd8 ((Array Int (_ BitVec 8)) Int) Int)"]
    for m in ("m", "mp"):
        L += G.decls_mem(m)
    # one frame at env addr e; name-ptr array pn, value array pv; parent frame ep
    L += ["(declare-fun e () Int)", "(declare-fun pn () Int)",
          "(declare-fun pv () Int)", "(declare-fun ep () Int)"]
    # string pointers: name string qn, value inner string vs
    L += ["(declare-fun qn () Int)", "(declare-fun vs () Int)"]
    # tag/value payload symbols, and the OPAQUE recursive tails (the cuts)
    L += ["(declare-fun nN () Int)"]
    for m in ("m", "mp"):
        L += [f"(declare-fun cstr_name_{m} () Bool)",   # name-string tail cut
              f"(declare-fun cstr_val_{m} () Bool)",    # value inner-string tail cut
              f"(declare-fun frame_par_{m} () Bool)"]   # parent-frame Repr cut
    # window
    L += ["(declare-fun sllo () Int)", "(declare-fun sp () Int)"]
    # ---- readLE_agreeP congruence axioms (background truths, one per read site).
    # These are the SMT image of ReprSurvival.readLE_agreeP: byte-window agreement
    # ⇒ read equality.  Emitted per concrete read site so no quantifier is needed.
    READ_SITES = [
        (4, "e"), (8, "(+ e 8)"), (8, "(+ e 16)"), (8, "(+ e 24)"),   # env header + parent slot
        (4, "pv"), (8, "(+ pv 8)"),                                    # value slot header+ptr
        (8, "pn"),                                                     # name-ptr slot
    ]
    for w, a in READ_SITES:
        L.append(f"(assert {read_eq_of_window(w, a)})")
    return L

def outside(addr, width):
    """assert [addr, addr+width) is disjoint from the stack window [sllo, sp)."""
    return f"(or (>= {addr} sp) (<= (+ {addr} {width}) sllo))"

W = 3  # bounded CString payload window (matches gen_probe W)

# --- FrameRepr, bounded, definition-encoded to depth L ----------------------
# value kind fixed to .str at L>=2 so the CString recursion is exercised (the
# hard case); at L<=1 use .int (finite) so L0/L1 are non-recursive like null.

def frame_header(m):
    # read32 e = 1  (vars.length = 1) ; read64(e+8)=pn ; read64(e+16)=pv.
    return f"(and (= {rd(4,m,'e')} 1) {rd_defined(4,m,'e')} " \
           f"{rd_defined(8,m,'(+ e 8)')} (= {rd(8,m,'(+ e 8)')} pn) " \
           f"{rd_defined(8,m,'(+ e 16)')} (= {rd(8,m,'(+ e 16)')} pv))"

def value_slot(m, L):
    a = "pv"  # binding 0 value slot at pv + 24*0
    if L <= 1:
        # .int : read32 a = 2 ∧ readI64(a+8)=n  (finite, no recursion)
        return f"(and (= {rd(4,m,a)} 2) {rd_defined(4,m,a)} " \
               f"{rd_defined(8,m,'(+ pv 8)')} (= {rd(8,m,'(+ pv 8)')} nN))"
    # .str : read32 a = 3 ∧ read64(a+8)=vs ∧ CString m vs (bounded + opaque tail)
    tag = f"(and (= {rd(4,m,a)} 3) {rd_defined(4,m,a)})"
    ptr = f"(and {rd_defined(8,m,'(+ pv 8)')} (= {rd(8,m,'(+ pv 8)')} vs) (not (= vs 0)))"
    cs = [f"(select {m}_def (+ vs {i}))" for i in range(W)] + [f"cstr_val_{m}"]
    return f"(and {tag} {ptr} (and {' '.join(cs)}))"

def name_binding(m, L):
    # read64 (pn + 0) = qn ∧ CString m qn (name)   [L>=2]
    slot = f"(and {rd_defined(8,m,'pn')} (= {rd(8,m,'pn')} qn))"
    cs = [f"(select {m}_def (+ qn {i}))" for i in range(W)] + [f"cstr_name_{m}"]
    return f"(and {slot} (and {' '.join(cs)}))"

def parent_link(m, L):
    # read64 (e+24) = φf pa ≠ 0 ∧ FrameRepr(parent)   [L>=3]
    slot = f"(and {rd_defined(8,m,'(+ e 24)')} (= {rd(8,m,'(+ e 24)')} ep) (not (= ep 0)))"
    return f"(and {slot} frame_par_{m})"  # parent frame Repr = opaque cut

def framerepr(m, L):
    parts = [frame_header(m), value_slot(m, L)]
    if L >= 2:
        parts.append(name_binding(m, L))
    if L >= 3:
        parts.append(parent_link(m, L))
    return "(and " + " ".join(parts) + ")"

# --- the un-strengthened copy hypothesis C: only the 32-byte env header is
#     known to agree (the flat frame-vector survival the writelog frame slice
#     gives).  Deeper windows are the IH.
def header_agree():
    conj = []
    for j in range(32):
        conj.append(f"(= (select mp_def (+ e {j})) (select m_def (+ e {j})))")
        conj.append(f"(= (select mp_val (+ e {j})) (select m_val (+ e {j})))")
    return "(and " + " ".join(conj) + ")"

# ---------------------------------------------------------------------------
# CANDIDATE VOCABULARY for Houdini — mined from the survival-lemma zoo:
#   valueRepr_agreeP  → value-slot header window  [pv, pv+24)
#   cstring_agreeP    → name/value string byte windows [qn,qn+W], [vs,vs+W] + tails
#   frameRepr_agreeP  → name-pointer slot [pn, pn+8)
#   storeRepr_agreeP  → parent-frame link [e+24,e+32) + parent Repr cut
#   φf_inj/arena      → memory-independent (VERBATIM) — noise here
# ---------------------------------------------------------------------------
def region_agree(name, base, width):
    conj = [f"(= (select mp_def (+ {base} {j})) (select m_def (+ {base} {j})))"
            for j in range(width)]
    conj += [f"(= (select mp_val (+ {base} {j})) (select m_val (+ {base} {j})))"
             for j in range(width)]
    return (name, "(and " + " ".join(conj) + ")")

def cand_valhdr():   return region_agree("valueRepr_agreeP@valhdr[pv,pv+24)", "pv", 24)
def cand_nameptr():  return region_agree("frameRepr_agreeP@nameptr[pn,pn+8)", "pn", 8)
def cand_parlink():  return region_agree("storeRepr_agreeP@parent[e+24,e+32)", "(+ e 24)", 8)
def cand_namestr(i): return region_agree(f"cstring_agreeP@name[{i}]", f"(+ qn {i})", 1)
def cand_valstr(i):  return region_agree(f"cstring_agreeP@valstr[{i}]", f"(+ vs {i})", 1)
def cand_ptr_pv():   return ("valueRepr_agreeP@ptr(vs)", "(and true true)")  # implied
def cand_name_tail():return ("cstring_agreeP@name-tail", "(= cstr_name_mp cstr_name_m)")
def cand_val_tail(): return ("cstring_agreeP@valstr-tail", "(= cstr_val_mp cstr_val_m)")
def cand_par_cut():  return ("storeRepr_agreeP@parent-frame(IH)", "(= frame_par_mp frame_par_m)")
# noise / verbatim-transfer candidates (should be DROPPED):
def cand_finj():     return ("noise@φf_inj(memory-indep)", "(and true true)")
def cand_arena():    return ("noise@arena-bound(memory-indep)", "(>= e 0)")
def cand_force_parT():return ("noise@force-dst-parent-true", "frame_par_mp")
def cand_force_nameT():return ("noise@force-dst-name-true", "cstr_name_mp")

def candidates(L):
    C = [cand_valhdr()]
    if L >= 2:
        C += [cand_nameptr()]
        for i in range(W): C.append(cand_namestr(i))
        for i in range(W): C.append(cand_valstr(i))
        C += [cand_name_tail(), cand_val_tail()]
    if L >= 3:
        C += [cand_parlink(), cand_par_cut()]
    # noise across all L:
    C += [cand_finj(), cand_arena(), cand_force_nameT()]
    if L >= 3: C.append(cand_force_parT())
    return C

# ---------------------------------------------------------------------------
def base_asserts(L, control_drop=False):
    H    = framerepr("m", L)
    C    = header_agree() if not control_drop else header_agree_drop()
    Cncl = framerepr("mp", L)
    A = ["(assert (>= e 0)) (assert (>= pv 0)) (assert (>= pn 0))",
         "(assert (>= vs 0)) (assert (>= qn 0)) (assert (>= ep 0))",
         f"(assert {H})", f"(assert {C})", f"(assert (not {Cncl}))"]
    return A

def header_agree_drop():
    # control: drop env header byte 0 → deliberately false even at L0
    conj = []
    for j in range(1, 32):
        conj.append(f"(= (select mp_def (+ e {j})) (select m_def (+ e {j})))")
        conj.append(f"(= (select mp_val (+ e {j})) (select m_val (+ e {j})))")
    return "(and " + " ".join(conj) + ")"

def z3(script, model=False):
    body = "\n".join(script) + "\n(check-sat)\n" + ("(get-model)\n" if model else "")
    t = time.time()
    p = subprocess.run([Z3, "-in"], input=body, capture_output=True, text=True, timeout=90)
    return (p.stdout.strip().split("\n", 1)[0] if p.stdout.strip() else "(no output)",
            time.time() - t, p.stdout)

def goal_unsat(L, cands):
    s = decls() + base_asserts(L) + [f"(assert {e})" for _, e in cands]
    v, dt, _ = z3(s); return v, dt

def cand_consistent(L, cand):
    # positive model H ∧ C ∧ Cncl ∧ cand must be SAT (else it contradicts / is vacuous)
    H = framerepr("m", L); C = header_agree(); Cncl = framerepr("mp", L)
    s = decls() + ["(assert (>= e 0))(assert (>= pv 0))(assert (>= pn 0))",
                   "(assert (>= vs 0))(assert (>= qn 0))(assert (>= ep 0))",
                   f"(assert {H})", f"(assert {C})", f"(assert {Cncl})", f"(assert {cand[1]})"]
    v, dt, _ = z3(s); return v, dt

def houdini(L):
    cands = candidates(L)
    log = []
    v0, dt0 = goal_unsat(L, cands)
    log.append(("full-set", [c[0] for c in cands], v0, dt0))
    if not v0.startswith("unsat"):
        return [], log, v0
    survivors = []
    for c in cands:
        vc, dtc = cand_consistent(L, c)
        if vc.startswith("sat"):
            survivors.append(c)
        log.append(("consistency", c[0], vc, dtc))
    def rank(c):
        n = c[0]
        if n.startswith("noise@"): return 0
        return 2
    changed = True
    while changed:
        changed = False
        for c in sorted(survivors, key=rank):
            trial = [x for x in survivors if x is not c]
            vt, dtt = goal_unsat(L, trial)
            log.append(("drop-test", c[0], vt, dtt))
            if vt.startswith("unsat"):
                survivors = trial; changed = True; break
    vf, dtf = goal_unsat(L, survivors)
    log.append(("final", [c[0] for c in survivors], vf, dtf))
    return survivors, log, vf

def positive_model_sat(L):
    """H ∧ C ∧ Cncl SAT?  (non-vacuity: the un-strengthened SAT is a real gap,
    not a contradiction in H∧C)."""
    H = framerepr("m", L); C = header_agree(); Cncl = framerepr("mp", L)
    s = decls() + ["(assert (>= e 0))(assert (>= pv 0))(assert (>= pn 0))",
                   "(assert (>= vs 0))(assert (>= qn 0))(assert (>= ep 0))",
                   f"(assert {H})", f"(assert {C})", f"(assert {Cncl})"]
    return z3(s)[0]

# ===========================================================================
# BASE / STEP DECOMPOSITION of the structural induction on the `frames` vector
# (blockmem-rewrite-plan.md §"the recursive-Repr residual", steps 2-4).
#
# storeRepr_agreeP recurses on the parent-frame chain (φf pa).  The Lean proof
# is `induction on s.frames.size with | nil => <base> | cons => <step using ih>`.
# We Z3-DISCHARGE the two schema obligations SEPARATELY, each non-recursive/QF
# once the IH is a hypothesis:
#
#   BASE  P(nil):   empty parent chain (ep = 0, no parent frame) ⇒ the frame's
#                   own byte-windows (header + value slot + name/value strings)
#                   suffice; there is no parent recursion to close.  UNSAT.
#   STEP  (∀parent,P) → P(node):  the parent-frame survival IH is a HYPOTHESIS
#                   (the `frame_par` equality cut = `P(parent)`); under it the
#                   current node's FrameRepr survives from the byte-windows +
#                   the parent-link window.  UNSAT.  This is the L3 WALL-probe
#                   with the IH supplied — the exact point structural induction
#                   discharges by the IH.
#
# The survivors of houdini(3) are the selected+SMT-validated IH; base+step both
# UNSAT under it is the Z3-SUFFICIENCY CERTIFICATE the plan asks for (NOT a Lean
# proof — a certified IH that base and step both close).
# ===========================================================================
def _nonrec_windows():
    """the frame's own (non-parent) byte-window agreements — valhdr, nameptr,
    name/val strings + string tails.  These are P's per-node footprint."""
    C = [cand_valhdr(), cand_nameptr()]
    for i in range(W): C.append(cand_namestr(i))
    for i in range(W): C.append(cand_valstr(i))
    C += [cand_name_tail(), cand_val_tail()]
    return C

def base_case():
    """P(nil): no parent frame (ep=0 ⇒ parent_link's `ep≠0` is unreachable).
    We assert L2 framerepr (header+value+name, no parent axis) and the node
    windows; the goal (framerepr mp at L2) must be UNSAT-forced.  UNSAT ⇒ base
    closes."""
    s = decls() + base_asserts(2) + [f"(assert {e})" for _, e in _nonrec_windows()]
    v, dt, _ = z3(s)
    return v, dt

def step_case():
    """(∀parent,P(parent)) → P(node): L3 framerepr WITH the parent-frame IH cut
    (`storeRepr_agreeP@parent-frame(IH)`) supplied as a hypothesis, plus the
    node's own windows + the parent-link window.  UNSAT ⇒ step closes under IH.
    Mirrors the WALL probe's `with_ih` = UNSAT."""
    cands = _nonrec_windows() + [cand_parlink(), cand_par_cut()]
    s = decls() + base_asserts(3) + [f"(assert {e})" for _, e in cands]
    v, dt, _ = z3(s)
    return v, dt

def step_wall():
    """CONTROL for the step: WITHHOLD the parent IH cut → must stay SAT (the
    recursion is genuinely open without the IH; the step is non-vacuous)."""
    cands = _nonrec_windows() + [cand_parlink()]
    s = decls() + base_asserts(3) + [f"(assert {e})" for _, e in cands]
    v, dt, _ = z3(s)
    return v, dt

def storerepr_survival_certificate(verbose=False):
    """PROGRAMMATIC entry (imported by scripts/autoprove.py's recursive branch).
    Selects the survival IH by Houdini at L3, then base/step-DECOMPOSES the
    structural induction and Z3-validates each half.

    Returns a dict:
      { ih_name, survivors, unstrengthened, positive_model,
        base_unsat, step_unsat, wall_sat,   # the base/step certificate
        certified }                          # base ∧ step both UNSAT ∧ wall SAT
    The IH is `storeRepr_agreeP@parent-frame(IH)` + the frame-window survivors.
    """
    v_uns, _, _ = z3(decls() + base_asserts(3), model=False)
    pos = positive_model_sat(3)
    survivors, hlog, vf = houdini(3)
    vb, dtb = base_case()
    vs, dts = step_case()
    vw, _ = step_wall()
    ih = [c[0] for c in survivors if "parent-frame(IH)" in c[0]]
    certified = (vb.startswith("unsat") and vs.startswith("unsat")
                 and vw.startswith("sat") and vf.startswith("unsat"))
    r = {
        "ih_name": ih[0] if ih else "(none)",
        "survivors": [c[0] for c in survivors],
        "unstrengthened": v_uns,
        "positive_model": pos,
        "houdini_closes": vf,
        "base_unsat": vb,
        "step_unsat": vs,
        "wall_sat": vw,
        "base_time": round(dtb, 3),
        "step_time": round(dts, 3),
        "certified": certified,
    }
    if verbose:
        print("=== StoreRepr survival: Houdini IH + base/step certificate ===")
        print(f"  unstrengthened(L3)      = {v_uns}  (SAT ⇒ IH load-bearing)")
        print(f"  positive-model          = {pos}  (SAT ⇒ non-vacuous)")
        print(f"  Houdini survivors       = {r['survivors']}")
        print(f"  selected IH             = {r['ih_name']}")
        print(f"  BASE  P(nil)            = {vb}  ({r['base_time']}s)  [UNSAT ⇒ base closes]")
        print(f"  STEP  (∀p,P)→P(node)    = {vs}  ({r['step_time']}s)  [UNSAT ⇒ step closes under IH]")
        print(f"  STEP wall (no IH)       = {vw}  [SAT ⇒ IH load-bearing in step]")
        print(f"  CERTIFIED (base∧step)   = {certified}")
    return r

def main():
    print("=== StoreRepr-survival bounded probe: un-strengthened goal per depth ===")
    for L in (0, 1, 2, 3):
        v, dt, _ = z3(decls() + base_asserts(L), model=False)
        vctrl, dtc, _ = z3(decls() + base_asserts(L, control_drop=True), model=False)
        vpos = positive_model_sat(L)
        print(f"  L{L}: unstrengthened={v:6} ({dt:.2f}s)  positive-model={vpos:4}"
              f"  ctrl-drop-hdr-byte0={vctrl:6} ({dtc:.2f}s)")
    # WALL probe: at L3, supply EVERY byte-agreement window (all non-cut cands)
    # but WITHHOLD the parent-frame IH cut → must stay SAT (the nested-frame
    # recursion cannot be closed by windows; it needs the survival IH itself).
    all_windows = [c for c in candidates(3)
                   if not c[0].startswith("noise@")
                   and "parent-frame(IH)" not in c[0]]
    vwall, _ = goal_unsat(3, all_windows)
    with_ih = all_windows + [cand_par_cut()]
    vih, _ = goal_unsat(3, with_ih)
    print(f"\n=== Nested-frame WALL probe (L3) ===")
    print(f"  all byte-windows, NO parent-frame IH : {vwall}  (SAT = wall: recursion open)")
    print(f"  + parent-frame IH cut (survival)     : {vih}  (UNSAT = IH closes it)")

    print("\n=== Houdini per depth ===")
    for L in (0, 1, 2, 3):
        survivors, log, vf = houdini(L)
        print(f"\n--- L{L} ---")
        for kind, a, v, dt in log:
            print(f"  [{kind:12}] {str(a):48.48} -> {v:8} {dt:5.2f}s")
        print(f"  survivors: {[c[0] for c in survivors]}")
        print(f"  goal closes under survivors: {vf}")

    print()
    storerepr_survival_certificate(verbose=True)

if __name__ == "__main__":
    main()
