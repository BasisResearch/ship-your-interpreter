#!/usr/bin/env python3
"""
IN-HOUSE HOUDINI IH-synthesis probe (Z3 as the ONLY solver — pure oracle, no
Spacer / no CHC engine).

ORIGINAL QUESTION (the `.str` pilot, still the default run): can a blind Houdini
loop rediscover a Z3-confirmed sufficient IH for the `.str` ValueRepr-copy
readback obligation, WITHOUT being handed `cstring_agreeP`?  (Answer: yes — see
experiments/smt/HOUDINI-IH.md.)

GENERALISED (this file): a `--field <SkelName>` / `--batch <list|all-supplier>`
driver that, per field, runs the bounded-VC + Houdini pipeline and emits ONE of
four honest verdicts:

  ENCODE-GAP     — the field's statement is machine-step / Repr-shape content the
                   bounded QF-ABV encoder cannot express (∀-closed Triple/SegEntry
                   /ExecEntry/*Geom/NativeSpec bundles).  Reported HONESTLY; this
                   is EXPECTED for the whole NO-CURE-SEMANTIC-GAP supplier class —
                   bounded-SMT does not reach machine-step semantics.
  PROVABLE-DIRECT— negation is Z3-UNSAT with NO IH (non-recursive stratum leaf;
                   the corresponding Lean leaf lemma is noted).
  IH-FOUND       — negation SAT; Houdini finds a maximal inductive candidate
                   subset that Z3 confirms closes the goal (survivors listed).
  IH-NOT-FOUND   — negation SAT; no candidate subset closes it (vocabulary
                   insufficient; the missing predicate shape is named).

The bounded encoder is `experiments/smt/bounded/gen_probe.py` (imported as G).
The `.str` pilot's candidate/Houdini machinery is unchanged and reused.
"""
import subprocess, time, os, sys, argparse

Z3 = "z3"
BOUNDED = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                       "..", "experiments", "smt", "bounded")
sys.path.insert(0, os.path.abspath(BOUNDED))
import gen_probe as G   # reuse read/copy/valuerepr encoders

W = 3   # bounded payload window depth (matches cdepth k=3 char prefix)

# ===========================================================================
# PART A — the ENCODER for a field's bounded VC.
#
# Two encodable strata only (everything else is an honest ENCODE-GAP):
#   * "valuerepr-copy" : the ValueRepr copy-readback obligation, per Value kind.
#     Non-recursive kinds (null/bool/int) are PROVABLE-DIRECT; str needs the IH.
#   * (no other supplier field is expressible — see FIELD_REGISTRY.)
# ===========================================================================

def base_decls():
    L = ["(set-logic ALL)", "(set-option :timeout 60000)"]
    for m in ("m", "mp"):
        L += G.decls_mem(m)
    L += ["(declare-fun srcAddr () Int)", "(declare-fun dstAddr () Int)"]
    L += ["(declare-fun bB () Int)", "(declare-fun nN () Int)"]
    L += [f"(declare-fun {m}_p () Int)" for m in ("m", "mp")]
    L += [f"(declare-fun cstr_tail_{m} () Bool)" for m in ("m", "mp")]
    return L

def base_asserts(kind, control=False):
    """H (src repr) ∧ C (24-byte struct copy) ∧ ¬Cncl (dst repr) for a Value kind."""
    H    = G.valuerepr("m",  "srcAddr", kind, W)
    C    = G.copy24("m", "mp", drop=(0 if control else None))
    Cncl = G.valuerepr("mp", "dstAddr", kind, W)
    return ["(assert (>= srcAddr 0))", "(assert (>= dstAddr 0))",
            f"(assert {H})", f"(assert {C})", f"(assert (not {Cncl}))"]

# ---------------------------------------------------------------------------
# CANDIDATE VOCABULARY (str only; the recursive kind).  key -> (origin, smt).
# ---------------------------------------------------------------------------
def cand_payload_byte(i):
    return (f"cstr_agreeP@payload[{i}]",
            f"(and (= (select mp_def (+ mp_p {i})) (select m_def (+ m_p {i}))) "
            f"(= (select mp_val (+ mp_p {i})) (select m_val (+ m_p {i}))))")
def cand_ptr_eq():   return ("read64_copy@ptr(mp_p=m_p)", "(= mp_p m_p)")
def cand_tail_eq():  return ("cstr_agreeP@tail", "(= cstr_tail_mp cstr_tail_m)")
def cand_tag_agree():
    return ("read32_copy@tag(implied-by-C)",
            "(= (select mp_val (+ dstAddr 0)) (select m_val (+ srcAddr 0)))")
def cand_src_tail(): return ("noise@force-src-tail-true", "cstr_tail_m")
def cand_dst_tail(): return ("noise@force-dst-tail-true", "cstr_tail_mp")
def cand_ptr_pos():  return ("weak@ptr>=0", "(and (>= m_p 0) (>= mp_p 0))")
def cand_addr_disj():
    return ("noise@addr-disjoint",
            "(or (>= srcAddr (+ dstAddr 24)) (>= dstAddr (+ srcAddr 24)))")

def all_candidates():
    C = [cand_ptr_eq(), cand_tail_eq()]
    for i in range(W):
        C.append(cand_payload_byte(i))
    C += [cand_tag_agree(), cand_src_tail(), cand_dst_tail(),
          cand_ptr_pos(), cand_addr_disj()]
    return C

def z3_run(script, get_model=True):
    body = "\n".join(script) + "\n(check-sat)\n" + ("(get-model)\n" if get_model else "")
    t = time.time()
    p = subprocess.run([Z3, "-in"], input=body, capture_output=True, text=True, timeout=90)
    dt = time.time() - t
    out = p.stdout.strip()
    verdict = out.split("\n", 1)[0] if out else "(no output)"
    return verdict, out, dt

def goal_unsat_under(kind, cands):
    script = base_decls() + base_asserts(kind, control=False)
    for _, expr in cands:
        script.append(f"(assert {expr})")
    v, _, dt = z3_run(script, get_model=False)
    return v, dt

def cand_consistent_with_positive(kind, cand):
    H    = G.valuerepr("m",  "srcAddr", kind, W)
    C    = G.copy24("m", "mp", drop=None)
    Cncl = G.valuerepr("mp", "dstAddr", kind, W)
    script = base_decls() + ["(assert (>= srcAddr 0))", "(assert (>= dstAddr 0))",
                             f"(assert {H})", f"(assert {C})", f"(assert {Cncl})",
                             f"(assert {cand[1]})"]
    v, _, dt = z3_run(script, get_model=False)
    return v, dt

def houdini(kind):
    """Houdini for the recursive `str` kind: maximal-consistent minimal-sufficient
    candidate subset.  Returns (survivors, log, final-verdict)."""
    cands = all_candidates()
    log = []
    v0, dt0 = goal_unsat_under(kind, cands)
    log.append(("full-set", [c[0] for c in cands], v0, dt0))
    if not v0.startswith("unsat"):
        log.append(("ABORT", "full candidate set does NOT close goal", v0, dt0))
        return [], log, v0
    survivors = []
    for c in cands:
        vc, dtc = cand_consistent_with_positive(kind, c)
        keep = vc.startswith("sat")
        log.append(("consistency", c[0], vc, dtc))
        if keep:
            survivors.append(c)
    def drop_rank(c):
        n = c[0]
        if n.startswith("noise@") or n.startswith("weak@"): return 0
        if n.startswith("read32_copy@tag"):                 return 1
        return 2
    changed = True
    while changed:
        changed = False
        for c in sorted(survivors, key=drop_rank):
            trial = [x for x in survivors if x is not c]
            vt, dtt = goal_unsat_under(kind, trial)
            log.append(("drop-test", c[0], vt, dtt))
            if vt.startswith("unsat"):
                survivors = trial
                changed = True
                break
    vf, dtf = goal_unsat_under(kind, survivors)
    log.append(("final", [c[0] for c in survivors], vf, dtf))
    return survivors, log, vf

# ===========================================================================
# PART B — the FIELD REGISTRY.
#
# Each supplier field's *statement* was read from the tree (Vsa/Sim/rows/*.lean,
# EntrySeams.lean).  Classification of what the bounded encoder can reach:
#
#   "valuerepr-copy:<kind>"  — encodable: run the copy-readback VC for <kind>.
#   "encode-gap:<why>"       — NOT encodable: the residual is a ∀-closed bundle
#                              over machine-step predicates (Triple/SegEntry/
#                              SegExit/ExecEntry/*Geom/NativeSpec/Steps).  These
#                              are the honest wall for bounded-SMT.
#
# The `encoding` string names the DOMINATING predicate of the residual's Prop, so
# the ENCODE-GAP verdict cites the exact reason.
# ===========================================================================
FIELD_REGISTRY = {
    # --- the leaf ValueRepr copy-readback family (PROVABLE-DIRECT / IH-FOUND) ---
    "ValueRepr.null":  ("valuerepr-copy:null",  "Vsa/Sim/ReprCopy.lean (read32_copy)"),
    "ValueRepr.bool":  ("valuerepr-copy:bool",  "Vsa/Sim/ReprCopy.lean (read32_copy)"),
    "ValueRepr.int":   ("valuerepr-copy:int",   "Vsa/Sim/ReprCopy.lean (readLE_copy)"),
    "ValueRepr.str":   ("valuerepr-copy:str",   "Vsa/Sim/ReprSurvival.lean (cstring_agreeP)"),

    # --- the 24 NO-CURE-SEMANTIC-GAP supplier fields (all ENCODE-GAP) ---
    # residual def : dominating predicate
    "hSExpr":         ("encode-gap:ExecExprGeom (∀-closed, machine seg)",     "ExecRecRows.ExprResid"),
    "hSRet":          ("encode-gap:ExecRetGeom (∀-closed, machine seg)",      "ExecRecRows.RetResid"),
    "hSRetNull":      ("encode-gap:ExecRetNullGeom (value_null bridge)",      "ExecRecRows.RetNullResid"),
    "hSVarNull":      ("encode-gap:ExecVarNullGeom (value_null+env_define)",  "ExecRecRows.VarNullResid"),
    "hSVarInit":      ("encode-gap:ExecVarInitGeom (∀-closed, machine seg)",  "ExecVarInitRow.VarInitResid"),
    "hSBlock":        ("encode-gap:BlockGeom + SeqSegIH (∀-closed)",          "ExecDispatchRows.BlockResid"),
    "hSIfNone":       ("encode-gap:IfGeom (∀-closed, machine seg)",           "ExecDispatchRows.IfNoneResid"),
    "hSIfTrue":       ("encode-gap:IfGeom + sub-ExecIH (∀-closed)",           "ExecDispatchRows.IfTrueResid"),
    "hSIfFalse":      ("encode-gap:IfGeom + sub-ExecIH (∀-closed)",           "ExecDispatchRows.IfFalseResid"),
    "hSWhileFalse":   ("encode-gap:WhileGeom (∀-closed, machine seg)",        "ExecDispatchRows.WhileFalseResid"),
    "hSWhileBreak":   ("encode-gap:WhileGeom (loop-break span)",              "ExecDispatchRows.WhileBreakResid"),
    "hSForStart":     ("encode-gap:ForGeom (loop scaffold seg)",              "ExecDispatchRows.ForStartResid"),
    "hSeqNil":        ("encode-gap:Triple SegEntry→SegExit (seq hop)",        "SeqForRows.SeqNilResid"),
    "hSeqConsNormal": ("encode-gap:Triple + head ExecIH (seq iter)",          "SeqForRows.SeqConsNormalResid"),
    "hSeqConsAbrupt": ("encode-gap:Triple + head ExecIH (abrupt span)",       "SeqForRows.SeqConsAbruptResid"),
    "hArgsNil":       ("encode-gap:Triple SegEntry→SegEntry (args hop)",      "CallRows.ArgsNilResid"),
    "hArgsCons":      ("encode-gap:EvalArgsStep + Triple (args body oracle)", "CallRows.ArgsConsResid"),
    "hVar":           ("encode-gap:Triple ArmEntryK→VarPostCall + LeafWiden", "EvalVarRow.VarLeafResid"),
    "hAssign":        ("encode-gap:AssignArmSpec (arm oracle, machine seg)",  "EvalAssignRow.AssignResid"),
    "hCall":          ("encode-gap:composite EvalIH call splice (4 states)",  "CallRows.CallResid"),
    "hCallPrint":     ("encode-gap:NativePrintSpec (∀-closed native seg)",    "CallRows.CallPrintResid"),
    "hCallPrintln":   ("encode-gap:NativePrintlnSpec (∀-closed native seg)",  "CallRows.CallPrintlnResid"),
    "hCallAssertOk":  ("encode-gap:NativeAssertOkSpec (∀-closed native seg)", "CallRows.CallAssertOkResid"),
    "hInitStore":     ("encode-gap:Steps ; SegEntry (interp_init decode)",    "EntrySeams.InterpInitStoreRepr"),
}

# The DISPATCH.md NO-CURE-SEMANTIC-GAP class + the PROVABLE-DIRECT ValueRepr leaf.
SUPPLIER_BATCH = [
    "hSExpr", "hSRet", "hSBlock", "hArgsNil", "hArgsCons", "hVar", "hAssign",
    "hInitStore", "hCall", "hSVarNull", "hSVarInit", "hSIfNone", "hSIfTrue",
    "hSIfFalse", "hSWhileFalse", "hSWhileBreak", "hSForStart", "hSRetNull",
    "hSeqNil", "hSeqConsNormal", "hSeqConsAbrupt", "hCallPrint", "hCallPrintln",
    "hCallAssertOk",
    # the leaf ValueRepr family already known PROVABLE-DIRECT:
    "ValueRepr.null", "ValueRepr.bool", "ValueRepr.int", "ValueRepr.str",
]

# ===========================================================================
# PART C — the per-field driver.
# ===========================================================================
def run_field(name):
    """Returns dict {field, verdict, detail, z3confirmed, time}."""
    if name not in FIELD_REGISTRY:
        return {"field": name, "verdict": "UNKNOWN-FIELD",
                "detail": "not in FIELD_REGISTRY", "z3confirmed": "n", "time": 0.0}
    encoding, origin = FIELD_REGISTRY[name]
    t0 = time.time()

    # (a) ENCODE-GAP: statement not expressible in the bounded QF-ABV fragment.
    if encoding.startswith("encode-gap"):
        why = encoding.split(":", 1)[1]
        return {"field": name, "verdict": "ENCODE-GAP",
                "detail": f"{origin}: {why}", "z3confirmed": "n",
                "time": round(time.time() - t0, 3)}

    # (b/c) valuerepr-copy: encodable.  Z3 direct-UNSAT check → PROVABLE-DIRECT,
    #       else SAT → Houdini → IH-FOUND / IH-NOT-FOUND.
    kind = encoding.split(":", 1)[1]
    # direct negation check (no IH):
    vdir, _, dtdir = z3_run(base_decls() + base_asserts(kind, control=False),
                            get_model=False)
    if vdir.startswith("unsat"):
        # non-vacuity: positive model must exist
        vpos, _, _ = z3_run(base_decls() + [
            "(assert (>= srcAddr 0))", "(assert (>= dstAddr 0))",
            f"(assert {G.valuerepr('m','srcAddr',kind,W)})",
            f"(assert {G.copy24('m','mp',drop=None)})",
            f"(assert {G.valuerepr('mp','dstAddr',kind,W)})"], get_model=False)
        vac = " (VACUOUS!)" if not vpos.startswith("sat") else ""
        return {"field": name, "verdict": "PROVABLE-DIRECT",
                "detail": f"neg UNSAT no-IH; leaf lemma {origin}{vac}",
                "z3confirmed": "y", "time": round(time.time() - t0, 3)}

    # SAT → IH needed. Run Houdini.
    survivors, log, vf = houdini(kind)
    if survivors and vf.startswith("unsat"):
        names = [c[0] for c in survivors]
        return {"field": name, "verdict": "IH-FOUND",
                "detail": f"survivors: {', '.join(names)}  (leaf {origin})",
                "z3confirmed": "y", "time": round(time.time() - t0, 3)}
    return {"field": name, "verdict": "IH-NOT-FOUND",
            "detail": f"neg SAT; no candidate subset closes goal "
                      f"(missing shape past the {kind} recursion cut)",
            "z3confirmed": "n", "time": round(time.time() - t0, 3)}

# ===========================================================================
# PART D — the ORIGINAL .str pilot main (default; ground-truth match check).
# ===========================================================================
def pilot_main():
    print("=== CTI mine (un-strengthened .str VC) ===")
    vc, out, dtc = z3_run(base_decls() + base_asserts("str", control=False))
    print(f"  verdict={vc}  time={dtc:.3f}s  (SAT expected => IH missing)")
    cands = all_candidates()
    print(f"\n=== Candidate vocabulary ({len(cands)}) ===")
    for name, _ in cands:
        print(f"  - {name}")
    print("\n=== Houdini ===")
    survivors, log, vf = houdini("str")
    for kind, a, v, dt in log:
        print(f"  [{kind:12}] {str(a):55.55} -> {v:8} {dt:5.2f}s")
    print("\n=== Surviving IH set ===")
    for name, expr in survivors:
        print(f"  - {name}")
    print(f"\nGoal closes (UNSAT) under survivors: {vf}")
    names = {n for n, _ in survivors}
    has_ptr = any(n.startswith("read64_copy@ptr") for n in names)
    has_pay = any(n.startswith("cstr_agreeP@payload") for n in names)
    match = has_ptr and has_pay
    print(f"\ncstring_agreeP content present?  ptr-eq={has_ptr}  payload-agree={has_pay}"
          f"  => MATCH={match}")
    return survivors, vf, match

# ===========================================================================
# PART E — CLI.
# ===========================================================================
def batch_list(spec):
    if spec == "all-supplier":
        return SUPPLIER_BATCH
    return [s.strip() for s in spec.split(",") if s.strip()]

def print_rows(rows):
    print(f"{'field':16} {'verdict':16} {'z3':3} {'time':6}  detail")
    print("-" * 100)
    for r in rows:
        print(f"{r['field']:16} {r['verdict']:16} {r['z3confirmed']:3} "
              f"{r['time']:6.3f}  {r['detail'][:60]}")

def storerepr_main():
    """Run the StoreRepr-survival Houdini probe (the recursive-Repr-cone twin of
    the .str pilot).  Delegates to experiments/smt/bounded/gen_storerepr.py, which
    encodes StoreRepr→FrameRepr→{ValueRepr,CString,φf-parent} bounded and runs the
    SAME maximal-consistent/minimal-sufficient Houdini loop.  Ground truth:
    Vsa/Sim/ReprSurvival.lean storeRepr_agreeP (frameRepr_agreeP ∘ valueRepr_agreeP
    ∘ cstring_agreeP + verbatim φf_inj/arena)."""
    import gen_storerepr as S
    S.main()

def main():
    ap = argparse.ArgumentParser(description="Houdini IH-selector / bounded-VC triage.")
    ap.add_argument("--field", help="one SkelName (e.g. hVar, ValueRepr.null)")
    ap.add_argument("--batch", help="comma-list of fields OR 'all-supplier'")
    ap.add_argument("--pilot", action="store_true",
                    help="run the original .str Houdini pilot (default if no field/batch)")
    ap.add_argument("--storerepr", action="store_true",
                    help="run the StoreRepr-survival recursive-cone Houdini probe")
    args = ap.parse_args()

    if args.storerepr:
        return storerepr_main()
    if args.field:
        r = run_field(args.field)
        print_rows([r]); return [r]
    if args.batch:
        rows = [run_field(f) for f in batch_list(args.batch)]
        print_rows(rows); return rows
    return pilot_main()

if __name__ == "__main__":
    main()
