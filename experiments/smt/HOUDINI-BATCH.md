# Houdini IH-selector — batch over the supplier class

Date: 2026-09-02. Tool: `scripts/houdini_ih.py --field <SkelName>` / `--batch
<list|all-supplier>` (generalises the `.str` pilot in `HOUDINI-IH.md`). Solver:
Z3 4.15.4 via `z3 -in` (pure oracle). Encoder: `experiments/smt/bounded/gen_probe.py`
(imported as G). Whole batch runs in <2s.

## Method (per field)

Each supplier field routes through a residual `*Resid`/`*Spec` def in the tree
(`Vsa/Sim/rows/*.lean`, `EntrySeams.lean`). The driver classifies by the
DOMINATING predicate of that residual's Prop:

- **(a) encodable?** Only the `ValueRepr` copy-readback obligation lives in the
  bounded QF-ABV fragment (`Mem = def:Array Int Bool, val:Array Int (BV8)`;
  `read32`/`readI64`/`read64` byte-unfolded; `copy24` the 24-struct-byte copy).
  Everything else is a ∀-closed bundle over MACHINE-STEP predicates
  (`Triple`/`SegEntry`/`SegExit`/`ExecEntry`/`Exec*Geom`/`Native*Spec`/`Steps`)
  the encoder cannot express → **ENCODE-GAP**, reported honestly with the exact
  dominating predicate cited.
- **(b) Z3 direct-UNSAT of the negation** (no IH)? → **PROVABLE-DIRECT**
  (non-recursive stratum leaf; corresponding Lean leaf lemma noted; non-vacuity
  confirmed by a positive `H∧C∧Cncl` model).
- **(c) else SAT → mine candidates** (`*_agree*`/`*_copy*`/`*_preserv*` zoo + the
  CTI from Z3's model), run Houdini to the maximal-consistent minimal-sufficient
  subset, Z3-confirm it closes the goal → **IH-FOUND** (survivors listed) or
  **IH-NOT-FOUND** (vocabulary insufficient; missing shape named).

## Per-field result

| field | verdict | IH lemmas / reason | Z3-conf | time |
|---|---|---|---|---|
| hSExpr | ENCODE-GAP | ExecRecRows.ExprResid — ExecExprGeom (∀-closed machine seg) | n | 0.00s |
| hSRet | ENCODE-GAP | ExecRecRows.RetResid — ExecRetGeom (∀-closed machine seg) | n | 0.00s |
| hSRetNull | ENCODE-GAP | ExecRecRows.RetNullResid — ExecRetNullGeom (value_null bridge) | n | 0.00s |
| hSVarNull | ENCODE-GAP | ExecRecRows.VarNullResid — ExecVarNullGeom (value_null+env_define) | n | 0.00s |
| hSVarInit | ENCODE-GAP | ExecVarInitRow.VarInitResid — ExecVarInitGeom (∀-closed machine seg) | n | 0.00s |
| hSBlock | ENCODE-GAP | ExecDispatchRows.BlockResid — BlockGeom + SeqSegIH (∀-closed) | n | 0.00s |
| hSIfNone | ENCODE-GAP | ExecDispatchRows.IfNoneResid — IfGeom (∀-closed machine seg) | n | 0.00s |
| hSIfTrue | ENCODE-GAP | ExecDispatchRows.IfTrueResid — IfGeom + sub-ExecIH (∀-closed) | n | 0.00s |
| hSIfFalse | ENCODE-GAP | ExecDispatchRows.IfFalseResid — IfGeom + sub-ExecIH (∀-closed) | n | 0.00s |
| hSWhileFalse | ENCODE-GAP | ExecDispatchRows.WhileFalseResid — WhileGeom (∀-closed machine seg) | n | 0.00s |
| hSWhileBreak | ENCODE-GAP | ExecDispatchRows.WhileBreakResid — WhileGeom (loop-break span) | n | 0.00s |
| hSForStart | ENCODE-GAP | ExecDispatchRows.ForStartResid — ForGeom (loop scaffold seg) | n | 0.00s |
| hSeqNil | ENCODE-GAP | SeqForRows.SeqNilResid — Triple SegEntry→SegExit (seq hop) | n | 0.00s |
| hSeqConsNormal | ENCODE-GAP | SeqForRows.SeqConsNormalResid — Triple + head ExecIH (seq iter) | n | 0.00s |
| hSeqConsAbrupt | ENCODE-GAP | SeqForRows.SeqConsAbruptResid — Triple + head ExecIH (abrupt span) | n | 0.00s |
| hArgsNil | ENCODE-GAP | CallRows.ArgsNilResid — Triple SegEntry→SegEntry (args hop) | n | 0.00s |
| hArgsCons | ENCODE-GAP | CallRows.ArgsConsResid — EvalArgsStep + Triple (args body oracle) | n | 0.00s |
| hVar | ENCODE-GAP | EvalVarRow.VarLeafResid — Triple ArmEntryK→VarPostCall + LeafWiden | n | 0.00s |
| hAssign | ENCODE-GAP | EvalAssignRow.AssignResid — AssignArmSpec (arm oracle machine seg) | n | 0.00s |
| hCall | ENCODE-GAP | CallRows.CallResid — composite EvalIH call splice (4 states) | n | 0.00s |
| hCallPrint | ENCODE-GAP | CallRows.CallPrintResid — NativePrintSpec (∀-closed native seg) | n | 0.00s |
| hCallPrintln | ENCODE-GAP | CallRows.CallPrintlnResid — NativePrintlnSpec (∀-closed native seg) | n | 0.00s |
| hCallAssertOk | ENCODE-GAP | CallRows.CallAssertOkResid — NativeAssertOkSpec (∀-closed native seg) | n | 0.00s |
| hInitStore | ENCODE-GAP | EntrySeams.InterpInitStoreRepr — Steps ; SegEntry (interp_init decode) | n | 0.00s |
| ValueRepr.null | PROVABLE-DIRECT | neg UNSAT no-IH; leaf `read32_copy` (ReprCopy.lean) | y | 0.03s |
| ValueRepr.bool | PROVABLE-DIRECT | neg UNSAT no-IH; leaf `read32_copy` (ReprCopy.lean) | y | 0.04s |
| ValueRepr.int | PROVABLE-DIRECT | neg UNSAT no-IH; leaf `readLE_copy` (ReprCopy.lean) | y | 0.03s |
| ValueRepr.str | IH-FOUND | `read64_copy@ptr(mp_p=m_p)`, `cstr_agreeP@tail`, `cstr_agreeP@payload[0..2]` = `cstring_agreeP` content (ReprSurvival.lean) | y | 0.9s |

## Coverage rollup (honest)

| verdict | count | fields |
|---|---|---|
| ENCODE-GAP | 24 | all NO-CURE-SEMANTIC-GAP supplier fields (the whole DISPATCH.md class) |
| PROVABLE-DIRECT | 3 | ValueRepr.null / .bool / .int (leaf copy-readback) |
| IH-FOUND | 1 | ValueRepr.str (blind Houdini rediscovers `cstring_agreeP`) |
| IH-NOT-FOUND | 0 | — |

**Automatable stratum vs full Lean stack.** Of the 28 fields probed, **4 (the
ValueRepr leaf family) are in the bounded-SMT automatable stratum** — 3 proved
outright, 1 IH-selected + Z3-confirmed. **All 24 genuine supplier fields are
ENCODE-GAP**: their statements are ∀-closed bundles over the machine-step /
segment / geometry / native-spec predicates (`Triple`, `SegEntry`/`SegExit`,
`ExecEntry`, `Exec*Geom`, `Native*Spec`, `Steps`), none of which the QF-ABV
memory model can express. This is NOT a Houdini failure — it is the honest reach
of bounded-SMT into the supplier class: **0% of the NO-CURE-SEMANTIC-GAP fields
are automatable, 100% need the full Lean abstraction stack** (`#derive_case`
segs, `callSeg`, `segToTriple`, the `*Geom` folds — exactly the tools in
CLAUDE.md's dispatch table).

## Why every supplier field is ENCODE-GAP (mechanism)

The bounded encoder reasons about BYTES in a `Mem` array. The supplier residuals
do not talk about bytes; they assert the existence of a machine-step `Triple`
between two `SegEntry`/`SegExit` PC-indexed configurations, or a `*Geom` bundle
of register/frame geometry facts, ∀-closed over the layout ghosts
(`g N A SL φf φc`) and often carrying a sub-`ExecIH`/`EvalIH` induction
hypothesis. Encoding one would require encoding the RISC-V step relation and the
whole segment-derivation calculus in SMT — precisely what the Lean stack
proves, and precisely outside the "memory-arithmetic leaf" pocket the
`BOUNDED-PROBE.md` / `HOUDINI-IH.md` results already delimited. The
`hVar`/`VarLeafResid` field DOES contain mineable memory-arithmetic sub-clauses
(pointer/arena disjointness), but its statement is DOMINATED by a `Triple
ArmEntryK→VarPostCall` conclusion + `LeafWiden`, so the field as a whole is
ENCODE-GAP; the disjointness fragments are not the field's obligation.

## Conclusion

Bounded-SMT + blind Houdini is a legitimate, cheap (<2s) IH-selector/triage
oracle for the **leaf memory-arithmetic supplier fields** (the `ValueRepr`
copy-readback family), where it proves the non-recursive cases outright and
rediscovers the `cstring_agreeP` payload-agreement IH for the recursive `.str`
case with Z3 confirmation. It reaches **none** of the 24 machine-step supplier
fields — an ENCODE-GAP-heavy result that is the honest measure of how far
bounded-SMT penetrates the supplier class. Those fields remain the Lean
abstraction stack's job, by design.
