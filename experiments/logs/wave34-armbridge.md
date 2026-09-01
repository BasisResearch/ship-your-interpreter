# Wave 34 — arm-dispatch bridge parametrization (Task, picking up from stall)

## Goal
Parametrize `blockA_binaryArm`'s shape into a reusable arm-dispatch bridge, then
instantiate `blockA_unaryArm`/`blockA_logicalArm` and close unaryE/logicalL fields
via `evalChildField_of_blockA_stage` + the landed staging cuts.

## Context established (reading pass)
- `blockA_binaryArm` (Vsa/Sim/rows/BinArmBridge.lean, COMMITTED): runs `blockA_k`
  at (tag 6, PC 0x800034e8, UnaryArmCallee), destructures ArmEntryK copy, transports
  BOTH operand ptrs (aLOp/aROp) m0→ment, packages `blockB_binary_leftStagePre`'s hpre.
  Conditional on `BinArmExtras`.
- `blockB_unary_stagePre` (StagePreSuppliers.lean): hpre = ∃ ment, ArmEntryK@0x800035e0
  UnaryArmCallee + x11=aIn + gpre-frame + 1 operand ptr + geometry conjuncts.
  Tag 8. Callee UnaryArmCallee = Value_intLoaded ∧ IntSlotPinned.
- `blockB_logical_stagePre` (StagePreSuppliers2.lean): hpre = ∃ ment, ArmEntryK@0x8000355c
  LogicalArmCallee + x11=aIn + x13=aEnv3 + gpre-frame + 1 operand ptr (LEFT, via surv-closure)
  + geometry. Tag ? Callee LogicalArmCallee (4-conj: int/slot/truthy/bool loaded).
- `evalNegSim` (EvalNegSim3.lean) ALREADY contains the blockA_k→blockB_unary composition
  in-line (lines 199-282) — the exact prologue+destructure+transport I must factor into
  `blockA_unaryArm`. Its hpre-assembly is the direct model.
- blockA_k signature (EvalIntSim2.lean:261): params (k, armPC, calleeLoaded, hcalleeSurv,
  hexprSurv, ...). Output: ∃ ment v8 v9 v18, ArmEntryK ... . calleeLoaded is a Mem→Prop
  parameter, so unary/logical/binary differ ONLY in {tag, armPC, calleeLoaded+surv, #operands, post}.

## Plan
1. blockA_unaryArm: UnaryArmExtras struct + bridge → blockB_unary_stagePre hpre.
2. blockA_logicalArm: LogicalArmExtras (+x13) + bridge → blockB_logical_stagePre hpre.
3. Factor shared core if budget-clean; else keep 3 arm bridges + note table option.
4. Wire unaryE/logicalL fields via evalChildField_of_blockA_stage.

## Landings (update after EACH)
- [DONE] `blockA_unaryArm` (Vsa/Sim/rows/UnaryLogicalArmBridge.lean) — EX_UNARY arm
  bridge `EvalEntry (.unary op esub) → blockB_unary_stagePre hpre`, MODULO
  `UnaryArmExtras` (NegExtras stagePre subset). Verified axiom-clean first try
  (~first run). Body = evalNegSim block-A prefix cut at hpre. Realign out0 via _hAout.
  POST binds ∃ v8 v9 v18 ment.
- [DONE] `blockA_logicalArm` (same file) — EX_LOGICAL arm bridge (tag 7, 0x8000355c,
  LogicalArmCallee) → blockB_logical_stagePre hpre, MODULO `LogicalArmExtras` +
  x13-reach (threaded via Triple precondition, as evalAndSim). Axiom-clean.
- [DONE] `unaryE_field_of_extras` + `logicalL_field_of_extras`
  (Vsa/Sim/EvalChildFieldCombinator.lean §3/§4) — the unary/logicalL EvalChildStages
  fields, machine-composed via evalChildField_of_blockA_stage (k=2 / k=3):
  blockA_unaryArm ≫ blockB_unary_stagePre, blockA_logicalArm ≫ blockB_logical_stagePre.
  MODULO UnaryArmGeomProvider / LogicalArmGeomProvider (arm-geometry residuals, the
  BinArmGeomProvider analogues). All 4 field composers axiom-clean. Olean regen'd.
  PARAMETRIZATION VERDICT: the shared blockA_k→destructure→transport body is IDENTICAL
  across binary/unary/logical; the 3 bridges differ only in {tag, armPC, calleeLoaded,
  #operands, post shape}. The output-post genuinely differs (per-arm conjunct lists
  the downstream stagePre's demand), so a single theorem would need the post as a
  param → trivial. Kept 3 concrete bridges (binaryArm committed + unary/logicalArm here);
  the DE-DUP win is that evalChildField_of_blockA_stage §1 is the ONE seam all three
  plug into for the field-level composition (already factored last wave).
- [DONE] `evalChildStages_ublr_wired` (ArmStagesWave34 §1b) — partial EvalChildStages
  with unary/binaryL/logicalL ALL machine-composed (3 fields), modulo the 3 geometry
  providers; other 11 fields named. divFamily_wave34 re-verified axiom-clean. Discipline OK.

## FINAL per-field board (EvalChildStages, 14 fields)
| field | status |
|---|---|
| unary   | **FIELD-COMPOSED** (unaryE_field_of_extras) mod UnaryArmGeomProvider |
| binaryL | FIELD-COMPOSED (binaryL_field_of_extras) mod BinArmGeomProvider |
| binaryR | staging landed, NOT wired — needs mid-arm SubEvalReturn blockA (aFTER-left dispatch) |
| logicalL| **FIELD-COMPOSED** (logicalL_field_of_extras) mod LogicalArmGeomProvider |
| logicalR| NOT landed — value_truthy-seam variant + mid-arm blockA |
| assignE/callF/argsHead | NOT landed — arm-head cut + blockA (eval/args dispatch) |
| stmt*/flCond (6) | NOT landed — exec-side arm-head cuts (exec entry 0x80003fe0) |

3 of 14 eval-child fields now machine-composed (was 1). Remaining recursive-eval
arm bridges: binaryR/logicalR are MID-arm (post-left-return SubEvalReturn entry, a
DIFFERENT dispatch bridge than blockA_k — see binaryR_midStagePre note in wave34-81).

## Wiring lines (report-only; NOT applied)
Add to Vsa.lean:
    import Vsa.Sim.rows.UnaryLogicalArmBridge   -- (imported transitively via EvalChildFieldCombinator)
Add to scripts/check_all.sh axiom-checked list:
    Vsa.Sim.blockA_unaryArm
    Vsa.Sim.blockA_logicalArm
    Vsa.Sim.unaryE_field_of_extras
    Vsa.Sim.logicalL_field_of_extras
    Vsa.Sim.divFamily_wave34   (already listed — re-verified)
  (all ⊆ {propext, Classical.choice, Quot.sound})

## FINAL STATE
All 3 touched files verify green + axiom-clean fresh (consolidated re-run). Oleans
regenerated at .lake/build/lib/lean/... . Discipline check OK (8 rules). Observation
+ parametrization verdict logged to experiments/observations.md. No sibling collision.
Blocker for further fan-out (assignE/callF/argsHead/logicalR/exec-side): unbuilt
per-arm blockB_*_stagePre machine cuts — honest, not a falsity.
