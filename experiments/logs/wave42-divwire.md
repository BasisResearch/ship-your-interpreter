# Wave 42 lane divwire — close the eval-child side of the divergence board (14/14)

Task: extend `Vsa/Sim/ArmStagesWave34.lean` with the 6 newly field-composed pieces
(wave-41 lanes execmm + argshead), each swapping a `∀`-premise for a strictly-smaller
named dispatch residual. Produce `evalChildStages_*_wired` + capstone `divFamily_wave42`.

## Grounding (done)
- Model chain: `evalChildStages_binaryL_wired → ublr → ublrac → ublracSE` (each wave
  added a suffix letter). §1d `ublracSE_wired` already wires stmtExpr (8/14), leaving
  6 `∀`-premises: argsHead, stmtRet, stmtVarInit, stmtIfCond, stmtWhileCond, flCond.
- Wave-40 capstone `divFamily_wave40` takes the `eval : EvalChildStages` bundle directly
  (all wiring is in the builder), so `divFamily_wave42` = same body, new doc.
- Field-composer signatures confirmed:
  - `stmtRet_field_of_dispatch (e c st d env) (hDisp : StmtRetArmDispatch e st d env c) : SEntryC ... → LandedN 1 ...`
  - stmtVarInit: `(x e c st d env) (hDisp : StmtVarInitArmDispatch x e st d env c)`
  - stmtIfCond: `(cnd t els c st d env) (hDisp : StmtIfCondArmDispatch cnd t els st d env c)`
  - stmtWhileCond: `(cnd b c st d env) (hDisp : StmtWhileCondArmDispatch cnd b st d env c)`
  - flCond: `(cc step b c st d env) (hDisp : FlCondArmDispatch cc step b st d env c) : FEntryC ... → LandedN 1 ...`
  - argsHead: `argsHead_field_of_dispatch (e es c st d env) (hDisp : ArgsHeadDispatch e es st d env c) (hAE : AEntryC ...) : LandedN 1 ...`
    (takes hDisp THEN hAE — the exact shape the argshead report proposed).
- Imports needed in ArmStagesWave34.lean: rows.{StmtRet,StmtVarInit,StmtIfCond,
  StmtWhileCond,FlCond,ArgsHead}ArmStagePre.

## Landings
- LANDED (green + axiom-clean {propext, Classical.choice, Quot.sound}):
  - Imports added to ArmStagesWave34.lean: rows.{StmtRet,StmtVarInit,StmtIfCond,
    StmtWhileCond,FlCond,ArgsHead}ArmStagePre.
  - `evalChildStages_ublracSEA_wired` (§1e) — builds on `ublracSE_wired`, swaps the 6
    remaining eval-child `∀`-premises (argsHead + 5 exec-eval) for their dispatch
    residuals. First-try from the model. All 6 field-composers wired as fun-thunks.
  - `divFamily_wave42` (§5) — capstone, body identical to `divFamily_wave40`
    (`divFamily_of_armStageComponents`); the progress is in the eval bundle's build.
- VERDICT: EvalChildStages FULLY machine-composed, 14/14 eval-child-side. Named
  remainder = 6 dispatch residuals: ArgsHeadDispatch, StmtRetArmDispatch,
  StmtVarInitArmDispatch, StmtIfCondArmDispatch, StmtWhileCondArmDispatch, FlCondArmDispatch
  (+ the earlier geometry/dispatch residuals for the 8 already-wired fields).
- `lake env lean Vsa/Sim/ArmStagesWave34.lean` GREEN, no maxHeartbeats bump, no new file.

## Mechanical-work note
The 6-field swap was fully mechanical (one fun-thunk per field, identical shape modulo
the arm's binder list + hDisp application), exactly as the model prescribed — the shared
abstraction (`*_field_of_dispatch` composers + `evalChildStages_mk` positional fields)
already exists, so no new abstraction was warranted (this is the intended terminal
instantiation of the wave-34..42 wiring ladder, not duplicated proof work).
