# Wave 43 lane nonevalmm — the 11 NonEvalChildStages fields + SqEntry + flStep

Plan queue item 6. Supply the staging residuals for the NON-eval child stages:
- 11 `NonEvalChildStages` fields (ArmSegSplitNonEval.lean): stmtIfThen, stmtIfElse,
  stmtWhileBody, stmtWhileLoop, stmtForInit, flBody, callArgs, argsTail, callC,
  stmtForLoop, flLoop.
- SqEntryStages: stmtBlock, callBody (+ seqHead if open).
- flStep (flStep_split in ArmSegSplitEval).

Each field lands at `ExecStmtPreBundle`/`SegPreBundle`/`JalPreBundle` (NOT SEntryC).
The `*_split` theorems finish (consume field → SEntryC/AEntryC/...).

## Model = wave-41 argsHead (rows/ArgsHeadArmStagePre.lean):
seg (#derive_case, straight-line → jal) + bridge (bridgeOfSeg) proved; the
marshalling residual (`*StagePre`) + dispatch residual (`*Dispatch`) named as typed
premises (Law 2); `*_field_of_dispatch` composes.

## Arm-head disasm (recursive jal exec_stmt @0x80003fe0 sites; exec_stmt 0x80003fe0..4308)

| field         | arm-head span            | terminator            | notes |
|---------------|--------------------------|-----------------------|-------|
| stmtIfThen    | 0x80004074→80 → 84       | jal exec_stmt (taken) | ld a1,16(s0);mv a3,s2;mv a2,s3;mv a0,s1 |
| stmtWhileBody | 0x800041a4→c0 → c4       | jal exec_stmt         | while-body loop, spills a6 |
| stmtForInit   | 0x80004248→50 → 54       | jal exec_stmt         | for-init (after env_new) |
| flBody(?)/for-body | 0x800042a8→b4 → b8  | jal exec_stmt         | for-body (after value_truthy) |

Only 4 `jal exec_stmt` sites: 80004084, 800041c4, 80004254, 800042b8. The other
NonEval fields (stmtIfElse/stmtWhileLoop/callArgs/argsTail/callC/stmtForLoop/flLoop)
land at SegPreBundle interior control (j/b), NOT fresh jal exec_stmt. NEED to map
which spec field maps to which machine arm — the exec_stmt decode is a big dispatch.

## Site batteries: NONE exist for these arm heads (checked). Use #derive_case seg +
   bridgeOfSeg (argsHead lesson — no hand sites).

## Progress

### LANDED stmtIfThen (rows/StmtIfThenArmStagePre.lean) — green + axiom-clean
- `stmtIfThenBodySeg` (#derive_case, 4 instrs 0x80004074→80: ld a1,16(s0); mv a3,s2;
  mv a2,s3; mv a0,s1) + `stmtIfThenBodyBridge` (bridgeOfSeg, jal exec_stmt @0x80004084,
  target 0x80003fe0, link 0x80004088). FIRST TRY.
- `IfThenArmHeadInv` / `IfThenArmStagePre` / `IfThenArmDispatch` — named residuals
  (marshalling to ExecStmtPreBundle + dispatch from SEntryC), exactly the argsHead
  ArgsLoopHeadInv/ArgsHeadStagePre/ArgsHeadDispatch shape.
- `stmtIfThen_field_of_dispatch` — composes to the exact NonEvalChildStages.stmtIfThen
  field type. AXIOM-CLEAN.

### UNIFORMITY (exponentiation, per CLAUDE.md): the 4 SEntryC-landing jal-exec_stmt
arms (stmtIfThen, stmtWhileBody, stmtForInit, + the for-body arm) are STRUCTURALLY
IDENTICAL modulo (body instr list, jal PC/link, child-node read offset). Each is:
#derive_case seg (straight-line head) + bridgeOfSeg (jal exec_stmt) + 3 residual defs
+ 1 composer. ~110 lines, ~30 of which are pure boilerplate rename. Template = the
argsHead file. See observation `nonevalchild-jal-exec_stmt-arms-uniform`.

The other 7 fields (stmtIfElse/stmtWhileLoop/callArgs/argsTail/callC/stmtForLoop/
flLoop) land at SegPreBundle via interior control (j/b jumps to loop heads), NOT
fresh jal exec_stmt — a DIFFERENT (lighter) shape (SegPreBundle, segEntry_of_jalPrefix).

## FINAL STATE (wave 43, lane nonevalmm) — re-grounded after stall

RE-VERIFIED (lake env lean, all green + axioms ⊆ {propext,Classical.choice,Quot.sound}):
- rows/StmtWhileBodyArmStagePre.lean  (stmtWhileBodyBridge, stmtWhileBody_field_of_dispatch)
- rows/StmtForInitArmStagePre.lean    (stmtForInitBodyBridge, stmtForInit_field_of_dispatch)
- rows/FlBodyArmStagePre.lean         (flBodyBodyBridge, flBody_field_of_dispatch)
- ArmStagesWave34.lean (nonEvalChildStages_wave43_wired threads the 3 dispatch residuals; green)

LANDED: 3 of the 11 NonEvalChildStages fields — the genuine `jal exec_stmt` arms:
  stmtWhileBody @jal 0x80004084, stmtForInit @jal 0x80004254, flBody @jal 0x800042b8.
  Each = #derive_case body seg + bridgeOfSeg(jal exec_stmt) + ArmHeadInv/ArmStagePre/
  ArmDispatch named residuals + field composer. (prior session; NOT regressed.)

REMAINING (8 NonEval + 3 SqEntry + flStep) — NOT landed; each has a machine-shape
mismatch with its declared pre-bundle target (full map in observations.md entry
`nonevalchild-remaining-8-shape-map` + `ifstmt-then-else-tail-redispatch-not-jal`):
  - stmtIfThen/stmtIfElse/stmtWhileLoop: tail-redispatch / loop-back branch, NOT jal
    → target `ExecStmtPreBundle` (fresh jal+prologue) is wrong shape.
  - callArgs/argsTail/callC/stmtForLoop/flLoop: land at `SegPreBundle` (jal-site model)
    but the interior entry is a fallthrough/branch/jalr target — no static jal to it.
  - stmtBlock/callBody/seqHead: `SqLoopHeadPreBundle` needs the `Reflect` witness
    (crux/IterSeam boundary, plan #4) + SegEntry at interp_run loop head 0x8000448c.
  - flStep: `jal eval_expr` in the EXEC frame but flStep_split hardcodes eval-frame
    `JalPreBundle` (sp-1088). Needs `ExecJalPreBundle` re-param + execEvalEntry twin,
    OR a flStep_split' re-typed to ExecJalPreBundle.

DECISION (Law 4): did NOT force false pre-bundle attributions. The 8+3+1 need NEW
bridge twins (j-tail-redispatch / branch-entry SegEntry / jalr-entry SegEntry /
exec-frame JalPreBundle) or field/combinator re-typing — statement surgery, out of
this lane's template-instantiation scope. Machine-checked obstruction, not a hack.

## WIRING (coordinator — nothing new to wire this session; prior session already did):
Vsa.lean imports (already present from prior session? VERIFY — if not, add):
  import Vsa.Sim.rows.StmtWhileBodyArmStagePre
  import Vsa.Sim.rows.StmtForInitArmStagePre
  import Vsa.Sim.rows.FlBodyArmStagePre
check_all THEOREMS:
  Vsa.Sim.stmtWhileBodyBridge, Vsa.Sim.stmtWhileBody_field_of_dispatch
  Vsa.Sim.stmtForInitBodyBridge, Vsa.Sim.stmtForInit_field_of_dispatch
  Vsa.Sim.flBodyBodyBridge, Vsa.Sim.flBody_field_of_dispatch
  Vsa.Sim.nonEvalChildStages_wave43_wired
