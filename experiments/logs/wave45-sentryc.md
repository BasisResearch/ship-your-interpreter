# Wave 45 — lane sentryc (the SEntryC amendment + the tail/loop-back field landings)

HEAD at start: 80aab36 (wave 44).  Spec = `experiments/logs/wave44-bridgetwins.md`
(twin 1's obstruction + the RATIFIED amendment plan) + the `ArmSegSplitTwins`
module doc.

## Consumer re-thread list (re-derived by grep `SEntryC`, wave-45 state)

| file | refs | class | action |
|---|---|---|---|
| `Vsa/Sim/ApproxArmReseat.lean` | 4 | THE DEF | amend (3-way disjunction) |
| `Vsa/Sim/ArmStagesWave34.lean` | 29 | opaque premise types + `nonEvalChildStages_mk` field types | re-type 3 staging fields; new `_wave45_wired` |
| `Vsa/Sim/ArmSegSplitEval.lean` | 27 | opaque (`hstage` positions) | re-verify only |
| `Vsa/Sim/ArmSegSplitNonEval.lean` | 57 | PRODUCES (`landedN_sEntryC_of_preBundle`) + field types | `Or.inl` + re-type ifThen/ifElse/whileLoop |
| `Vsa/Sim/ArmSegSplitSqEntry.lean` | 14 | PRODUCES (`seqHead_split` pack) | `Or.inl` |
| `Vsa/Sim/ArmSegSplitExecEval.lean` | 11 | opaque | re-verify only |
| `Vsa/Sim/ArmStagesPartial.lean` | 5 | opaque | re-verify only |
| `Vsa/Sim/ApproxArmResidGapAssembly.lean` | 2 | opaque | re-verify only |
| `Vsa/Sim/ArmSegSplitTwins.lean` | 20 | DESTRUCTURES (obstruction core) + moved defs | restate over `SFreshC`; move `ExecDispatchEntry`/`SDispatchC` upstream |
| `rows/StmtExprArmStagePre.lean` | 2 | DESTRUCTURES (`obtain … := hSE`) | 3-way case + `*ReentryDispatch` residual |
| `rows/StmtRetArmStagePre.lean` | 1 | DESTRUCTURES | same |
| `rows/StmtVarInitArmStagePre.lean` | 1 | DESTRUCTURES | same |
| `rows/StmtIfCondArmStagePre.lean` | 1 | DESTRUCTURES | same |
| `rows/StmtWhileCondArmStagePre.lean` | 1 | DESTRUCTURES | same + `viaWhileArm` leg (only genuinely-while consumer) |
| `rows/StmtWhileBodyArmStagePre.lean` | 10 | opaque (residual takes `SEntryC` whole) | re-verify only |
| `rows/StmtForInitArmStagePre.lean` | 6 | opaque | re-verify only |
| `rows/StmtIfThenArmStagePre.lean` | 10 | obstruction tie-in destructure | restate over `SFreshC` |
| `rows/StmtForLoopSegPreB.lean` | 4 | opaque | re-verify only |

KEY CONSTRAINT found: wave 44's `rows/ArmDispatchInstancesExec.lean` DISCHARGED
the five `Stmt*ArmDispatch` residuals (via `execArmDispatch_of_slot`) — their
defs must NOT be re-typed (would break another lane's landed content).  The
reentry route therefore rides a NEW per-row named residual (`*ReentryDispatch`),
per the "adapter over re-typing" instruction.

## Landings (per-file log below, appended as they go green)

## §REVERT (coordinator, end of wave 45)

The lane stalled mid-flight: the amended `SEntryC` (3-way) landed upstream in
`ApproxArmReseat.lean` together with SOME consumers, but the per-row
`*ReentryDispatch` residuals + the `_wave45_wired` capstone threading were NOT
landed, leaving 7 committed consumer files red at stage a
(ArmSegSplitSqEntry, rows/Stmt{Expr,Ret,VarInit,IfCond,WhileCond}ArmStagePre,
rows/CallCruxMarshal5 — the `obtain … := hSE` destructures and the
`segExitJoin_frame_x8_false` restatement).  The twin-file dedup
(`ExecDispatchEntry`/`SDispatchC`/`execStmtDispatchHead` moved upstream,
duplicates deleted from ArmSegSplitTwins) and the SFreshC restatements of the
obstruction pair were completed coordinator-side, but the full consumer
surgery is the wave-46 statement-surgery lane per this log's §table.

**All sentryc-lane edits were REVERTED to the wave-44 state for the wave-45
green push** (`git restore`: ApproxArmReseat, ArmSegSplitNonEval,
ArmSegSplitTwins, CallEntry, InductionScaffold, LoopScaffoldClose,
rows/NativeArmSplice, rows/StmtIfThenArmStagePre).  Wave 46 re-lands the
amendment from this log + `wave44-bridgetwins.md` spec.
