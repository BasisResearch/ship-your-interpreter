# Lane E5: `exec_stmt`'s statement arms

Branch `lane-e5` (from `wave4-base`; merged `hub/iris-main` at INTEGRATION.md,
`hub/lane-e6` (SpecLoop), `hub/lane-e1` (`ReadOK.win`), `hub/lane-e2`
(`CoreOK`, `errCtx`)). Design: `VsaIris/INTERP_DESIGN.md` §4, §6, §8 (row
"exec"); statement changes in §10 "STATEMENT CHANGES (E5)". Rows:
`scripts/iris_arms/arms.d/e5-exec.tsv`.

## Status: done — every arm of the family in both modes

All axioms ⊆ {propext, Classical.choice, Quot.sound} (`VsaIris/Interp/E5Audit.lean`,
40 declarations, imported by `VsaIris/Audit.lean`). No holes added
(`check_iris_holes.py` passes: 10 ledgered, none from E5). Drift gate clean.

| arm (`ExecSCost`/`ExecS` ctor) | total | partial | family |
|---|---|---|---|
| `brk`, `cont` | `caseT_ExecBrk`/`Cont` | `caseP_ExecBrk`/`Cont` | `execConst` |
| `expr` | `caseT_ExecExpr` | `caseP_ExecExpr` | `execEval1 tail=epi` |
| `ret` (e) | `caseT_ExecRet` | `caseP_ExecRet` | `execEval1 tail=ret` |
| `retNull` | `caseT_ExecRetNull` | `caseP_ExecRetNull` | `execNullRet` |
| `ifTrue`/`ifFalse`/`ifNone` | `caseT_ExecIfTrue`/`False`/`None` | `caseP_ExecIf` (every outcome) | `execIfTrue/False/None`, `execIfAll` |
| `while*` (any while derivation) | `caseT_ExecWhile` | `caseP_ExecWhile` | `execWhile` (over E6) |
| `forStart` | `caseT_ExecFor` | `caseP_ExecFor` | `execFor` (over E6) |
| `block` | `caseT_ExecBlock` | `caseP_ExecBlock` | `execBlock` (over G's seqLoop) |
| `varInit` / `varNull` | `caseT_ExecVarInit`/`Null` | `caseP_ExecVarInit`/`Null` | `execVarInit`/`execVarNull` |

## Interface for A (and E6)

- **STATEMENT CHANGE: the exec motive is `execDispT_body D`**, stated at the
  dispatch point `0x80004014` (`SpecExecDisp.lean`), because gcc made the `if`
  branch an in-frame tail call (`j 0x80004014`, `bnez s0,0x80004014`). The
  partial Löb hypothesis is `execDispsP Core`. `ExecDisp.lean`:
  `execSpecT_of_disp`, `execSpecP_of_disp`, `execSpecsP_of_disps` give the
  entry specs to every `jal exec_stmt` caller (E6's loops, G's seqLoops, the
  closure body, `interp_run`). E6's `execSpecT_body D ∧ …while…` becomes
  `execDispT_body D ∧ …while…`.
- Case hypotheses (all as specs/motives, no proof imports): children's
  `evalSpecT_body`/`execDispT_body`; `whileT_body`/`whileP_body`,
  `execInitT_body`/`forLoopT_body`, `execInitP_body`/`forLoopP_body` (E6:
  `whileP_all`, `forLoopP_all`, `execInitP_all` supply the partial ones);
  G's `blockSeqT_body` (total; `blockSeqP_all` is used directly in partial);
  helper specs `valueNullSpec`, `valueTruthySpec` (H2), `envNewSpec`,
  `envDefineSpec` (H1).
- Partial error premises follow E2: `errCtx inp` (resource), `CoreOK N L Room
  inp Core`, `NewlibHoles`, `CodeLive live`. Allocating arms are stated at
  `vsaLayoutP`/`vsaRoomB`.
- Open for A (recorded in `PROOF_CLOSURE_PLAN.md`): the top-level handler of
  an out-of-memory abort under `Core := abortCore … 0x88000000 0x800000`.

## Layers (hand)

- `SpecExecDisp.lean` (statement), `ExecDisp.lean` (prologue, entry specs,
  `execDispT_apply`/`execDispP_apply`).
- `ExecArm.lean`: node facts (`StmtNode`, `ExprFieldNode`, `IfNode`), the two
  shared exits for either WP (`wp_execEpi` at `0x8000409c`, `wp_execRetCopy` at
  `0x80004138`, `wp_execEpiRet` at `0x80004150`), `ms_callEvalPF` (partial child
  call from a frame of any size), `ms_callHelperSlot`/`ms_callHelperVal`,
  `ms_valCarve`/`ms_valUncarve`, `ms_slotIn`/`ms_valOut`, the in-frame tail call
  (`ifRedispatch`, `execDispKP_redispatch`), `ix_esaved`, `ix_execRet`.
- `SymLater.lean`: `wp_swpF_later` (a symbolic run that pays a Löb later).
- `ExecIf.lean`, `ExecLoops.lean` (while/for dispatch, `wp_loopExit`),
  `ExecBlock.lean` (`blockNode_of`), `ExecVar.lean` (`varTail`, `varTailP`),
  `ExecEnv.lean` (`ms_callEnvNew(W)`, `ms_callEnvDefine`,
  `storeRepr_frameAt_ne`), `ExecOom.lean` (`ms_callRegsAbort`, `oom_regs`,
  `ms_callEnvNewP`, `ms_callEnvDefineP`).

## Generator (additions only; G's, E1's and E2's rows regenerate identically)

- `gen_iris_cases.py`: exec rows may start at the dispatch point (`EXEC_DISP`);
  a family may emit one mode only (the three total `if` rows, one partial row).
- Families `execConst`, `execEval1` (tail snippets
  `execEval1_tail_{epi,ret}_{T,P}`, `execEval1_seg_epi`), `execNullRet`,
  `execIfTrue/False/None/All`, `execWhile`, `execBlock`, `execFor`,
  `execVarInit`, `execVarNull`.

## Line counts (generated vs hand)

| arm | generated T | generated P |
|---|---|---|
| brk / cont | 96 / 96 | 74 / 74 |
| expr / ret e | 136 / 117 | 124 / 111 |
| ret; | 131 | 106 |
| if (3 T, 1 P) | 42 + 42 + 37 | 59 |
| while | 69 | 89 |
| for | 126 | 182 |
| block | 184 | 227 |
| var init / null | 104 / 110 | 120 / 125 |

Generated: 2,581 lines (24 files). Hand: templates 2,191 lines (most families
are one row: their template is the proof), layers 3,725 lines, table 18 rows.

## Build
`lake build Vsa VsaIris VsaIris.Audit` green (2,528 jobs). **E1/E2 `errCtx` clash:** E1's
`LeafErr` and E2's `SpecErr` both define `VsaIris.Interp.errCtx` (different bodies), so both
cannot be imported together. As E4 did (`e5b6ca4`), this branch keeps E2's (E5's partial
allocating arms use `errCtx`/`CoreOK` from `SpecErr`) and leaves E1's `LeafErr` and the
`var`/`assign` cases over it out of the root and audit imports (commented, marked). The
integrator must pick one `errCtx`.

## Findings

- The `if` in-frame tail call (above).
- Duplicates to fold later: E6's `LoopKit` has `execSP_off` (over
  `ExecFrameGeom`; E5's is `execSP_offF`), `ms_callEvalPx` (≈ E5's
  `ms_callEvalPF`), `ms_truthyCall` (≈ `ms_callHelperVal` + `valueTruthySpec`).
