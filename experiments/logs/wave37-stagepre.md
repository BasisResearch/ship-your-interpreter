# Wave 37 — the remaining ArmStages stagePre cuts (assignE / callF / argsHead + exec)

## Board on entry (from wave 36)
- eval-child: 5/14 machine-composed (unary, binaryL, binaryR, logicalL, logicalR).
  Remaining 9: assignE, callF, argsHead, stmtExpr, stmtRet, stmtVarInit,
  stmtIfCond, stmtWhileCond, flCond (last 6 are exec/for-side EEntryC-valued).
- SqEntry: seqHead wired; stmtBlock/callBody named.
- flStep: named.

## Structural analysis (done before any build)

The `assignE`/`callF`/`argsHead` fields want:
  `EEntryC c st d env (node) → LandedN 1 c (fun c' => JalPreBundle child c' st d env)`
Closed via `assignE_split`/`callF_split`/`argsHead_split` (ArmSegSplitEval), which
reduce to a stagePre residual of the SAME shape (they are pure `evalChildSplit_of_stage`
wrappers). So each field == one stagePre supplier.

The stagePre supplier decomposes (per EvalChildFieldCombinator) as:
  blockA dispatch bridge (EvalEntry → ArmEntryK-post)  ⊗  blockB arm-head cut (site_*_ee chain → JalPreBundle)

### Gen segs are the WRONG marshalling layer
`AssignArmEntryGen` / `CallArmCalleeEvalGen` exist BUT they use `bridgeOfSeg`: they
FIRE the jal and land at the callee entry `0x80003164` as a raw ABI-framed `Steps`
chain, discarding the rich `ExprRepr`/`StoreRepr`/geometry facts. `JalPreBundle`
requires the state AT the jal PC (before firing) carrying all those repr facts. So
the Gen segs do NOT supply the cut. Confirms wave-36 D3.

### The honest path (blockB_unary_stagePre model)
Per-PC `site_*_ee` lemmas at the arm PCs, composed by hand into a `JalPreBundle`.
- assign arm span: 0x8000347c ld a2,16(a2) ; 0x80003480 addi a0,sp,240 ; 0x80003484 sd a3,0(sp) ; jal@0x80003488
  → EXACTLY the binaryL-left shape (ld+addi+sd), 3 steps. site_*_ee NOT yet built for these PCs.
- call arm span: 0x800031b0 ld a2,8(a2) ; 0x800031b4 addi a0,sp,96 ; 0x800031b8 sd a3,0(sp) ; jal@0x800031bc
  → same 3-step shape. site_*_ee NOT yet built.
- argsHead: entry is AEntryC (EvalArgs), child jal is the per-arg eval INSIDE the
  arg loop; the arg-loop-entry seg is BRANCH-terminated (blez a5), not jal-reaching.
  HARDER — not the uniform ld+addi+sd shape.

All decode_* DecodeTable lemmas for the assign/call instructions EXIST
(01063603/0f010513/00d13023 ; 00863603/06010513). So site_*_ee are buildable.

### The blockA dispatch bridge gap
assignE/callF have NO `blockA_*Arm` bridge and none of its inputs
(`*ArmCallee` predicate / `*_writeMap8` survival / `KindSlotPinned` tag). Building
the full field (EEntryC → JalPreBundle) therefore ALSO needs the dispatch bridge,
which is a separate ~200-line battery per arm.

## Decision
Build the arm-head `site_*_ee` + `blockB_*_stagePre` cuts for assignE and callF
(the uniform ld+addi+sd shape), delivered as `*StagePre`-typed suppliers over the
ArmEntryK entry bundle — the SECOND factor, mirroring `blockB_unary_stagePre` /
`blockB_binary_leftStagePre`. The blockA dispatch bridge remains the honest
upstream residual (as it is for unary/binary/logical — those close modulo their
GeomProvider which is exactly the dispatch input). Track counts via LandedN/StepCount.


## RESULTS

### Landed (green + axiom-clean, oleans regenerated)
- `Vsa/Sim/rows/AssignArmStagePre.lean` (~380 lines):
  - `site_8000347c_as`/`site_80003480_as`/`site_80003484_as`/`site_80003488_as` — assign arm-head site lemmas
  - `blockB_assign_stagePre` — assign arm-head → JalPreBundle e (LandedN 3), the SECOND factor
  - `AssignArmDispatch` (dispatch residual) + `assignE_field_of_dispatch` — the EvalChildStages.assignE field composer
- `Vsa/Sim/rows/CallArmStagePre.lean` (~410 lines):
  - `site_800031b0_cf`/`site_800031b4_cf`/`site_800031b8_cf`/`site_800031bc_cf` — call arm-head site lemmas
  - `blockB_call_stagePre` — call arm-head → JalPreBundle f (LandedN 3)
  - `CallArmDispatch` + `callF_field_of_dispatch` — the EvalChildStages.callF field composer
- `Vsa/Sim/ArmStagesWave34.lean` (edited, OWNED this wave):
  - added imports of both new rows; new builder `evalChildStages_ublrac_wired`
    wires assignE + callF via the dispatch composers → 7/14 eval-child machine-composed.
    `divFamily_wave34` unchanged (still green + axiom-clean).

### Counts (StepCount/LandedN)
- Both cuts are delivered as `LandedN 3` (3 arm-head steps), composed via
  `evalChildField_of_blockA_stage` (Steps.toN + StepsN.trans_add) with the k=3 arg,
  weakened to `LandedN 1` — no hand step arithmetic. Same counting layer as the
  landed unary/binary/logical fields.

### argsHead — NOT the uniform shape (blocked)
argsHead's entry is `AEntryC` (EvalArgs), and the child jal is the per-arg eval
INSIDE the arg loop; the arg-loop-entry seg (CallClosureArgLoopEntryGen) is
BRANCH-terminated (blez a5), not a jal-reaching ld+addi+sd head. Needs the arg-loop
front + the per-arg eval jal marshalling — a distinct (harder) shape. Deferred.

### exec-side stmt* — DIFFERENT shape (out of the eval 3-step class)
The exec stmtExpr arm (0x80004170) head is
`ld a2,8(s0) ; addi a0,sp,16 ; mv a3,s3 ; mv a1,s1 ; jal eval_expr@0x80003164` — a
FIVE-instruction head with two `mv` moves, an s0-based operand load, and the EXEC
frame buffer at sp+16 (no -1088 lowering; exec_stmt has its own prologue/frame).
`JalPreBundle` pins the EVAL frame (sp-1088, x12=aExpr, the 4 callee-saved slots at
sp-8..sp-32). The exec arm lands the child eval in the exec frame, so it needs an
`ExecEntry`→`JalPreBundle` marshalling via `execEntry_of_jalPrefix` (ArmSegSplitExec)
plus its own `_es` site battery. NOT the uniform eval 3-step; deferred as a separate
(larger) class. Recorded in observations `exec-stmt-stagepre-different-frame`.

## Board on exit
- eval-child: **7/14** machine-composed (unary, binaryL, binaryR, logicalL, logicalR,
  **assignE**, **callF**). Remaining 7: argsHead, stmtExpr, stmtRet, stmtVarInit,
  stmtIfCond, stmtWhileCond, flCond.
- non-eval (11 exec/args/for fields): unchanged (named).
- SqEntry: seqHead wired; stmtBlock/callBody named.
- flStep: named.

## Wiring lines (report-only; Vsa.lean/check_all.sh NOT touched — coordinator owns them)
Vsa.lean: ArmStagesWave34 is ALREADY imported (line 555), and it now imports
  `Vsa.Sim.rows.AssignArmStagePre` + `Vsa.Sim.rows.CallArmStagePre` transitively — so
  no new Vsa.lean import is strictly needed. If direct imports are wanted:
    import Vsa.Sim.rows.AssignArmStagePre
    import Vsa.Sim.rows.CallArmStagePre
check_all.sh axiom-checked list (all ⊆ {propext, Classical.choice, Quot.sound}):
    Vsa.Sim.blockB_assign_stagePre
    Vsa.Sim.assignE_field_of_dispatch
    Vsa.Sim.blockB_call_stagePre
    Vsa.Sim.callF_field_of_dispatch
    Vsa.Sim.evalChildStages_ublrac_wired   (the 7/14 capstone builder)

## Verify results (all one serial `lake env lean`, oleans into .lake/build/lib/lean/)
- Vsa/Sim/rows/AssignArmStagePre.lean — GREEN, axioms clean, discipline OK
- Vsa/Sim/rows/CallArmStagePre.lean — GREEN, axioms clean, discipline OK
- Vsa/Sim/ArmStagesWave34.lean — GREEN, axioms clean, discipline OK (divFamily_wave34 intact)
