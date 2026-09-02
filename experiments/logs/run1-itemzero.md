# Run 1 — ITEM ZERO B1 entry re-index (additive)

Sandbox: /tmp/vsa-itemzero-sandbox

## Plan
Add 3 additive fields to EvalEntry / ExecEntry (+ entry-extension structs):
- stackBudget : StackOK SL sp (need + (maxCallDepth - d) * perCallBudget + 1088)
- expr_bodies / stmt_bodies : bodiesBound perCallBudget X = true
- store_bodies : StoreBodiesBound st.store perCallBudget

Then fix ~22 construction sites; regen cone; inhabit probe.

## Progress log
- B0 StackNeed.olean rebuilt at .lake/build/lib/lean/Vsa/While/StackNeed.olean (axiom-clean).

## Files amended (B1 additive)
Primary entries:
- Vsa/Sim/InterpEntry.lean: +import StackNeed; EvalEntry +stackBudget/+expr_bodies/+store_bodies
- Vsa/Sim/ExecEntry.lean: ExecEntry +stackBudget/+stmt_bodies/+store_bodies
Entry-extension structs (re-list EvalEntry fields, literal expr):
- Vsa/Sim/EvalNullSim.lean (EvalNullEntry), EvalBoolSim.lean (EvalBoolEntry),
  EvalStrSim.lean (EvalStrEntry), EvalVarSim.lean (EvalVarEntry): +3 fields each
Leaf/router construction sites (forward from hc — already entry-conditioned by prior refactor):
- Vsa/Sim/rows/TermRouting.lean (null/bool/str rows), rows/EvalVarRow.lean
Marshalling seams (add 3 budget conjuncts to hpre + forward):
- Vsa/Sim/ArmSegSplit.lean, ArmSegSplitExec.lean, ArmSegSplitExecEval.lean,
  EvalRecCommon.lean (armTail_rec), ExecRecCommon.lean (armTail_rec_es),
  ExecBlock.lean (blockSubStmt)
Loop-head / seq-head:
- Vsa/Sim/rows/LoopHeadDispatch.lean (LoopHeadDispatchGeom +3 fields, depth 0),
  SeqHeadStages.lean (execEntry_recast_depth specialized d0:=0, stackBudget via StackOK.mono)
Recursive-arm sim (add 3 budget conjuncts to Triple pre + forward to armTail_rec):
- Vsa/Sim/EvalNegSim.lean (blockB_unary)  [FIRST of the fan-out class — MORE below]
Inhabit probe: experiments/itemzero_inhabit_probe.lean (GREEN, axiom-clean, omega-free).

## Wave 47a resume (2026-09-02, main tree)
- B1 patch (experiments/wip/itemzero-b1-amendment.patch) applied to main: 17/52
  files were already half-applied by the stalled run; remaining 35 applied clean.
- REPAIRS found during the sanity sweep (the stall's unverified residue):
  - ExecRecCommon.execExprGlue/execExprSimC: armTail_rec_es call site never
    forwarded the 3 budget conjuncts — added them as named premises + forwarded.
  - ArmSegSplitExecEval.ExecJalPreBundle: exec twin of JalPreBundle missed the
    +3 conjuncts (landedN_eentryC_of_execPreBundle red) — amended to match.
  - ArmSegSplitNonEval.ExecStmtPreBundle: same for the stmt-level bundle
    (execEntry_of_jalPrefix's amended pre) — +3 conjuncts appended.
- NEW KIT (Vsa/While/StackNeed.lean, axiom-clean): `StackOK.child` (the ONE
  parent→child frame-lowering budget step) + `bodiesBound` projection lemmas
  (assign/unary/binary/logical/call, Stmt.expr). Every consumer derivation goes
  through these — no per-site BitVec.toNat_sub re-derivation.
- FAN-OUT landed (each `lake env lean` green, olean regenerated):
  - EvalAndSim (blockB_logical +3 pre conjuncts; consumer site derives L-trio
    from EvalEntry.stackBudget via StackOK.child)
  - EvalOrSim, EvalNotSim, EvalNegSim3 (consumer-site derivations)
  - EvalBinSim (blockB_binary +6: L over st, R over st')
  - EvalLogical3/EvalLogical4 (blockC_andTrue/blockC_orFalse +3 R-conjuncts;
    AndTrueExtras/OrFalseExtras +store_bodiesR field; both call sites derive)
  - rows/Eval{Add,Sub,Lt,Le,Gt,Ge,Mul,Div,Mod}Row + EvalEqNeRow: Goal pre towers
    +6 conjuncts (mail-merged), forwarded to blockB_binary
  - rows/BinArmBridge: NEW `blockA_binaryArm_budgeted` (named repacker deriving
    the 5 entry-derivable conjuncts once; post-LEFT store-bodies = ONE premise)
  - rows/BinArmBridgeProbe reseated on the budgeted bridge (+1 premise)
- NOTE: Vsa/Sim/EvalCallClosure.lean found PRE-EXISTING red (written against the
  pre-nf/nc SegExit — stale since before wave 45; olean dated Aug 29; not
  imported by Vsa.lean, not in check_all). NOT a B1 casualty; left untouched
  (out of scope), excluded from the B1 sweep.

## Wave 47a fan-out COMPLETE (2026-09-02)
Full B1 fan-out sweep GREEN: 122-file dependency-ordered `lake env lean -o`
cone (changed set + every armTail_rec/armTail_rec_es/jalPrefix/JalPreBundle/
ExecJalPreBundle/blockB_* consumer), all oleans regenerated. Landings beyond
the earlier checkpoint:
- MidArmCombinator (binaryR_midStagePre/midStage1 +3 R-premises),
  MidArmFieldIH (MidArmRightMarshal +3; midArmField_of_IH pre +3 L-conjuncts),
  MidArmFieldWire (MidArmLeftJalBundle +3 L-conjuncts)
- StagePreSuppliers (blockB_unary_stagePre, blockB_binary_leftStagePre +3),
  StagePreSuppliers2 (blockB_logical_stagePre +3)
- EvalChildFieldCombinator: binaryL/unaryE/logicalL fields DERIVE the trio
  from EvalEntry via StackOK.child + bodiesBound projections
- rows/AssignArmStagePre + rows/CallArmStagePre (+3 pre; field composers
  derive from the entry; fixed a latent missing-hopStk positional shift in
  both composers' destructures)
- rows/FlCondArmStagePre (+3 at the stmt frame; ghost jsp-1088 = sp-176 via
  BitVec.add_sub_cancel), rows/Stmt{Expr,IfCond,Ret,VarInit,WhileCond}
  ArmStagePre (mail-merged, both bundle towers per file)
- rows/EvalEqNeFront (evalEqSimD/evalNeSimD towers +6)
- rows/BinDispatchRow: BinIntCellResid/BinEqCellResid gain the ONE
  store-bodies residual conjunct; all 11 binRow_* reseated on
  blockA_binaryArm_budgeted; eval_binary_row shell threads it
- SeqHeadStages: repaired the patch's stale `simp; exact` (No goals) → omega
- ExecRecCommon execExprGlue/execExprSimC, ArmSegSplitExecEval
  ExecJalPreBundle, ArmSegSplitNonEval ExecStmtPreBundle (earlier checkpoint)
Gates: experiments/wip/itemzero_inhabit_probe.lean GREEN axiom-clean;
axiom probe over 24 key amended theorems: all ⊆ {propext, Classical.choice,
Quot.sound}; `lake env lean Vsa.lean` loads clean; check_discipline OK
(9 rules). observations.md gains `store-bodies-eval-preservation` (the ONE
genuinely missing general fact — threaded as named residuals for now).

## Wave 47b — ITEM ZERO replay-bundle application to main (2026-09-02)
Bundle: /tmp/itemzero-apply (sandbox-validated). Base: 298ea7d clean.
- Patches 01-08: ALL asserts fail on `old` text — diagnosed as ALREADY LANDED
  by wave 47a (298ea7d includes the composed ITEM ZERO + B1 amendment; its own
  run1-itemzero.md log describes it). Verified semantically: every `new`
  string of every patch (incl. the PAIRS/SECTIONS forms of 06/07/08) is
  verbatim present in the current tree; deletions confirmed (ForResid def
  gone, hFl* GAP fields gone from TermResidualsCore, rows wired). Zero
  partial writes (all patch scripts write only after all asserts).
- Step 9 gen_assembly_skeleton.py --no-verify: .lean already at 58 holes
  (idempotent); TSV had 4 stale hFl rows — regen dropped them (only diff).
- Step 10/11 topo regen: SKIPPED — no .lean source changed this session;
  spot-check: key oleans all newer than sources.
- Step 12 battery (all serial, one lean process):
  * B1_leaves_obstructions.lean FAILS (4 errors: `∅` witness lands in BitVec
    slot after binder shift — the refutations no longer state);
  * B2_Field_{hNeg,hNot,hAndTrue,hAndFalse,hOrTrue,hOrFalse}.lean ALL FAIL
    (hNeg 4 errors, siblings 1 each);
  * B5ExecArmObstructions.lean FAILS (11 errors, incl. termResidualsCore_false
    dead — the record is no longer machine-refutable);
  * B6LoopSeqObstruction.lean FAILS (motive-shape obstruction no longer states).
  * experiments/fleet/AmendedGroundEvidence.lean (from bundle) GREEN,
    4/4 witness-closure lemmas axiom-clean;
  * experiments/fleet/AxiomProbe.lean GREEN, 12/12 probes axioms ⊆
    {propext, Classical.choice, Quot.sound}.
- Step 13 field_census.py -j4: {'NOT_FOUND': 58} — 58 rows, zero TYPE_ERROR;
  field-census.tsv re-baselined (63→58 rows: 4 hFl + extension-only hErrFam).
- Step 14 check_all.sh: hSeqNil_row/hFlLoop_row comments corrected; added
  hFlCondFalse_row/hFlBodyBreak_row/hFlBodyRet_row, "execIH_of_exitSim'"
  (quoted — primed name), TermSimAssembly.seqSpanGround_of; all 6 verified
  resolving axiom-clean via `import Vsa` probe.
- Step 15: 4 lost observations entries re-appended (b3-bincell-resids-
  refutable, seq-motive-multi-pair-census, code-free-segentry-args-call-spans,
  sandbox-external-resync-stomp).
- check_discipline: OK (9 rules).
