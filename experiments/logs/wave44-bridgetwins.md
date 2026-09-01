# Wave 44 — lane bridgetwins (statement surgery: the non-eval bridge twins)

HEAD at start: 8991fdd (wave 43). Spec = observations
`nonevalchild-remaining-8-shape-map` + `experiments/logs/wave43-nonevalmm.md`.

## Landing 1 — `Vsa/Sim/ArmSegSplitTwins.lean` (GREEN, axiom-clean, ~all <2s)

All 22 theorems `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
Verified `lake env lean`; olean emitted via `lake env lean -o` (never lake build).

### §1 Twin 1 — tail re-dispatch (stmtIfThen / stmtIfElse; NOT stmtWhileLoop)

**FINDING (Law 4, machine-checked): the frozen field CONCLUSION is unreachable
on the tail arms — item-4 fires.**  `SEntryC` demands `ExecEntry` whose `pc`
field literally pins `execStmtEntry = 0x80003fe0`; the if-then arm's terminator
is `j 0x80004014` (`0xde5ff06f @0x80004230`), the else arm's the taken
`bnez s0,0x80004014` (`@0x800042d0`) — the child runs in the SAME frame from the
post-prologue dispatch head, and `0x80003fe0` is never revisited with the child
node.  Obstruction core landed:
- `sEntryC_pins_entry_pc` (named PC destructurer for the SEntryC bundle)
- `sEntryC_false_at_dispatchHead` (decidable refutation at 0x80004014)

**The honest twin layer (landed):**
- `execStmtDispatchHead : Nat := 0x80004014`
- `StepInto` / `GRegsHopInto` — terminator-AGNOSTIC one-step hops (mem/out
  preserving; the rich one adds the non-noise GPR frame).  Instantiators:
  `gregsHopInto_of_jx0Site` (`sigmaPost_jump_x0` — the ifThen `j`),
  `gregsHopInto_of_branchTakenSite` (`sigmaPost_branch_taken` — the ifElse
  `bnez`), both off the BlockTerm `pc/mi/frame_term_*_bt` consumers.
- `ExecDispatchEntry` — NAMED-FIELD post-prologue dispatch-head entry
  (pc=0x80004014, s0/s1/s2/s3 = aStmt/aInterp/aRet/aEnv, a6=8,
  a4=stmtJumpTableBase, spD lowered w/ `StackOK SL spD 1088`, mem/code/stmt/
  store/store_survives/out/frame + geometry — `ExecEntry` minus the
  call-boundary a0-a3/ra fields).
- `SDispatchC` — its ∃-bundle (the amended-field landing shape).
- `execEntry_of_jTailRedispatch` — the twin: `GRegsHopInto` + staged pre →
  `LandedN 1 (ExecDispatchEntry …)`.
- `ExecStmtTailPreBundle` + `landedN_sDispatchC_of_preBundle` +
  `execTailChildSplit_of_stage` + `stmtIfThen_splitT` / `stmtIfElse_splitT`
  (amended-shape splits, conclusion `LandedN 1 (SDispatchC child)`).

**stmtWhileLoop is a THIRD shape** — its loop-back `bne a0,a5,0x80004034`
re-enters the WHILE-ARM head (0x80004034, post-dispatch), NOT the dispatch head
(no a4/a6 rematerialization on that path).  Not covered by ExecDispatchEntry;
needs a while-arm entry predicate (or fold-recursion re-seat) — reported in the
amendment plan, not forced.

**AMENDMENT PLAN (NOT applied — not signature-free):** re-seat `SEntryC` (or the
fold's stmtIfThen/stmtIfElse/stmtWhileLoop recursion targets) on
`SEntryC ∨ SDispatchC`; supply the fresh-call disjunct by the 14-instr prologue
seg `0x80003fe0→0x80004010` (unbuilt `#derive_case` span).  Consumer re-thread
list (grep SEntryC): ArmStagesWave34 (29), ArmSegSplitEval (27),
ArmSegSplitSqEntry (14), ArmSegSplitExecEval (11), ArmStagesPartial (5),
ApproxArmResidGapAssembly (2), rows/Stmt{WhileBody,ForInit,Expr,WhileCond,
VarInit,Ret,IfCond}ArmStagePre.  Full plan in the ArmSegSplitTwins module doc.

### §2 Twin 2 — `SegPreBundleB` (branch/fallthrough/jalr SegEntry entry)

- `SegPreBundleB` = `SegPreBundle` with the static-jal-site premise replaced by
  the abstract hop `StepInto entryPC` (one mem/out-preserving step into the
  entry — j / branch / jalr / fallthrough all qualify).
- `segPreBundleB_of_jal` — the jal model strictly refines B (old suppliers ride).
- `landedN_segEntry_of_preBundleB` + `landedN_{a,c,f}EntryC_of_preBundleB` +
  `{args,callee,for}ChildSplit_of_stageB` + the FIVE field splits
  `callArgs_splitB` / `argsTail_splitB` / `callC_splitB` / `stmtForLoop_splitB` /
  `flLoop_splitB` — each concluding the EXACT frozen `ApproxArmResid` field type
  (those are fine: AEntryC/CEntryC/FEntryC anchor on SegEntry at a GHOST PC).
- NOTE: `NonEvalChildStages`' 5 seg fields stay `SegPreBundle`-typed (amending
  them breaks `nonEvalChildStages_mk`/`_wave43_wired` in forbidden files);
  wave-45 assembly feeds the `*_splitB` outputs into the `ApproxArmResidGap`
  literal directly (or a future `NonEvalChildStagesB` + `armResidGap_…B` beside).

### §3 Twin 3 — `flStep_split'`

- Exec-frame twin of `flStep_split`, staging typed to `ExecJalPreBundle`
  (falsity-#7 class), finishing via `execEvalChildSplit_of_stage`; conclusion is
  the exact `ApproxArmResid.flStep` field type (`LandedN 1 (EEntryC e)`).
- `ArmStages.flStep` stays `JalPreBundle`-typed (re-typing breaks
  `armStages_mk`/`divFamily_of_armStageComponents`/`divFamily_wave34/40/42`
  premise lists) — wave-45 consumes `flStep_split'` directly when building
  `ApproxArmResidGap`.

## Landing 2 — pilot 1: `Vsa/Sim/rows/StmtIfThenArmStagePre.lean` (GREEN, axiom-clean)

- `stmtIfThenTailSeg` — 2-block `#derive_case` chain `0x8000421c → 0x8000422c`
  (li a6,8; auipc a4; addi a4,-616; **mid-chain not-taken `beqz`**; ld s0,16(s0)),
  parked AT the `j 0x80004014` site 0x80004230.  auipc IS decode-table supported.
- `stmtIfThenTailRow` — segToTriple, ONE ChainOK decide; post carries the
  symbolic `x16 = 8` projection (`gholds_lookup … (by rfl)` — the `by decide`
  free-var + `by rfl` deep-whnf gotchas both hit; see below).
- `stmtIfThenTail_a4_computed` — GROUND kernel `decide`: the auipc/addi fold
  computes exactly `stmtJumpTableBase` (0x80019fb8) — `ExecDispatchEntry.a4`
  staging dischargeable.  (Symbolic version blocked: observation
  `lookupG-evalBlocks-value-peel-missing` filed.)
- `stmtIfThenTail_target_not_sEntryC` — pilot-level obstruction tie-in.
- `IfThenArmHeadInv` / `IfThenTailStagePre` / `IfThenTailDispatch` named
  residuals (wave-43 WhileBody shape) + `stmtIfThen_tailField_of_dispatch`
  (amended staging field) + `stmtIfThen_amended_of_dispatch` (composes through
  `stmtIfThen_splitT` to `SDispatchC t`).

## GOTCHAS hit (for the wave-45 mail-merge)

- Symbolic `gholds_lookup` value proofs: small-positive-imm constants (`li`)
  close `by rfl`; `auipc`+negative-`addi` folds blow the elaborator (stack
  overflow) — keep them out of symbolic posts, ground-`decide` them separately.
- j-terminator tuple: `⟨pc, word, b0..b3(LE), .j, 0, 0, 0#13, imm21, 0#12⟩`,
  imm21 = 21-bit two's-complement byte offset (0x80004230→0x80004014 =
  0x1ffde4#21).  Branch: `.br bop.BEQ <taken>, rs1, rs2, imm13`.
- New-file olean: `lake env lean -o .lake/build/lib/lean/<path>.olean <file>`
  before verifying a dependent file.

## Landing 3 — pilot 3 (twin 3): `Vsa/Sim/rows/FlStepArmStagePre.lean` (GREEN, axiom-clean)

The for-STEP arm as a wave-43-shape row (StmtWhileBody template clone, exec-eval
seam):
- `flStepBodySeg` — `#derive_case` (mv a3,s3; mv a1,s1; addi a0,sp,16 @
  0x800042dc..e4), all words tabled.
- `flStepBridge` — `bridgeOfSeg` ≫ `jal eval_expr @0x800042e8` (target
  0x80003164, link 0x800042ec); seg run + ABI frame FREE; `hfacts`/`hjalSeam`
  the only residuals.
- `FlStepArmHeadInv` / `FlStepArmStagePre` (lands at `ExecJalPreBundle` — the
  exec-frame seam, ghost rebase sp := esp+1088) / `FlStepArmDispatch` named
  residuals + `flStep_stageField_of_dispatch` (the exec-typed ArmStages.flStep
  staging) + `flStep_field_of_dispatch` (composes `flStep_split'` to the EXACT
  frozen `ApproxArmResid.flStep` field type, `LandedN 1 (EEntryC e)`).

## Landing 4 — pilot 2 (twin 2): `Vsa/Sim/rows/StmtForLoopSegPreB.lean` (GREEN, axiom-clean)

- `forCondReentryPC := 0x8000426c`; `ForLoopReentryJSite` (the
  `j @0x80004258` `sigmaPost_jump_x0` site obs, named residual) +
  `ForLoopReentryInv` (light SegEntry facts at the `j` site).
- `forLoopSegPreB_of_inv` — **PROVED**: inv → `SegPreBundleB 0x8000426c`
  (hop = `gregsHopInto_of_jx0Site ≫ StepInto.of_gregsHop`).  First real
  interior-control arm inhabiting the B bundle (jal-model `SegPreBundle` was
  uninstantiable there).
- `ForLoopReentryDispatch` (named) + `stmtForLoop_field_of_dispatch` — the EXACT
  frozen `ApproxArmResid.stmtForLoop` field via `stmtForLoop_splitB`.

## Addendum — `stepInto_of_jalrSite` (twins file §1.2)

The `callC` entry class (`jalr` closure dispatch, writes its link register →
only the LIGHT hop holds) gets its own instantiator: `sigmaPost_jalr` site obs →
`StepInto tgtPC`.  All four entry classes now instantiate the B bundle:
j (`gregsHopInto_of_jx0Site`), taken-branch (`gregsHopInto_of_branchTakenSite`),
jal (`segPreBundleB_of_jal`), jalr (`stepInto_of_jalrSite`).

## FINAL STATE

Files (all `lake env lean` green, `#print axioms` ⊆ {propext, Classical.choice,
Quot.sound}; discipline gate OK):
- `Vsa/Sim/ArmSegSplitTwins.lean` (23 theorems + 2 structures/bundles + hops)
- `Vsa/Sim/rows/StmtIfThenArmStagePre.lean` (twin-1 pilot)
- `Vsa/Sim/rows/FlStepArmStagePre.lean` (twin-3 pilot)
- `Vsa/Sim/rows/StmtForLoopSegPreB.lean` (twin-2 pilot)
Observation filed: `lookupG-evalBlocks-value-peel-missing`.

### What each twin unlocks
- Twin 2 (`SegPreBundleB` + 5 `*_splitB`): callArgs, argsTail, callC,
  stmtForLoop, flLoop — their FROZEN field conclusions are reachable; only the
  staging bundle changed.  Wave-45 = per-arm dispatch/site residual supply
  (mail-merge on the StmtForLoopSegPreB template).
- Twin 3 (`flStep_split'`): flStep — frozen field conclusion reachable; wave-45
  feeds `flStep_field_of_dispatch` into the `ApproxArmResidGap` literal directly
  (bypassing the mistyped `ArmStages.flStep` premise).
- Twin 1 (`ExecDispatchEntry`/`SDispatchC` + splits): stmtIfThen/stmtIfElse —
  CONDITIONAL on the SEntryC amendment (frozen conclusions machine-unreachable,
  obstruction `sEntryC_false_at_dispatchHead`); stmtWhileLoop is a third shape
  (bne → while-ARM head 0x80004034) still needing its own entry predicate.

### WIRING (coordinator; nothing applied to Vsa.lean/check_all by this lane)
Vsa.lean imports:
  import Vsa.Sim.ArmSegSplitTwins
  import Vsa.Sim.rows.StmtIfThenArmStagePre
  import Vsa.Sim.rows.FlStepArmStagePre
  import Vsa.Sim.rows.StmtForLoopSegPreB
check_all THEOREMS:
  Vsa.Sim.sEntryC_false_at_dispatchHead, Vsa.Sim.execEntry_of_jTailRedispatch,
  Vsa.Sim.landedN_sDispatchC_of_preBundle, Vsa.Sim.stmtIfThen_splitT,
  Vsa.Sim.stmtIfElse_splitT, Vsa.Sim.segPreBundleB_of_jal,
  Vsa.Sim.landedN_segEntry_of_preBundleB, Vsa.Sim.callArgs_splitB,
  Vsa.Sim.argsTail_splitB, Vsa.Sim.callC_splitB, Vsa.Sim.stmtForLoop_splitB,
  Vsa.Sim.flLoop_splitB, Vsa.Sim.flStep_split',
  Vsa.Sim.stmtIfThenTailRow, Vsa.Sim.stmtIfThenTail_a4_computed,
  Vsa.Sim.flStepBridge, Vsa.Sim.flStep_field_of_dispatch,
  Vsa.Sim.forLoopSegPreB_of_inv, Vsa.Sim.stmtForLoop_field_of_dispatch
