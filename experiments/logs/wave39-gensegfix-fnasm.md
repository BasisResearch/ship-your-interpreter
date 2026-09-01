# Wave 39 — genseg lds fix + evalFnSim assembly

## Task A: genseg jal-row lds fix
- FIX applied to scripts/genseg.py emit_jal_row: threaded `(lds : List (List (BitVec 8)))`
  binder, replaced all literal `[]` with `lds` in SegEvalState.init/ChainFacts/bridgeOfSeg/
  hjalSeam/conclusion. Doc updated.
- Affected Gen jal rows (span contains ld/lw/lb):
  - AssignArmEntryGen (ld a2,16(a2))
  - AssignArmStageGen  (ld a1,8(s0); ld a6,240(sp); ld a4,248(sp); ld a5,256(sp); ld a0,0(sp))
  - CallArmCalleeEvalGen (ld a2,8(a2))
  - CallClosureEnvDefineCallGen (ld a1,0(a4))
  - CallClosureEnvNewCallGen (ld a0,8(a3))
- Not affected (no loads): CallClosureValueNullCallGen, DriveSpillGen, FnArmMallocCallGen.
- Consumers: only CallClosureSplice.lean references envNew/envDefine Bridge — in PROSE
  comments only, never invoked; instantiates seg at []. Statement only GAINS lds => name kept.

### Task A RESULT — COMPLETE
- Re-emitted 5 files; diffs are EXACTLY the lds threading (verified by diff).
- All 5 GREEN + axiom-clean {propext, Classical.choice, Quot.sound}. Oleans regenerated.
- Consumers verified GREEN + axiom-clean:
  - CallClosureSplice.lean (references Gen Bridges in PROSE only)
  - CallClosureFoldStage.lean (imports EnvDefineCallGen; uses *Seg/*L only, 0 Bridge refs)
  - CallClosureDispatchStage.lean (imports EnvNewCallGen; uses *Seg/*L only, 0 Bridge refs)
- Same theorem names kept (statements only GAIN lds generality; consumers instantiate seg at []).
- No new names needed. No wiring change (files already imported).

## Task B: evalFnSim assembly

### KEY FINDING: eval_fn_row ALREADY EXISTS (recursor hFn slot is FILLED)
- `Vsa/Sim/rows/CallRows.lean:364 eval_fn_row` already fills the recursor's hFn slot
  (routes to `evalFnSimD` over `FnResid`), green + axiom-clean. My separate EvalFnRow.lean
  was redundant → deleted.
- The OPEN work is the `FnResid` SUPPLIER (no provider existed; TermAssembly demands it).

### DELIVERED: Vsa/Sim/rows/FnResidSupply.lean (GREEN, axiom-clean, discipline-clean)
Three theorems, all axioms ⊆ {propext, Classical.choice, Quot.sound}:
- `store_size_of_allocClosure` — hfr/hcl (frames fixed, closures+1) = TRIVIAL, discharged
  (Task B item c: store-size monotonicity). axioms=[propext].
- `fnArmGeom_hArm_offdiag` — builds `FnArmGeom.hArm` (off-diagonal φc→φc') from the
  diagonal `fnArmGeom_hArm_of_seam` (φc'→φc') + named φc-entry-rebase `hEntryRebase`.
  Consumes the 9 dispatch facts (Task B item a) + hSeam. Record-update `{hc with …}` over
  EvalEntry overriding ONLY store/store_survives (the only φc-dependent fields) — no
  positional nav (R6/R7 clean).
- `fnResid_of_pipeline` — SUPPLIES the FnResid conjunction (FnArmSpec ∧ EvalRecWiden)
  from: hAlloc, hpc/hout, the 9 dispatch facts, hSeam, hEntryRebase, hW. Assembles
  FnArmGeom → fnArmSpec_of_geom (item b) → FnArmSpec.

### The 9 dispatch facts (Task B item a) — fn tag identified
- fn kind = 10 (ExprRepr `.fn` reads read32=10; matches hkle:k≤10), arm PC = 0x800033c4.
- The int/null/bool/str-shaped clone: hkle/hklt/hkind/hslot(KindSlotPinned 10 0x800033c4)/
  hcallee/hcalleeSurv/hexprSurv/harmAl/htableStk. Threaded as premises to
  fnArmGeom_hArm_offdiag (supplied where blockA lands the arm, like the leaf rows).

### GENUINE OBSTRUCTION FOUND + logged (observations `fnArmGeom-hArm-diagonal-phic-only`)
- `fnArmGeom_hArm_of_seam` has ONE closures-map param φc' → only the DIAGONAL
  Triple(EvalEntry@φc' , PreEpilogueV@φc'). FnArmGeom.hArm needs OFF-DIAGONAL
  (EvalEntry@φc , exit@φc'). EvalEntry.store = StoreRepr…φc st.store genuinely depends
  on φc, so not defeq. Gap = a φc-entry rebase StoreRepr…φc→φc' over
  PhiExtends φc φc' st.store.closures.size (old store references no fresh index) — the
  closures analog of the φf-rebase in CallClosureEnvNewMarshal. Named as `hEntryRebase`
  premise; NOT fabricated. Proposal: `storeRepr_phic_mono` OR generalize
  fnArmGeom_hArm_of_seam to two maps.

### REMAINING named premises for a fully CLOSED FnResid (itemized)
1. hSeam : FnArmSeamRun — the EX_FN middle seam; closed by fnArmSeamRun_of_allocClosure
   (FnArmSeamReduce) modulo the AllocClosureContract (off-path arm-head decode + build
   write-log). IRREDUCIBLE machine residual.
2. The 9 jump-table dispatch facts (fn kind 10, arm 0x800033c4) — mechanical leaf clone.
3. hEntryRebase — the φc-entry rebase (the ONE genuine new lemma-gap this wave found).
4. hpc (PhiExtends closure-alloc) + hout (output inv) — from allocClosure.
5. hW : EvalRecWiden at the grown store.
NOTE items b(store-size mono) + the FnArmGeom assembly are now DONE (in FnResidSupply).

## WIRING (report-only, NOT applied — I do not touch Vsa.lean/check_all.sh)
- Vsa.lean: add `import Vsa.Sim.rows.FnResidSupply`
  (after `import Vsa.Sim.rows.FnArmSeamReduce` / `Vsa.Sim.rows.CallRows`).
- scripts/check_all.sh axiom list: add
  `Vsa.Sim.fnArmGeom_hArm_offdiag`, `Vsa.Sim.store_size_of_allocClosure`,
  `Vsa.Sim.fnResid_of_pipeline`.
- The 5 re-emitted Gen files are ALREADY imported (no new wiring); their theorem
  names are unchanged so no check_all axiom-list edit needed.

## FINAL STATUS
- Task A: DONE. genseg.py fixed; 5 affected files re-emitted, green + axiom-clean;
  3 consumers verified green + axiom-clean; ledger entry marked RESOLVED.
- Task B: eval_fn_row (hFn slot) was ALREADY filled+green in CallRows.lean. Delivered
  the FnResid SUPPLIER (FnResidSupply.lean, green + axiom-clean + discipline-clean):
  store-size mono DONE, FnArmGeom assembly DONE, off-diagonal hArm bridge DONE.
  Found + logged the ONE genuine new gap (φc-entry rebase), named as hEntryRebase.
