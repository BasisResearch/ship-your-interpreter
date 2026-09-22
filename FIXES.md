# Lean 4.34 port fixes (MBP overnight)

Prior fixes: ~/vsa-iris-spike-logs/prior-fixes.patch

## Fixed

- `Vsa/Sim/RamReadVirtual.lean` — simp unfolding (`EStateM.pure`/`EStateM.bind` no longer
  collapse `pure () >>= k` in a Sail `do` block, so the misalignment `ite_self` stopped firing
  and `rw [hsplit]` lost its pattern): added the local `rfl` lemma `pure_unit_bindCont` and one
  simp argument.
- `Vsa/Sim/EnvSetScanStart.lean` — `simp` no longer evaluates `sign_extend` on literals:
  added `hz : sign_extend (m := 64) 0x000#12 = 0#64` (`BitVec.eq_of_toNat_eq`/`decide`,
  the `EnvSetReturn.lean` idiom) to the `simpa` for `hx8_4`.
- `Vsa/Sim/CallEntry.lean` — `simp` no longer evaluates `sign_extend` on literals: added
  `hpcv : 2147496408#64 + sign_extend 124#13 = 2147496532#64` to the `evalArgsNil` PC `simpa`.
- `Vsa/Sim/SeqClosureRetResume.lean` — `simp` no longer evaluates `sign_extend` on literals:
  added the `jalr` target equation `BitVec.update (0x80003378#64 + sign_extend 0#12) 0 0#1 =
  0x80003378#64` to the `SeqClosureRetCarrier.exit` PC `simpa`.
- `Vsa/Sim/SegEval.lean` — `simp only [writeLog]` no longer reduces the resulting
  `List.foldl applyW m []`: added `List.foldl_nil` to the `writeLog_evalBlocks_init` `simpa only`.
- `Vsa/Sim/DeriveMeta.lean`, `Vsa/Sim/RepackTac.lean` — numeral elaboration: `let mut n := 0`
  now takes its type from the later `m!"{n}"` interpolation (`OfNat MessageData 0`); annotated
  the four counters `: Nat`.
- `Vsa/Sim/EnvSetReturn.lean` — `simp` no longer ground-reduces `mkLine`/`evalBlock`: routed the
  memory goal through `writeLog_evalBlocks_init` and added `+ground` to the closing `simp`.
- `Vsa/Sim/rows/ArgsReturnCopy.lean` — `simp` no longer ground-reduces `evalBlocksPC`: replaced
  both `simpa using hpc'` with the repo's `chainEndPC_eq_bt … (by decide); rfl` idiom
  (as in `CmpDispatchSeg.lean`).
- `Vsa/Sim/MemcpyCopyByte.lean` — `simp` no longer ground-reduces `evalBlocksPC`: added the local
  `byteSegPC` end-PC lemma (`chainEndPC_eq_bt`) and used it in both loop-branch `simpa`s.
- `Vsa/Sim/StrlenHeadRun.lean` — `simp` no longer unfolds `gprGet` at a literal index (and the
  `RegisterType x14` index blocks the plain ascription): added `gprGet` to the `a4` `simpa`.
- `Vsa/Sim/WhileGeomSuppliers.lean` — `sign_extend` on literals: added the `jalr` target equation
  `BitVec.update (0x800042d0#64 + sign_extend 0#12) 0 0#1 = 0x800042d0#64`.
- `Vsa/Sim/rows/EnvDefineEpilogueCore.lean` — `simp only` no longer normalises `n + 0` here:
  added `Nat.add_zero` to the `off := 0` `LPins8` `simpa only`.
- `Vsa/Sim/ExecRetEpilogue.lean` — `simp` no longer ground-reduces `mkLine`/`evalBlock`: added
  `+ground` and `evalBlock`/`wlogM` to the memory-frame `simpa`.
- `Vsa/Sim/rows/EnvDefineScanRows.lean` — `simp` no longer ground-reduces `mkLine`/`evalBlock`:
  added `+ground` and `evalBlock`/`wlogM` to the three segment-memory `simpa`s.
- `Vsa/Sim/DriveToLoopHeadSpans.lean` — four sites: two `evalBlocksPC` end-PCs rerouted through
  `chainEndPC_eq_bt … (by decide); rfl`, one `output` unfolding added to a `simpa`, one
  `BitVec.addInt pc 4` literal supplied by `decide`.
- `Vsa/Sim/rows/Field_hInitSome.lean` — six sites: `+ground`/`SegEvalState.init`/`wlogM` for three
  segment-memory `simpa only`s, `gprGet` for two register readbacks, and the `chainEndPC_eq_bt`
  idiom for the body end PC.
- `Vsa/Sim/BinarySecondData.lean` — `simp only` no longer reduces the reflected load list: added
  `stepLdsM`/`stepMemM`/`List.tail_cons`/`List.headD_cons` and `+ground`.
- `Vsa/Sim/MemcpyCopyTail.lean`, `Vsa/Sim/MemcpyCopyEntry.lean`, `Vsa/Sim/MemcpyCopyWord.lean` —
  `simp` no longer ground-reduces `evalBlocksPC`: added local end-PC lemmas
  (`tailSegPC`/`entrySegPC`/`wordSegPC`, all via `chainEndPC_eq_bt`) to the branch `simpa`s.

### Pass 4 (same four 4.34 categories, 17 further modules)

`StrlenCompleteRun`, `EnvGetReflected/EnvGetCountHead`, `EnvGetReflected/EnvGetScanAdvance`,
`InitialNullRun`, `SeqClosureNormalExitResume`, `rows/EnvDefineEpilogue`, `StoreSetFootprint`,
`WhileBodyDispatch`, `rows/Field_hSForStartClosed`, `rows/EnvDefineScanLoop`,
`rows/BlockArmEnvNew`, `rows/CallClosureSplice`, `EnvNewSuccessSuffix`, and the three
`MemcpyCopy` rows. Fixes are the same shapes as above: `+ground` plus `evalBlock`/`wlogM` for
reflected-segment memory, local `chainEndPC_eq_bt` end-PC lemmas, `gprGet`/`gprReg`/`guardB`/
`StatusCode`/`ExecSeqCopy.Loaded`/`Store.allocFrame` unfoldings, explicit `sign_extend` literal
equations, and `+unfoldPartialApp` where a predicate argument had to be unfolded.

### Pass 5 (30 errors, 9 modules — same categories)

`rows/EnvDefineUpdateExact`, `EnvSetHitReconstruct`, `rows/EnvDefineScanFramed`,
`SeqClosureNormalContinue`, `rows/EnvDefineAppendExact`, `WhileCondPrefix`, `CallArgsSetup`,
`EnvGetReflected/EnvGetFrameParent`, `CallArgReturnFacts`.

### Pass 6 (9 errors, 5 modules — same categories)

`rows/EnvDefineAppendPrefix`, `rows/EnvDefineGrowExact`, `rows/EnvDefineTailFramed`,
`EvalValueReturnTail`, `CallArgumentValues` (the last also needed `List.getElem_cons_succ`,
which `simp only` no longer supplied).

### Pass 7 (3 errors, 1 module)

`rows/EnvDefineDispatchExact` — reflected-segment memory, `+ground` recipe.

### Pass 8 (9 errors, 2 modules)

`rows/EnvDefineAppendClosed` (reflected load lists, `bytesVal`, `Alloc.ExtDisjoint`),
`rows/EnvDefineContractUpdate` (`+unfoldPartialApp` for `SetOutside`).

### Pass 9 (6 errors, 1 module)

`rows/EnvDefineCallRuns` — `+ground` for the reflected store/load addresses and `bytesVal`.

### Pass 10 (11 errors, 3 modules)

`MemcpyCopyBulk` (local `bulkSegPC`), `rows/EnvDefineEmptyLane` (`+ground` recipes, `bytesVal`),
`EnvDefineMissAppend` (`BitVec.setWidth_eq` after `BitVec.ofNat_toNat`).

## SLOW (per-module build time > 180 s)

- `Vsa.Sim.SnprintfSpec20` — 210 s (pass 2)
