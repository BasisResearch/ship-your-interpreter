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

## SLOW (per-module build time > 180 s)

- `Vsa.Sim.SnprintfSpec20` — 210 s (pass 2)
