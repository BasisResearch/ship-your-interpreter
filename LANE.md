# Lane A0: the boundary world — PAUSED (moving to aws-dev), WIP

Package A0 of `VsaIris/INTERP_DESIGN.md` §5.1/§9. All work is in
`VsaIris/Interp/World.lean`. That file is NOT yet imported from `VsaIris.lean`,
so `lake build Vsa VsaIris` is unaffected. No holes added: `check_iris_holes.py` passes.

## Done (elaborates, axioms ⊆ {propext, Classical.choice, Quot.sound})
§1–§8 of World.lean, up to and including `closSupply_frame0` / `freeStack_disj` / `interp_disj`:
- `fillMem`, `MemGrows`, `HeapAt.grow` (+ `ChunkWalk.grow`, `BinChain.grow`): the boundary
  does not assert that every arena byte is present, so the heap image `memImg m` is read at the
  filled memory. `imgShape_of_blockHeapAt`, `costRoom_of_reserve`.
- `Boot c p`: every witness of `Loaded interpRunLayout` named (`boot_of_loaded`); `Boot.fits`
  (S1 stack admissibility), `frameRepr`, `frameOwned`, `env_ne`, `H := inuseBlocks chunks`.
- `FrameChunks` + `BootGap` (the named premise, see Findings). `inuseBlocks_disj`,
  `FrameChunks.disjoint`, `payloadShared_of_valueOwned`, `Boot.frameBridge`.
- The byte partition `BootByte = RoByte ∨ store blocks ∨ heapFoot ∨ StackByte ∨ StaticByte`
  (stack further = `FreeStackByte ∨ InterpByte ∨ CallerByte`), all pairwise-disjointness
  lemmas (`ro_disj`, `store_disj`, `heap_disj`, `stack_disj`, `stack_parts`, `bootByte_lt`).
- `bootAddrs`/`Boot.bytes` (the `mm` for adequacy) and `Boot.bytes_agree` (MemAgree).
- `RegimeOK`, `Boot.regime_of_bigStep` (counted regime from BigStep via S1's cost),
  `heapRes_of_bytes` (both regimes), `freeStack_carve`, `interpCtxPre_of_bytes`, `ownImg_ext_split`.

## In flight (exact resume point)
§9 `boot_of_bytes` and `world_of_boundary`, plus `worldPre`/`bootRes` defs (these defs elaborate).
- Up to the `ihave #Hsh := roOn_mono (Q := …) (P := …) …` line, the proof steps check
  (tested by truncating before `world_of_boundary`: 2s).
- With the explicit `roOn_mono` arguments, the FULL file now runs past 5 min. It is not yet
  known whether the hang is in the rest of `boot_of_bytes` (storeRepr_empty /
  frameBody_of_frameRepr / storeRepr_allocFrame with `(by rfl)` / heapRes / astSs steps) or
  in `world_of_boundary` (`iapply (boot_of_bytes (I := ⟨γf, γc⟩) …)`: the unification of
  `I.frameName` with `γf` may be the culprit). Bisect by truncating with a python script
  into the scratchpad, as done so far. Do NOT raise heartbeats (Law 1).
- Lesson: IntoWand does not unfold defs. Give `ownSet_unglue`/`ownSet_iff`/`roOn_mono`
  explicit set arguments whose syntactic form matches the hypothesis. `set_option
  autoImplicit false` is on in the file. (Earlier hang: `output` was auto-bound.)

## Next
1. Finish §9, then add `VsaIris/Interp/WorldVacuity.lean`: `Boot` at `Control.loaded`
   (`Vsa/Sim/NativeNameAudit/ControlLoaded`), `BootGap` at the control: blocks
   (0x81000000,0x38), (0x81000040,0x48), (0x81000100,0xc8) are in-use payloads of
   `heapChunks`; top_room from heapTop/heapBrk. Then `world_of_boundary` inhabited in both
   regimes (counted via `Control.costReserve`).
2. Add a `textOwn_of_roOn` projection (mentioned in the `bootRes` doc).
3. Import World (+ Vacuity) from `VsaIris.lean`, add `#print axioms` to `Audit.lean`, full build
   under the lock, record in INTERP_DESIGN.md §5.1 and PROOF_CLOSURE_PLAN.md (the gap below).
4. Ask the user: add `BootGap` as an `InterpRunReadyFacts` field (like S1's
   `stack_admissible`), or relax §3's `world` (store blocks ⊆ heap blocks instead of ∈)?

## Findings
- **Boundary gap (`BootGap`).** `InitialOwned` puts each live extent inside SOME in-use chunk
  (`HeapAt.live`), but not alone: the global frame's `Env` struct may share a chunk with a
  binding name, and arrays may share their chunk's tail. §3's `world` needs the store's blocks
  to be members of the heap's live-block list (whole payloads, user ruling), exclusively
  owned, so it needs the three chunks distinct and holding no shared byte. Also `BlockHeapAt`'s
  `top_room` (top + 16 ≤ brk) is not stated by `HeapAt`. Both carried as the named premise
  `BootGap` of `world_of_boundary`; true at the control. Not yet recorded in
  PROOF_CLOSURE_PLAN.md (do it at step 3).

## Holes
None added.
