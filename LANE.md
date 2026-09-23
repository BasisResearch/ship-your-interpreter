# Lane R: representation predicates

Package R of `VsaIris/INTERP_DESIGN.md` §9: `InterpGS` and the §3 predicates.

## Done
- `VsaIris/Interp/Repr.lean`: `InterpGS` (two names over the machine's
  `Nat ↦ Nat` ghost-map functor), `frameAt`/`closAt`, `roImg`/`roOn`,
  `strAt`, `astE`/`astS`/`astSs` (`*ReprWithin` over a read-only view),
  `valOf`/`valAt`/`slot24`, `closOwn`, `FrameGeom`/`FrameLayout`/`frameBody`/
  `frameOwn`, `storeRepr`, `interpCtx`/`interpCtxPre`, `Regime`/`heapRes`,
  `world`.
- `VsaIris/Interp/Store.lean`: the one frame opener `storeRepr_open`
  (+ `storeRepr_open_define`), `storeRepr_frameAt`/`_closAt`/`_closure`,
  `storeRepr_empty`, `storeRepr_allocFrame`, `storeRepr_allocClosure`,
  `ownImg_persist`/`strAt_of_owned` (discard after the write),
  two-owner facts `storeRepr_blocks_disjoint`, `storeRepr_blocks_off_heap`,
  `world_blocks_off_heap`.

## In flight
- Bridge to VSA (`MemRepr`/`ProgramRepr`/`StoreRepr`): `astE_of_exprRepr`,
  `strAt_of_cstring`, `valAt`/`frameBody` from `FrameRepr`.
- Vacuity at the control program (`Vsa/Sim/NativeNameAudit/Control*`).
- Replace `Specs.lean` §C with the landed definitions.

## Holes
None added.
