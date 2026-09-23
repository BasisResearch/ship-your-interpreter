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
- `VsaIris/Interp/Bridge.lean`: VSA → Iris. `memImg` + the `readLE`/`imgLE`
  calculus (`readLE_memImg`, `imgLE_split`, `imgW_lo32`, `imgW_read64`);
  `roOn_of_roImg`/`roOn_of_ownImg`/`roImg_of_roOn`; `strAt_of_cstringWithin`
  (with `cstr_bytes`/`cstrImg_of_cstring`); `astE_of_exprRepr`,
  `astS_of_stmtRepr`, `astSs_of_stmtArrayRepr`, `astSs_of_programRepr`
  (what `InterpRunReadyFacts.ast_owned` hands A0); `PayloadShared`/
  `closSupply`, `valOf_of_valueRepr`, `valAt_of_valueWordRepr`; `FrameReads`
  (one named destructurer for VSA's `FrameRepr` tower), `FrameBridge` (named
  per-frame boundary data), `frameLayout_of_frameRepr`,
  `bindings_of_frameRepr`, `frameBody_of_frameRepr`.
- `VsaIris/Interp/Boundary.lean`: `extAddrs`/`blockAddrs`, `imgMap`,
  `memAgree_imgMap`, `sepL_of_memMap`, `ownImg_of_memMap`, `roOn_of_memMap` —
  adequacy's `[∗map] k ↦ v ∈ mm, k ↦ₘ v` becomes `ownImg`/`roOn`.

## In flight
- Vacuity at the control program (`Vsa/Sim/NativeNameAudit/Control*`):
  instantiate every §3 predicate at `heapMem`/`initSt` and show inhabited.
- Replace `Specs.lean` §C with the landed definitions.

## Holes
None added. `python3 scripts/check_iris_holes.py` passes.

## Next
Vacuity, then `Specs.lean` §C.
