# Lane R: representation predicates — INTERFACE STABLE

Package R of `VsaIris/INTERP_DESIGN.md` §9: `InterpGS` and the §3 predicates.
Everything below is in `lake build Vsa VsaIris` (green), axioms of every new
theorem ⊆ {propext, Classical.choice, Quot.sound}. Merged `hub/iris-main`
(F1/F2/S1/F3). **Wave 3 can build on these names now.**

## The interface wave 3 uses

`VsaIris/Interp/Repr.lean` — the predicates
- `InterpGS GF` (two ghost-map names over the machine's `Nat ↦ Nat` functor;
  no second `GhostMapG` instance is in scope), `frameAt fa e` / `closAt ca p`
  (persistent, `_agree` lemmas).
- Bytes: `ownImg S img` (= `ownSet S (fun a => a ↦ₘ img a)`), `roImg S img`,
  `roOn P m` (read-only VIEW of a memory), `imgLE`/`imgW` (total reads).
- Persistent data: `strAt p s` (`CStrImg`), `astE`/`astS`/`astSs` (VSA's
  `*ReprWithin` over a `roOn` view), `closOwn ca cd`.
- Values: `valOf N v w0 w1 w2`, `valImg N img a v`, `valAt N a v`, `slot24 a`.
- Frames: `FrameGeom` (e, cap, pn, pv, par, sblk, nblk, vblk),
  `FrameGeom.blocks`, `BlocksCover`, `ExtDisj`, `FrameLayout`, `bindings`,
  `parentAt`, `frameBody N f G`, `frameOwn N fa f bl`, `framesOwn`,
  `closuresOwn`.
- Store/world: `StoreMaps`, `storeRepr N s B`, `interpCore`/`interpCtx`/
  `interpCtxPre` (offsets `interpDepthOff`/`interpJmpOff`/`interpJmpLen`/
  `interpErrOff`/`interpErrLen`), `wordAt`/`wordRO`, `Regime`, `heapRes`,
  `world N L Room inp ρ st d`.

`VsaIris/Interp/Store.lean` — H1's openers
- `storeRepr_open` (the ONE frame opener: frame `fa` with its blocks out, a
  closer that puts ANY frame back) and `storeRepr_open_define` (closer
  specialized to `Store.define`'s update).
- `storeRepr_frameAt` / `_closAt` / `_closure` (lookups without opening),
  `storeRepr_empty`, `storeRepr_allocFrame` (`env_new`),
  `storeRepr_allocClosure` (`EX_FN`).
- `ownImg_persist` / `strAt_of_owned` — the discard, to be used AFTER the last
  write (design §10.6). `roImg_ownImg_off`, `memRO_excl_ne`.
- Two-owner facts: `storeRepr_blocks_disjoint`, `storeRepr_blocks_off_heap`,
  `world_blocks_off_heap`.

`VsaIris/Interp/Bridge.lean` — VSA's pure relations → these predicates
- `memImg m` and its read calculus: `readLE_succ`, `readLE_mapped`,
  `readLE_memImg`, `readLE_lt`, `imgLE_split`, `imgW_lo32`, `imgW_read64`.
- `roOn_of_roImg`, `roOn_of_ownImg` (discard), `roImg_of_roOn` (window).
- `strAt_of_cstringWithin` (via `cstr_bytes`, `cstrImg_of_cstring`).
- `astE_of_exprRepr`, `astS_of_stmtRepr`, `astSs_of_stmtArrayRepr`,
  `astSs_of_programRepr` ← `InterpRunReadyFacts.ast_owned`.
- `payloadStr`, `PayloadShared`, `closSupply`/`closSupply_of_ne`,
  `valOf_of_valueRepr`, `valImg_congr`, `valAt_of_valueWordRepr`.
- `wordAt_of_ownImg`, `wordRO_of_ownImg`, `blockOwn_of_ownImg`.
- `FrameReads` (+ `.of_frameRepr`): ONE named destructurer for VSA's
  `FrameRepr` conjunction. `FrameBridge` (named per-frame boundary data),
  `frameLayout_of_frameRepr`, `bindings_of_frameRepr`,
  `frameBody_of_frameRepr`, `sepL_zipIdx_of_persistent`.

`VsaIris/Interp/Boundary.lean` — A0's carving
- `extAddrs`/`blockAddrs` (+ nodup from pairwise-disjoint blocks), `imgMap`,
  `imgMap_get?`, `memAgree_imgMap`, `sepL_of_memMap`, `ownImg_of_memMap`,
  `roOn_of_memMap`. Adequacy's `[∗map] k ↦ v ∈ mm, k ↦ₘ v` becomes the
  exclusive and read-only byte resources.

`VsaIris/Interp/Vacuity.lean` — the vacuity check
- Every predicate instantiated at the control program's real initial memory
  (`Vsa/Sim/NativeNameAudit/Control*`): `ctl_frameBridge`, `ctl_frameBody`,
  `ctl_storeRepr`, `ctl_astSs`/`ctl_astS`, `ctl_strAt_*`, `ctl_valAt`,
  `ctl_interpCtxPre`, and `ctl_predicates_inhabited` — all of it out of ONE
  boundary resource plus two freshly allocated ghost maps.

`VsaIris/Interp/Specs.lean` — §C now points at the above; the file elaborates
with no errors (the three stuck-instance errors F3 reported were `GF` not
being determined in `evalSpecT`/`execSpecT`/`specsP`). Statement changes are
recorded in `INTERP_DESIGN.md` §10.

## Holes
None added. `python3 scripts/check_iris_holes.py` passes (6 ledgered holes,
all pre-existing, none R's).

## Not in R
`heapRes`/`world` inhabitation at the control memory needs `isHeap` for the
interpreter control's dlmalloc heap — H4/A0, not R.
