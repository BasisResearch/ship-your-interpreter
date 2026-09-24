# Lane H4 (continued): the remaining allocator paths

Branch `lane-h4`. Goal: discharge `IrisHoles.alloc` (`VsaIris/Vsa/AllocHoles.lean`,
`VsaIris/HOLES.md`). The previous session's report is `LANES-h4.md`.

## Done
- **`malloc_extend_top`** (`0x80004a48`) is proved and wired into `malloc_paths`
  (`VsaIris/Vsa/MallocExtend.lean`, `extend_top`):
  - `sbrk_r_run` (`Vsa/Sbrk.lean`): the whole `_sbrk_r` → `_sbrk` call as one `AW` step,
    both outcomes, with the call's effects named (`SbrkPre`/`SbrkPost`). `_malloc_trim_r`
    will reuse it.
  - `PHeapAt.topGrow` (`Vsa/HeapGrow.lean`): the in-place top growth at a larger
    page-aligned break.
  - `top_split` (`MallocTop.lean`): the split arm factored out of `top_path`, entered from
    both the top path and the grown top.
  - `ext_setup` / `ext_grow` / `ext_null` / `ext_stats` / `ext_top`: the joins around the
    call, each within the default heartbeat budget.
- **Interface correction** (`PROOF_CLOSURE_PLAN.md`): `MNull.starved` is now
  `Starved top0 n`, the bound a failed `sbrk` actually gives; the counted regime refutes it
  through `physSize_le_chg16`.
- **Symbolic-execution layer** (`AllocTac.lean`): `sx_side` refutes word (dis)equalities by
  `toNat` and owns literal allocator globals (`MOK`) and `_sbrk_r`'s frame (`SbrkPre`);
  `sx_mem` forwards word loads (`ldv_lw_miss`, `ldv_lw_zero_eq`); `sx_addr` accepts goals its
  first `simp` closes; `upd_self_eq` pins a register's known value into the file.
  `MHeap.glob_off`: the stack window misses the allocator globals.

- **The last remainder's split** (`0x80004da0`, `lr_split` in `Vsa/MallocSplit.lean`),
  over the new heap edit `PHeapAt.splitFree` (`Vsa/HeapCarve.lean`): `PHeapAt.take` into a
  virtual intermediate memory, then `PHeapAt.carve` (shrink an in-use chunk, the tail alone
  on bin 1). `lr_split_ret` is the heap half, reusable by the block walk's split.

- **The small re-binning** (`0x8000491c`, `rebin` in `Vsa/MallocRebin.lean`) over the new
  `PHeapAt.moveBinAt` (`Vsa/HeapMoveAt.lean`: a move to any insertion point); it enters
  the block search's test `bb_entry` (factored out of `bb_check`). `t4 = bin 1` is now
  threaded from the last-remainder check to the block walk.

- **The large re-binning** (`0x80004c70`, `rebinL` in `Vsa/MallocRebinL.lean`): the
  `binIndex` cascade (`lbin_idx`), the empty-bin case, and the sorted walk (`rebinL_walk`, an
  induction over the unvisited members), all onto `rebin_link` / `rebin_at_heap`.

- **The large-request scan** (`0x80004884`, `lscan` in `Vsa/MallocLarge.lean`): the cascade
  `lscan_idx`, the backward walk `lscan_walk`, the take `lscan_take`, over the general
  `take_ret` (any bin and position). `from_lr` (`MallocChain.lean`) is the shared tree from
  the last-remainder check on.

- **The block walk** (`0x80004978`, `Vsa/MallocBlocks.lean`, `Vsa/MallocBlocks2.lean`):
  member walk, take, split, bin loop, block clearing (`PHeapAt.clearBlock`,
  `Vsa/HeapClear.lean`), next-block search, and the fold `bw_walk`. `malloc_all` closes
  `_malloc_r`.
- **`malloc` discharged**: `mallocChgRun_proved`, `mallocLocalRun_proved`
  (`Vsa/MallocRunAll.lean`, through `aw_run`, `malloc_ret`, `mOK_loc`); the fields
  `alloc.mallocChgRun` and `alloc.mallocLocalRun` and their HOLES rows are deleted.
  `AllocBase.lean` holds the calling conditions so `AllocHoles.lean` can import the proofs.

- **Interface correction** (`PROOF_CLOSURE_PLAN.md`): `pShape`/`vsaRoomB` carry `Starts H`
  (distinct block starts); without it `alloc.freeLocalRun`/`freeChgRun` were unsatisfiable.
- **`_free_r` in progress**: heap edits `Vsa/HeapFree.lean` (`drop`, `unlink`, `absorb`,
  `toTop`, `release`, `coalNext`, `coalPrev`, and `agree_of_words`/`wl1_congr` for relating
  virtual and machine memories), `PHeapAt.topResize` (trim's shrink), `sbrk_r_gen`, the
  context `Vsa/FreeCtx.lean` (`FOK` over the shared `WOK`), the prologue and epilogue
  (`Vsa/FreePro.lean`), the bin insertion (`Vsa/FreeBin.lean`, `Vsa/FreeLarge.lean`:
  `fb_release`, small bins, the large cascade and sorted walk), and every path below the top
  (`Vsa/FreePaths.lean`, `free_split`: both neighbours in use, forward, backward and double
  coalescing, the last remainder on either side).

- **`free` discharged**: the top merge (`free_top`, `Vsa/FreeTop.lean`), `_malloc_trim_r`
  (`trim_run`, `Vsa/FreeTrim.lean`), the whole body `free_body`, and the runs
  `freeChgRun_proved`/`freeLocalRun_proved` (`Vsa/FreeRunAll.lean`, over the tracking memory
  `ft0` with the block's bytes inserted). The fields `alloc.freeChgRun` and
  `alloc.freeLocalRun` and their HOLES rows are deleted.

## Holes
- None left in `IrisHoles.alloc`: the field is deleted (`VsaIris/Interp/Specs.lean`), and
  `allocSpecs` (`VsaIris/Vsa/AllocHoles.lean`) builds every allocator spec from the six
  proved runs. `check_iris_holes.py`: 4 ledgered holes, all `newlib.*` (H5).

- **`sltu` step** (`Vsa/AllocSltu.lean`): `swp_alu` (any observational ALU step as one `SWP`
  step) and `st_800052d0`.

- **`realloc` discharged**: `reallocChgRun_proved`, `reallocLocalRun_proved`
  (`Vsa/ReallocRunAll.lean`: the wrapper `realloc_entry`, `realloc_body`, the entry heap
  `rHeap_entry` over `ft0`, the contexts `rLocCtx`/`rChgCtx` with `rOK_loc`/`rOK_chg`; the
  counted regime refutes NULL through `Starved`). Axioms: propext, Classical.choice,
  Quot.sound (`HeapAudit.lean`).
- **`_realloc_r` in detail**: interface correction (`ReallocLocalRun` needs `nNew < 2^64`,
  `PROOF_CLOSURE_PLAN.md`); context `ReallocCtx.lean` (`ROK`, `RRet`, `RNull`, `RHeap`, epilogue
  `repi`), prologue and error return (`ReallocPro.lean`), nested calls `rcall_malloc`/`rcall_free`
  (`ReallocCall.lean`), heap edits `PHeapAt.cut`/`reblock`/`growTop`/`setTop`/`fresh_of_block`/
  `addBlock` (`HeapRealloc.lean`), the tail join `realloc_tail` (`ReallocTail.lean`), the dispatch
  `realloc_dec` (`ReallocDec.lean`), word copies `copyW`/`copyW_spec`/`copyW_agreeOn`
  (`ReallocCopy.lean`, `ReallocPrev.lean`), `memmove_fwd` (`ReallocMove.lean`); the malloc path
  `realloc_mal` (`ReallocMal.lean`); `realloc_next` over `next_absorb` (`ReallocNext.lean`);
  `realloc_topgrow` (`ReallocTop.lean`); the predecessor paths `realloc_pvX`, `realloc_pvXN`,
  `realloc_pvT` (`ReallocPrev{,N,T}.lean`, sharing `pvG_rt` over a virtual pre-state `PvIn`);
  the growth dispatch `realloc_grow` (`ReallocGrow.lean`).
- **Strengthened contract** (`PROOF_CLOSURE_PLAN.md`): `MRet`/`MHeap`/`TakeRet` carry
  `LiveKeep` (live blocks' chunks survive `_malloc_r`), which the merge path needs.

## Next
- `AllocSpecs` exposes the uncounted realloc spec only; `reallocChgRun_proved` is ready for a
  counted `DlReallocChgImpl` field when a consumer needs it (`reallocChgSpec_of_run`).
- The three predecessor copies (`pv{A,N,T}_inline`) are one unrolled shape at three code
  addresses, generated here by address substitution; a copy descriptor over step lemmas
  would replace them if a fourth site appears.
