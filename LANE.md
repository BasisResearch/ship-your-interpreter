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

## In flight
- The two residual malloc joins (`malloc_paths`' hypotheses): the large-bin scan
  (`0x80004884`) and the block walk (`0x80004978`).

## Holes
- Unchanged: `alloc.mallocChgRun`, `alloc.mallocLocalRun`, `alloc.freeChgRun`,
  `alloc.freeLocalRun`, `alloc.reallocChgRun`, `alloc.reallocLocalRun`.

## Next
1. The block walk's split (`0x80004d14`) reuses `PHeapAt.splitFree` with `i` the victim's
   bin; its exact fit (`0x800049e8`) is `PHeapAt.take`.
2. The re-binding and `_free_r`'s frontlink share a sorted insert into a large bin; generalize
   `PHeapAt.moveBin` to an insertion point.
3. The large-bin scan and the block walk are loops: inductions over the bin list with `AW` as
   the motive.
4. Then `_free_r`, `_malloc_trim_r` (over `sbrk_r_run`), `_realloc_r`.
