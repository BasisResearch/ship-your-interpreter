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

---

# Lane H4: the allocator machine runs

Branch `lane-h4` (pushed to `hub`). Goal: discharge `IrisHoles.alloc` (`VsaIris/HOLES.md`) by proving the
first-order runs of `_malloc_r`, `_free_r` and `_realloc_r` at the binary.

## Done
- **Merged `hub/iris-main`** (F1's `MachWP`, F2's console, S1's Room/Cost bridge): both `jal`-site
  generators now supply `StepConFrame`, `segFrom_of_runFact` passes the output component through,
  and `mallocCostSpec` takes a `MachWP`.
- **Merged iris-heap's later work** (29 commits cherry-picked from `~/Documents/code/vsa-iris-heap`):
  - fast-heap `MallocRoomRun` (`mallocRoomRun_fast`);
  - the top-merge `FreeRoomRun` (`freeRoomRun_fast`);
  - the realloc specs.
- **`IrisHoles.alloc` is now an exact statement**: `VsaHeap.AllocHoles` (`Vsa/AllocHoles.lean`).
  - Six runs at the binary: counted and uncounted malloc, free and realloc.
  - `allocSpecs` turns them into the Iris specs (`DlMallocChgImpl`, `DlMallocImpl`, `DlFreeRoomImpl`,
    `DlReallocImpl`).
  - `HOLES.md` rows match the fields; the `Specs.lean` skeleton points at it.
- **Counted regime** (`MallocChg.lean`, `Vsa/HeapRoom.lean`):
  - `mallocChgSpec`/`reallocChgSpec` charge `c` credits for a request (`vsaChg`: `roundUp16 n ≤ c`,
    the cost model's unit). `isHeapRoom_mono` is the credit-monotonicity lemma.
  - `vsaRoomB`: `2k + extendSlack ≤ heapEnd - top`, exactly `InitialAllocatorAt.capacity` with the
    derivation's cost as credits (`roomB_of_initial`).
- **Spec repairs** (every consumer updated):
  - `mallocSpec`, `freeSpec`, `reallocSpec`, `DlMallocImpl` and the three `*LocalRun`s take the
    caller's stack discipline `SpOK`. Without it they are unsatisfiable: the prologue's frame stores
    fault for a bad `sp`.
  - The Iris shape `vsaLayoutP` requires a page-aligned break (see Findings).
- **WP-agnostic specs**: merged `hub/lane-f1`'s `MachWP`. Every allocator spec takes a
  `Wp : MachWP M` (`fnSpecW`), the `Impl` structures quantify over it, and the `*_of_run`
  lemmas hold for every `Wp` (`wp_localRunW`); the runs themselves are first-order.
- **Heap algebra** (`Vsa/HeapAlg.lean`, `Vsa/HeapTake.lean`): bins as rings of fd/bk links,
  walk rewriting under `reflag`, and the take of a free chunk from a bin (`PHeapAt.take`).
- **Symbolic-execution layer** (the exponentiating layer for machine code):
  - `SWP pc R Mt` (`Vsa/SymRun.lean`): a WP over `LocalRun`, with `swp_step`, `swp_jal` and store
    forwarding (`ldv_store_hit`/`_miss`).
  - `scripts/gen_alloc_steps.py` generates `AllocCode.lean` (the allocator's 5748 code bytes) and
    `AllocSteps/Part00-11.lean`: one lemma `st_<pc>` per instruction, 1433 in all, about 25 s to
    build. Axioms: `propext`, `Classical.choice`, `Quot.sound`.
  - `sx_run` (`AllocTac.lean`) drives the table from an `AW … pc R Mt` goal and prunes refuted
    branches.
  - The step table depends only on the machine layer (`RunBase`), not on the spec modules.

## Findings
- **Page-aligned break needed** (`PROOF_CLOSURE_PLAN.md` §2, INTERP_DESIGN Q5).
  - `malloc_extend_top` returns NULL or fenceposts the old top when the heap end is not
    page-aligned (`0x80004f70`, `0x80004f94`).
  - `InitialAllocatorAt` does not exclude this, so A0 needs the fact at the boundary.
- **A 32-bit `binblocks` word is needed** (INTERP_DESIGN Q5b, `PROOF_CLOSURE_PLAN.md` §2).
  `_malloc_r`'s block search shifts a mask to the next set bit of `binblocks` and steps the bin
  index by four; `HeapAt.binblocks` bounds only the bits of nonempty blocks, and dlmalloc clears
  the bitmap lazily, so a bit at 32 or above walks past bin 127. `PHeapAt.bb_lt` carries the
  bound; `roomB_of_initial` takes it at the boundary.
- **Every path is needed in the counted regime.** String concat frees its `stringify` buffers, so
  bins fill. The boundary's capacity is `heapEnd`-relative, so the top grows by `sbrk`.
- `sltu` at `0x800052d0` (`_realloc_r`) is outside `MKind` and needs a hand step lemma
  (`stepObs_alu` + `execute_rtype_sltu_char`). `sltiu` at `0x80006bd8` is in `memcpy`, which the
  allocator does not call.

## In flight
- `_malloc_r` paths, on the step table and the heap algebra. `Vsa/MallocChain.lean`
  (`malloc_paths`) chains everything proved so far from the entry `0x800047a8`, and its five
  hypotheses are exactly the joins left:

  | PC | what runs there |
  |---|---|
  | `0x80004884` | the large-bin index and scan |
  | `0x80004da0` | splitting the last remainder |
  | `0x8000491c` | putting a too-small remainder back on its own bin |
  | `0x80004978` | the block walk over `binblocks` |
  | `0x80004a48` | `malloc_extend_top` |

  Proved: `malloc_pro` + `malloc_errno` (prologue, `request2size`, the ENOMEM return),
  `j_small` + `small_take` (small bins, over `PHeapAt.take`), `lr_check`/`lr_take`/`lr_last`
  (the last-remainder check and its exact-fit return), `bb_check`/`bb_top` (the block search's
  entry) and `top_path` (the top split, over the new `PHeapAt.topSplit` in `Vsa/HeapSplit.lean`).
- **The take return is factored** (CLAUDE.md law 3): `TakeRet C Mt v` names what a path that
  hands out a block owes the caller (fresh, aligned, heap with the block live, footprint present,
  window framed) and `MOK.fin_take` ends the epilogue at `a0 = v + 16`. `small_take`, `lr_take`
  and `top_path`'s split arm all produce one `TakeRet`; the large-bin take (`0x800049e8`) and the
  last-remainder split should too. The instruction tail itself (`sd a5,8(sp)` / `jal
  __malloc_unlock` / `ld a5,8(sp)` / `addi a0,a5,16`) is one `sx_run` line per copy.

## Holes (see `VsaIris/HOLES.md`)
- `alloc.mallocChgRun`, `alloc.mallocLocalRun`, `alloc.freeChgRun`, `alloc.freeLocalRun`,
  `alloc.reallocChgRun`, `alloc.reallocLocalRun`.

## Next
1. The five residual malloc joins (the table above). `0x80004a48` (`malloc_extend_top`) is the
   one the counted regime needs most, since the boundary's capacity is `heapEnd`-relative;
   `PHeapAt.topSplit` already takes its post-state reads abstractly, so the in-place growth can
   reuse it.
2. Heap algebra on `PHeapAt`: the three edits `take`, `topSplit` and `moveBin` are proved
   (`Vsa/HeapTake.lean`, `Vsa/HeapSplit.lean`, `Vsa/HeapMove.lean`). Still to build: the
   last-remainder split (`0x80004da0`, a chunk split in the middle of the walk), the large-bin
   sorted `frontlink`, top extension, coalescing and trim.
3. Then free, then realloc (with the `sltu` step). Delete each `IrisHoles` field and its
   HOLES.md row as it is proved.
4. The `xmalloc` site lemma.
