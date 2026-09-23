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
