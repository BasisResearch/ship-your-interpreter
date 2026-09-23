# Lane H4: the allocator machine runs

Branch `lane-h4` (pushed to `hub`). Goal: discharge `IrisHoles.alloc` (`VsaIris/HOLES.md`) by proving the
first-order runs of `_malloc_r`, `_free_r` and `_realloc_r` at the binary.

## Done
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
- **Every path is needed in the counted regime.** String concat frees its `stringify` buffers, so
  bins fill. The boundary's capacity is `heapEnd`-relative, so the top grows by `sbrk`.
- `sltu` at `0x800052d0` (`_realloc_r`) is outside `MKind` and needs a hand step lemma
  (`stepObs_alu` + `execute_rtype_sltu_char`). `sltiu` at `0x80006bd8` is in `memcpy`, which the
  allocator does not call.

## In flight
- `_malloc_r` paths (`Vsa/MallocPaths.lean`), on the step table and the heap algebra:
  - done: entry/exit adapters (`mallocChgRun_of_aw`, `malloc_exit`), the epilogue copies
    (`epi_core`), the small-bin join `j_small`, and the exact small-bin take `small_take`
    (unlink, `PREV_INUSE`, return), via `PHeapAt.take`/`take_fresh` (`Vsa/HeapTake.lean`);
  - next: the prologue to `j_small`, the last-remainder check (`0x800048ec`), the binblocks
    scan, the top split and `malloc_extend_top`, large bins.

## Holes (see `VsaIris/HOLES.md`)
- `alloc.mallocChgRun`, `alloc.mallocLocalRun`, `alloc.freeChgRun`, `alloc.freeLocalRun`,
  `alloc.reallocChgRun`, `alloc.reallocLocalRun`.

## Next
1. The remaining malloc joins (see In flight).
2. Heap algebra on `PHeapAt`: unlink, small and large `frontlink`, split with the last-remainder
   bin, `binblocks`, top split and extension, coalescing, trim.
3. Malloc paths, then free, then realloc (with the `sltu` step). Delete each field and its row
   as it is proved.
4. The `xmalloc` site lemma.
