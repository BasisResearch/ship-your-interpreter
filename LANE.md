# Lane H4: the allocator machine runs

Branch `lane-h4` (pushed to `hub`). Goal: discharge `IrisHoles.alloc` (`VsaIris/HOLES.md`) by proving the
first-order runs of `_malloc_r`, `_free_r` and `_realloc_r` at the binary.

## Done
- Merged iris-heap's later work (29 commits, cherry-picked from `~/Documents/code/vsa-iris-heap`
  `c740152..ebfa279`). `lake build VsaIris` is green (1418 jobs), and the axioms are clean.
  - `MallocRoomRun` on the **fast heap** (`vsaRoomFast`: no free chunk, `binblocks = 0`), requests
    `≤ 487` bytes: `mallocRoomRun_fast` (`Vsa/MallocSmallChain.lean`), and at the boundary
    `vsaDlMallocRoomImpl_boundary` (`Vsa/MallocLive.lean`).
  - `FreeRoomRun` for the top merge (`vsaFreeTop`): `freeRoomRun_fast` (`Vsa/FreeChain.lean`).
  - `reallocSpec`/`ReallocLocalRun`/`DlReallocImpl` statements and consumers (`MallocRun.lean`).

## Findings that shape the remaining work
- **The counted regime needs every allocator path, not only the fast path.**
  - `eval_expr`'s string concat frees both `stringify` buffers (`0x80003abc`, `0x80003ac4`), so
    free chunks enter the bins. Later mallocs reuse them.
  - `InitialAllocatorAt.capacity` bounds `heapEnd - top`, not the top chunk, so allocation must
    grow the top through `sbrk` (`malloc_extend_top`, `0x80004a48…`).
  - `_sbrk` fails only when `brk + incr > __heap_end` (`0x8000012c`). A `heapEnd`-relative credit
    with `extendSlack` therefore guarantees success.
- **Credits are bytes, not requests.** The skeleton's `.counted (k + n)` spends cost units, and
  `Vsa/While/Cost.lean` counts rounded bytes. `physSize n ≤ 2 * charge`, which covers both halves
  of the array realloc (see Next, item 1).
- `vsaRoom`/`TopReserve` measure the top chunk (`brkv - top`), not the boundary's `heapEnd - top`.
  They cannot be established from the boundary for programs whose allocations exceed the initial
  top chunk.

## In flight
- A symbolic-execution layer for machine runs, to replace ~100-line hand stages:
  - `SWP pc R Mt`: a weakest precondition over `LocalRun`, with register file `R` and tracking
    memory `Mt`.
  - Generated per-instruction step lemmas for all allocator code (`scripts/gen_alloc_steps.py`).
  - A driver tactic.

## Holes (unchanged; see `VsaIris/HOLES.md`)
- `alloc.mallocRoomRun`, `alloc.mallocLocalRun`, `alloc.freeLocalRun`, `alloc.reallocLocalRun`.

## Next
1. The byte-credit, `heapEnd`-relative `Room` (`vsaRoomGen`), and a malloc spec charging `c` with
   `physSize n ≤ 2c`.
2. The SWP layer and step table; re-prove the fast path on it as the calibration.
3. The heap algebra on `HeapAt`: unlink, frontlink (small and large bins), split with the
   last-remainder bin, coalescing, `binblocks`, top extension, trim.
4. The paths, in order: malloc (bins, last remainder, `binblocks` scan, `sbrk`), free
   (coalescing, bins, trim), realloc (grow).
5. Regime lemmas and the `xmalloc` site lemma. Make the runs WP-agnostic once `hub/lane-f1` has
   `MachWP`.
