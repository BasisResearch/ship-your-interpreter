# iris-heap progress

Branch `iris-heap`, rebased on `iris-machine` (`074583c`, `VsaIris/Vsa/Instance.lean`).

## Done
- **Heap shape** (`VsaIris/Vsa/HeapShape.lean`): `vsaLayout` fixes `DlLayout` for the binary. Globals come from the ELF symbol table, the arena is `[_end, __heap_end)`, and `Shape` is `HeapAt` with exact live blocks (`BlockHeapAt`). `BlockHeapAt.transport` proves that `HeapAt` reads only `vsaFoot H`, the globals plus the arena outside the live extents, which is `heapFoot vsaLayout H`. `blockHeapAt_of_heapAt`/`blockHeap_of_initial` convert VSA's boundary heap (`InitialAllocatorAt`).
- **Control-heap test** (`VsaIris/Vsa/ControlWitness.lean`): at the real `Control.heapMem`, the Iris shape holds. The malloc(32) and malloc(64) post-states on the top-split path both write only `heapFoot vsaLayout controlBlocks` and satisfy the post shape. The 64-byte block contains `0x82000238`, which malloc(32) writes (`live_relative_frame_admits_both`).
- **Spec repair** (`VsaIris/DlHeap.lean`): the old `DlMallocImpl` could not be satisfied by any real allocator. It gave the callee no code and no callee-saved registers, while `_malloc_r` spills `s0`. It now takes `textOwn text` and `savedOwn saved`.
- **Run rule** (`VsaIris/LocalRun.lean`): `wp_localRun` handles a chain of segments over an owned register list and an owned byte set, on the sibling's lagging interpretation. `segFrom_of_runFact` turns VSA `RunFact`s (`seg_runFact`) into segments.
- **DlMallocImpl** (`VsaIris/MallocRun.lean`, `VsaIris/Vsa/Malloc.lean`): `dlMallocImpl_of_localRuns` / `vsaDlMallocImpl` build it from `MallocLocalRun` and `FreeLocalRun`.
- **Consumer adapter** (`VsaIris/Vsa/MallocConsumer.lean`): `wp_call_malloc_owns`, `ownSet_agree_state`, and `mallocCallerFacts_of_iris`. These supply the `MallocBlock`, `HeapOwned`, `StoreRepr` and shared-agreement premises of `prepareCopy`/`envNewAllocator_run`.

## In flight
- Capacity: a credit-indexed success spec, so that `budget`/`reserve` follow too.

## Holes left (named, not proved)
- `MallocLocalRun`, `FreeLocalRun`: the instruction-level runs of `_malloc_r`/`_free_r`, framed by the live extents. They are satisfiable (see the control test); proving them means chaining `segEval` segments through `_malloc_r`.
- The capacity/success premise (`budget`, `reserve`): `mallocPost` allows NULL.

## Next
- Credit-indexed spec; realloc; the `text` list from `Code.FixedTextLoaded`.

## QUESTIONS
- `DlMallocImpl`'s signature changed (code bytes, callee-saved registers). This is a VsaIris-only change, needed for satisfiability. The sibling branch may want to adopt it.
