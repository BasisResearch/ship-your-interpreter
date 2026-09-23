# iris-heap progress

## Done
- `VsaIris/Vsa/HeapShape.lean`: `vsaLayout` instantiates `DlLayout` (globals from the ELF symbol table, arena `[_end, __heap_end)`, `Shape` = `HeapAt` with exact live blocks). `BlockHeapAt.transport`: `HeapAt` reads only `vsaFoot H` (globals ∪ arena minus live extents). `blockHeapAt_of_heapAt` / `blockHeap_of_initial` convert VSA's boundary heap.
- `VsaIris/Vsa/ControlWitness.lean`: at the real control heap, the Iris shape holds; malloc(32)/malloc(64) post-states (top-split path) both stay inside `heapFoot vsaLayout controlBlocks` and satisfy the post shape.

## In flight
- Generic `wp_localRun` (per-step framed run → WP) and `DlMallocImpl` from first-order runs.

## Holes left
- (to fill in)

## Next
- Adapter to one VSA consumer; instantiate with sibling's `VsaIris/Vsa/Instance.lean` once it lands.

## QUESTIONS
- (to fill in)
