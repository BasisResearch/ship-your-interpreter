# IrisHoles ledger

Every assumption left in the Iris route is a field of `structure IrisHoles` and has a row here. `scripts/check_iris_holes.py` checks the two agree. A hole is discharged by proving the field and deleting both the field and its row in the same commit.

| field | what it assumes | owner | satisfiability evidence | discharge plan |
|---|---|---|---|---|
| `alloc.mallocRoomRun` | `_malloc_r` top-split fast path meets `MallocRoomEnd` | H4 | `Vsa/ControlEnd.lean` (control heap, hand-computed post-states) | chain `seg_runFact` segments via `segFrom_of_runFact` |
| `alloc.mallocLocalRun` | general `_malloc_r` (bins, sbrk) meets `MallocEnd` | H4 | `ControlWitness` | per-path segment chains |
| `alloc.freeLocalRun` | general `_free_r` (coalescing, bins) meets `FreeEnd` | H4 | top-merge path proved (`FreeRoomRun`) | per-path segment chains |
| `alloc.reallocLocalRun` | `_realloc_r` grow path | H4 | `reallocSpec_of_localRun` consumers | segment chains |
| `newlib.snprintf` | safety of `snprintf` `%s`/`%d` on error paths (partial mode only) | scheduled after E1–E6 (user, Q4) | `%lld` success path proved (M3) | reuse M3 digit loop + format parser segments |
| `newlib.fprintf` | safety of `fprintf` on error/out-of-memory paths (partial mode only) | scheduled after E1–E6 (user, Q4) | — | stdout write path segments |
