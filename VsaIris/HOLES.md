# IrisHoles ledger

Every assumption left in the Iris route is a field of `structure IrisHoles` and has a row here. `scripts/check_iris_holes.py` checks the two agree. A hole is discharged by proving the field and deleting both the field and its row in the same commit.

| field | what it assumes | owner | satisfiability evidence | discharge plan |
|---|---|---|---|---|
| `alloc.mallocChgRun` | counted `_malloc_r` (every path, `sbrk` growth included) meets `MallocRoomEnd` over `vsaRoomB`/`vsaChg` | H4 | top split proved on the fast heap (`mallocRoomRun_fast`); `ControlEnd` | `SWP` step table (`AllocSteps`, `sx_run`) + `HeapAt` algebra per path |
| `alloc.mallocLocalRun` | uncounted `_malloc_r` meets `MallocEnd` (NULL or fresh block) | H4 | `ControlWitness` | same paths as `mallocChgRun`, plus the `sbrk` failure arm |
| `alloc.freeChgRun` | counted `_free_r` (coalescing, bins, trim) keeps `vsaRoomB` | H4 | top merge proved (`freeRoomRun_fast`) | `SWP` paths: top merge, backward/forward coalescing, small/large `frontlink`, `_malloc_trim_r` |
| `alloc.freeLocalRun` | uncounted `_free_r` meets `FreeEnd` | H4 | as `freeChgRun` | shares `freeChgRun`'s paths |
| `alloc.reallocChgRun` | counted `_realloc_r` grow path meets `ReallocChgEnd` (never NULL) | H4 | `reallocChgSpec_of_run` consumers | `SWP` paths: in place (top, free next), malloc-copy-free; `sltu` at `0x800052d0` needs a hand step lemma |
| `alloc.reallocLocalRun` | uncounted `_realloc_r` grow path meets `ReallocEnd` | H4 | `reallocSpec_of_localRun` consumers | as `reallocChgRun`, plus the NULL arm |
| `newlib.snprintf` | safety of `snprintf` `%s`/`%d` on error paths (partial mode only) | scheduled after E1–E6 (user, Q4) | `%lld` success path proved (M3) | reuse M3 digit loop + format parser segments |
| `newlib.fprintf` | safety of `fprintf` on error/out-of-memory paths (partial mode only) | scheduled after E1–E6 (user, Q4) | — | stdout write path segments |
