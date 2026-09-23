# IrisHoles ledger

Every assumption left in the Iris route is a field of `structure IrisHoles` and has a row here. `scripts/check_iris_holes.py` checks the two agree. A hole is discharged by proving the field and deleting both the field and its row in the same commit.

| field | what it assumes | owner | satisfiability evidence | discharge plan |
|---|---|---|---|---|
| `alloc.mallocRoomRun` | `_malloc_r` top-split fast path meets `MallocRoomEnd`; for the counted regime it is stated at byte credits as `MallocCostRun` (`MallocRoomRun` at every `costRoomAt c k`, `16 ≤ c`, `VsaIris/Vsa/CostRoom.lean`), which also needs the `sbrk` extension path | H4 | `Vsa/ControlEnd.lean` (control heap, hand-computed post-states) | chain `seg_runFact` segments via `segFrom_of_runFact` |
| `alloc.mallocLocalRun` | general `_malloc_r` (bins, sbrk) meets `MallocEnd` | H4 | `ControlWitness` | per-path segment chains |
| `alloc.freeLocalRun` | general `_free_r` (coalescing, bins) meets `FreeEnd` | H4 | top-merge path proved (`FreeRoomRun`) | per-path segment chains |
| `alloc.reallocLocalRun` | `_realloc_r` grow path | H4 | `reallocSpec_of_localRun` consumers | segment chains |
| `newlib.snprintf` | `snprintf(dst, n, fmt, a3…a7)` with `0 < n < 2^31` and a `%s`/`%d` format (`FmtArgsOK`) writes a NUL-terminated string into `dst[0,n)`, keeps `stdioOwn`, prints nothing, returns with the ABI frame, in 1024 bytes of stack (`Newlib.snprintfSpec`) | H5; scheduled after E1–E6 (user, Q4) | `%lld` success path proved (VSA M3, `SnprintfSpec*`); measured frames 272 + 592 + 64 | M3 format-parser and digit-loop segments; `%s` copy loop |
| `newlib.fprintf` | `fprintf(stderr, fmt, a2…a7)` with a `%s`/`%d` format prints some string, moves newlib's data from `StdioOK` to `Ierr`, returns, in 4096 bytes of stack (`Newlib.fprintfSpec`) | H5; scheduled after E1–E6 (user, Q4) | `stderr` idle at the boundary (`ExitRuntimeData.stderr`); frames ≈ 3200 | `_vfprintf_r` → `__sbprintf` → `__sfvwrite_r` → `_write` segments |
| `newlib.fwrite` | `fwrite(ptr, 1, n, stderr)` on readable bytes prints some string, moves newlib's data from `StdioOK` to `Ierr`, returns, in 768 bytes of stack (`Newlib.fwriteSpec`) | H5; scheduled after E1–E6 (user, Q4) | frames 592 measured | `__sfvwrite_r` unbuffered path segments |
| `newlib.exitHandlers` | `exit`'s interior `0x80004778`–`0x80004788` (`__call_exitprocs(e, 0)`, `__stdio_exit_handler`) from `StdioOK` or `Ierr` reaches `0x80004788` with `s0 = e` and the ABI frame, printing some string, in 512 bytes of stack (`Newlib.exitHandlersSpec`) | H5 | `ExitRuntimeData`: empty `__atexit`, installed handler, idle files; `__call_exitprocs` with `__atexit = 0` is 20 straight-line instructions | `__call_exitprocs` by segments (short); `_fwalk_sglue`/`_fclose_r` close path |
