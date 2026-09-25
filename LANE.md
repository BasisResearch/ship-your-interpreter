# Lane B3: loader-derived `Loaded` witnesses (REVIEW.md P4)

Branch `lane-b3` (from `hub/iris-main` `286c2ad`, merged `hub/lane-v`).
Brief: build kernel-checked `Loaded interpRunLayout p c` witnesses for the
`c/tests/*.wl` programs from their real boot: the ELF loader's memory plus the
emulator's store log up to `interp_run`'s entry, checked by `decide`s over
the reflected state (no `native_decide`), generated per program. The
witnesses can close only after P1 (console flags) and P2 (script bytes, lane
B1) and P3 (stack presence, lane B2).

## Status: in flight (infrastructure)

## Done

- Corpus: `scripts/gen_boot_witness.py corpus` patches the proof ELF's script
  blob per script, traces each build to `interp_run` with the Lean emulator,
  and dumps `initializeMemory`'s pieces natively
  (`scripts/boot_elf_pieces.lean`). All 35 ELFs (review corpus + proof ELF)
  agree with the proof ELF outside the script blob.
- `Vsa/Sim/Boot/Log.lean`: packed store log (`PackedLog`), final byte map
  (`RunTree`), the check `LogOk` (each store against its cells, each cell
  against its last writer, with the model's own `writeEntryByte`), and
  `writeLog_view`: `(writeLog m L.log)[x]? = logView t (m[·]?) x`. No
  sequential fold in the kernel (a naive fold hits the kernel's recursion
  depth); the check splits into independent 1024-store chunks.
- `Vsa/Sim/Boot/Image.lean` + generated `ImageData.lean`: the loader's memory
  (`loadedMem script`, `initializeMemory`'s insertions over `bootPieces`),
  `bootMem script L = writeLog (loadedMem script) L.log`, `bootMem_get`.
- `Vsa/Sim/Boot/Gen/<Prog>.lean` (generated): script, log, runs, entry
  registers, `logOk`, `mem_get`. Built: `while` (9,005 stores, 66 s),
  `adv_empty` (1,455 stores, 10 s). Library `VsaBoot` (`lake build VsaBoot`).

## Next

- Boot config (entry registers into the Sail register map), per-field
  checkers of `InterpRunPhysicalFacts`/`InterpRunReadyFacts` over `bootView`.
- `initializeMemory .B64 elf = loadedMem script` from the native piece dump.
- `capacity` (`InitialAllocatorAt`): needs the cost of every terminating
  derivation, i.e. determinism of the cost relations or a cost evaluator.
- Merge B1/B2 when they land.

## Holes

None added.
