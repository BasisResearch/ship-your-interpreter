# Lane B3: loader-derived `Loaded` witnesses (REVIEW.md P4)

Branch `lane-b3` (from `hub/iris-main` `286c2ad`, merged `hub/lane-v`).
Brief: build kernel-checked `Loaded interpRunLayout p c` witnesses for the
`c/tests/*.wl` programs from their real boot: the ELF loader's memory plus the
emulator's store log up to `interp_run`'s entry, checked by `decide`s over
the reflected state (no `native_decide`), generated per program. The
witnesses can close only after P1 (console flags) and P2 (script bytes, lane
B1) and P3 (stack presence, lane B2).

## Status: in flight (infrastructure; witnesses blocked on P1–P3 and C4)

## Found: C4 (new vacuity, machine-checked)

The natives' `Value` name pointers are `.rodata` literals (`0x80019538`,
`0x80019540`, `0x80019548`); `FrameOwned.values` makes those bytes `shared`,
and `BootHeapFacts.shared_geom` (`SharedGeom.ram`) requires every shared byte
at or above `0x8001acf0`. `Vsa.Sim.Boot.nativeName_obstruction`
(`Obstruction.lean`) refutes `InterpRunReadyFacts` from three reads; every
generated trace instantiates it (`Gen/<Prog>.c4_obstruction`) at its real
entry memory. Proposed fix P7 (REVIEW.md): the shared bytes' geometry admits
`.rodata` (the Iris consumers need only `ReadOK`/`SharedWin`). Pending the
user's decision; recorded in PROOF_CLOSURE_PLAN.md.

## Done

- Corpus: `scripts/gen_boot_witness.py corpus` patches the proof ELF's script
  blob per script, traces each build to `interp_run` with the Lean emulator,
  and dumps `initializeMemory`'s pieces natively
  (`scripts/boot_elf_pieces.lean`). All 35 ELFs agree with the proof ELF
  outside the script blob.
- `Log.lean`: packed store log, final byte map (`RunTree`), `LogOk` (each
  store against its cells and each cell against its last writer, with the
  model's `writeEntryByte`), `writeLog_view`. Checked in 1024-store chunks
  (a sequential kernel fold hits the recursion limit).
- `Image.lean` + generated `ImageData.lean`: the loader's memory
  (`loadedMem`), `bootMem script L = writeLog (loadedMem script) L.log`.
- `Config.lean`: the Sail register map (post-setup CSRs, traced `x1…x31`),
  `GoodState`, `gprs`; `bootConfig` (`tick = steps % 2`).
- `View.lean`: `ViewOf`, `readLEv`, `boot_read`/`boot_facts`, `.text` and
  post-script `.rodata` from the loader (P2's pin).
- `Store.lean`: partial views (`maskView` gives `store_survives` from the same
  check), C strings, values, frames, `storeRepr_initSt`.
- `Heap.lean`: `heapCheck` → `DlHeap.HeapAt` (walk, bins, top, live/exact).
- `Owned.lean`: `BootOwn`, `OwnOk`/`FrameOk`/`HeapFactsOk` (named decidable
  fields) → `Ledger`, `Immutable`, `Reserved`, `StoreOwned`,
  `StoreArraysReady`, `initialOwned_of`, `bootHeapFacts_of`.
- Generated `Gen/<Prog>.lean` for the proof ELF and every `c/tests/*.wl`
  build that reaches the entry (arithmetic, for, functions1/2, recursion,
  scope, strings, while, err_divzero, err_undefined): `logOk`, `view`,
  `c4_obstruction`, `ownOk`, `frameOk`, `heapOk` all kernel-checked.
  `lake build VsaBoot`.

## In flight

- Cost evaluator + completeness for `capacity` (sub-agent).
- AST decoder over a view + `ProgramRepr` uniqueness for `program`,
  `ProgramRepr`, `stack_admissible` (sub-agent).

## Next

- Physical facts assembly per trace once B1 (P1/P2) and B2 (P3) land.
- `initializeMemory .B64 elf = loadedMem script` from the native piece dump.

## Holes

None added.
