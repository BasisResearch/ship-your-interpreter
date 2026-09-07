# Complete concrete execution certificate

The dense-state execution and historical refinement refutation passed the resumed
1,403-module source build and a separate type/axiom audit. They use only
`propext`, `Classical.choice`, and `Quot.sound`. The counterexample uses the
previously approved physical boundary, now named
`LayoutInstance.BeforeAstOwnership.interpRunLayout`. The new ownership boundary
excludes this snapshot. The 1,403-module evidence below predates that migration.

| Theorem | Checked conclusion |
|---|---|
| `OutputAliasLoaded.snapshot_loaded` | The exact snapshot satisfies the historical physical `Loaded` boundary. |
| `LoadedOutputAlias.program_bigStep` | The source program prints one newline. |
| `OutputAliasLoaded.snapshot_halts_twoLF` | The exact dense snapshot halts with two newlines and exit code zero. |
| `OutputAliasLoaded.snapshot_not_interpSim` | Forward simulation under the historical boundary is false. |
| `OutputAliasLoaded.snapshot_not_remainingWork` | `RemainingWork BeforeAstOwnership.interpRunLayout → False`. |
| `OutputAliasLoaded.snapshot_not_behavioralCorrespondence` | Behavioral correspondence under the historical boundary is false. |

The source theorem is in `Vsa/Sim/OutputAliasProgram.lean`. The machine theorem
is in `Vsa/Sim/OutputAliasRun.lean`; the refutations are in
`Vsa/Sim/OutputAliasRefutation.lean`. `RemainingWork` is a `Type`, so its
impossibility is expressed by a function to `False`.

## Verification

The final retained-cache build rebuilt 18 modules and reused 1,385, taking
916.51 seconds with exit zero. All 1,403 source/dependency fingerprints match
and all retained objects exist. Native executable linking was not tested.

`certification/verification/receipt.json` records the source, input, and evidence
hashes. That directory contains the build transcript and manifest, the final
type/axiom audit, and the packaging receipts. The 35 counterexample proof files
pass the prohibited-token scan. The discipline checker retains its earlier
58 findings (28 R6, 18 R7, 11 R1, 1 R5), with none in the new proof files.
No full SMT/fuzzer or total-coverage success is claimed.

## Inputs and coverage

The untrusted sparse replay has 1,861 pre-instruction rows. The certificate
executes 1,860 ordinary machine steps and the final `Machine.Halted` transition.
Its initial memory is the proved dense `snapshotMem`, not the sparse replay map.
The first 14 instructions come from `snapshot_firstTrace`; 285 remaining units
supply the rest of the run and halt.

The sparse replay starts with the same physical registers and snapshot byte
values. It contains 478 integer loads and 3,028 load bytes, including 72 absent
sparse bytes read as zero. The dense snapshot proves present zero bytes at those
RAM addresses.

- Full trace: `/private/tmp/vsa-alias-loaded/full-trace/result.jsonl`.
- Partition: `/private/tmp/vsa-alias-loaded/trace-segments.json`.
- Input hashes: `snapshot-replay/trace-artifacts.json`.
- Reproduction: `snapshot-replay/FullTrace.lean` and `partition_trace.py`.
- Portable certificate generator: `certification/generate_certificates.py`.
- Generator comparison: `certification/generator-roundtrip.json`, all 286
  generated files byte-identical to the checked data and unit sources.

| Original unit kind | Units | Instruction rows |
|---|---:|---:|
| Reflected segments | 192 | 1,767 |
| Direct calls | 78 | 78 |
| Indirect calls | 11 | 11 |
| HTIF character stores | 2 | 2 |
| Additional ALU instructions | 2 | 2 |
| HTIF halt store | 1 | 1 |

The partition covers all rows in order. Its 454 basic blocks include 267 ordinary
stores and three HTIF stores. Longer segments use smaller internal certificates;
all intermediate register values, logs, branches, and loads are checked again.
No Lean limit is raised.

Four 32-bit stores require full source-register values in `WEntry`, although the
trace reports only the written low 32 bits. The generator retrieves the source
register and verifies its width-masked value against the recorded store bytes.
This preserves the exact log representation and the actual store semantics.

## Proof route

`TraceHolds` records `GoodState`, bounded tick, exact PC, register pins, output,
HTIF payload, and equality with `writeLog snapshotMem log`. `TraceHolds.segment`
uses `segEval_sound` with proved instruction bytes, decode theorems, threaded
load bytes, branch decisions, and structural conditions.

`WriteLogRead.lean` proves byte lookup from the newest matching write, including
widths 1, 2, 4, and 8. `snapshot_logRead` supplies the proved dense initial byte
function. These proofs avoid evaluating the 128 MiB hash map.

`OutputAliasDecode.lean` provides all 26 words absent from the existing decode
index. `OutputAliasCalls.lean` supplies both call forms. `OutputAliasTraceAlu.lean`
executes `SLTIU` at `0x800028dc` and `SLTU` at `0x800027f8`.
`OutputAliasPutchar.lean` executes both newline stores at `0x8000005c`.
`OutputAliasTraceHalt.lean` executes the final halt store at `0x80000190`.

`TraceFits` checks exact PC, write-log, output, and payload equality and every
target register pin. It permits canonical register ordering. Store-log checks
compare the newly computed suffix and use `List.take_add` to retain the existing
prefix. They cannot substitute a recorded machine transition for a proof.

`OutputAliasRun/Data.lean` contains the finite data. `Part00` through `Part14`
contain the checked unit proofs. `Groups.lean` composes those proofs, then
`snapshot_halts_twoLF` attaches the initial prefix and final halt.

Finally, `Machine.Halts.deterministic` excludes the one-newline halt required by
the proved source behavior. This refutes the historical physical boundary. It does
not establish the proof-closure plan's requested unconditional refinement.
