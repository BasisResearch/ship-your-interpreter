# Explicit snapshot replay

The sparse replay starts from `physicalState` with tick/steps zero. It uses
`snapshotByte` on the entire fixed image and every `snapshotWords` extent.
Other bytes are absent and Sail reads them as zero. No boot or state repair runs.

The interpreter returns at step 1,409 with `a0 = 0` and output `"\n\n"`.
Actual HTIF halt occurs at step 1,861 with exit code zero and the same output.
Compilation and execution exited zero; their logs are empty.

`Vsa.Sim.OutputAliasLoaded.snapshot_loaded` proves `Loaded` for the finite
128 MiB `snapshotMem`. This replay uses a smaller map and does not prove a
machine run of that dense state. The complete instruction trace is available
at `/private/tmp/vsa-alias-loaded/full-trace/`; it is untrusted certificate input.

`commands.txt` records the exact scratch commands. The copied harness can be
run from the repository root with current private dependencies:

```sh
lake env sh -c 'LEAN_PATH="/private/tmp/vsa-full-build.sQd0gM${LEAN_PATH:+:$LEAN_PATH}" lean --run experiments/smt/output-alias/snapshot-replay/SnapshotReplay.lean 20000'
```

The fuel bound is checked. Exhaustion, a Sail error, or unexpected output
returns a nonzero exit status. `sha256.txt` records the original artifacts.
