# Output alias machine experiment

Status: compiled and executed. Control printed one newline; alias printed two.
Both returned normally. The initial runtime audit failed: stdout flags were
0x000a, whereas ConsoleStream requires 0x200a. No fixup or rerun was performed.
See execution-evidence.json, invocation.txt, and preserved result.jsonl.

`AliasMachine.lean` runs the unchanged embedded fixed ELF using production
`Vsa.setupElf` and `Vsa.stepOnce`. It boots once to `interp_run` at 0x800043ec,
before executing that instruction. It rejects unexpected sp/gp/ra/a0 values.
Both experiments use that same reached snapshot.

The patch installs the native global environment at 0x81000000 and two-statement
AST at 0x82000000 for `println(); if ("" == "\n") println();`. It changes a1/a2 to
the new statement array/count and the interpreter's globals pointer. The only
case-dependent memory word is the left string pointer at 0x82000108:

- Control: 0x82000160, an independent zero byte.
- Alias: 0x8001bb97, the actual one-byte stdout buffer, explicitly initialized zero.

All original physical runtime state remains from startup. The native calls have
zero arguments; no `value_print`, `fputs`, or allocation is required by this AST.
The string equality operation is C token 19 and reaches the ELF's `strcmp`.

Execution stops before main's continuation at 0x800045ec. The trace records
native `println`, `value_str`, `value_equal`, and `strcmp` entries, plus initial
and final buffer/cursor/write-count/flags/main saved-RA bytes. The checker expects
one newline for control and two for alias. The preserved execution observed both outputs.

## Run procedure

1. Check fixed ELF and embedded byte identity:

   ```sh
   python3 /private/tmp/vsa-output-alias-machine/check_run.py --repo /Users/kirancodes/Documents/code/verified-semantic-abstraction
   ```

2. Obtain the root agent's serialized compiler/execution slot. Use the current
   fingerprint-checked private Lean dependency overlay to compile the scratch
   leaf. Do not run `lake build`, alter shared source, or rebuild the emulator.
   Set `LEAN_PATH` to that overlay and its validated dependencies; use the exact
   toolchain compiler. The leaf has a normal `main`, so `lean --run
   /private/tmp/vsa-output-alias-machine/AliasMachine.lean 2000000` is sufficient
   for a first bounded execution after a successful compile. Capture stdout in
   `result.jsonl` and stderr in `run.stderr`. Record exact invocation and hashes.

3. Validate:

   ```sh
   python3 /private/tmp/vsa-output-alias-machine/check_run.py --repo /Users/kirancodes/Documents/code/verified-semantic-abstraction --results /private/tmp/vsa-output-alias-machine/result.jsonl
   ```

Fuel is separately bounded for startup and each case. Failure to reach the
required PC is an error, not a successful result. No execution oracle is added
to any theorem; this is a direct runtime experiment under the existing semantics.

## Boundary limits

This harness does not construct or claim `Loaded`. A naturally reached sparse
machine snapshot need not have a present byte at every address in the full
8 MiB abstract stack region. `GoodState`, the complete fixed/runtime predicates,
source representation/store survival, and every field of `Loaded` need separate
checking or Lean proof. The read-level AST recipe was independently audited by
the certificate worker. This experiment isolates whether the mutable buffer
alias changes actual execution; a complete theorem counterexample additionally
requires those outstanding boundary obligations.
