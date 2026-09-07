# Mutable output-buffer alias

The fixed ELF prints one newline for the independent-string control and two for
the aliased string. Both return normally from `interp_run` with `a0 = 0`.

This is concrete execution evidence, not a Lean `Loaded` witness or a proved
counterexample to the final refinement theorem.

## Construction

`AliasMachine.lean` boots the unchanged embedded ELF with production `setupElf`
and `stepOnce` to `interp_run` at 0x800043ec. It checks the reached sp/gp/ra/a0/a3.
It then constructs a data snapshot for:

```text
println(); if ("" == "\n") println();
```

The native global environment occupies 0x81000000..0x81001000. The AST occupies
0x82000000..0x82001000. The finite patch also sets interpreter globals/depth,
array/count arguments, buffer byte zero, and stdout flags 0x200a as required by
`ConsoleStream`. It preserves the ELF code and all other startup state.

The cases share this snapshot and differ only at the left string pointer word
0x82000108. The control points to an independent zero byte at 0x82000160. The
alias points to the actual stdout buffer at 0x8001bb97. The first `println`
changes that byte to 10; the next byte remains zero. The later equality reaches
actual ELF `strcmp` with that pointer. No machine step or native call is replaced
with a summary.

The harness stops before main's continuation at 0x800045ec. It records function
entries, output, final a0, initial/final buffer state, and boundary checks.

## Checked and unchecked facts

Both cases pass 55 finite runtime/static read checks, all 31 `GoodState` register
checks, initial x13/HTIF/output checks, and fixed .text/.rodata byte equality.
These are executable checks. They are not Lean proofs of those propositions.

Full 8 MiB stack-byte presence, `ProgramRepr`, store representation/survival,
and the complete `Loaded` construction remain unverified. The run stops at the
interpreter return; it does not claim a full HTIF halting trace.

An earlier natural-startup experiment produced the same output difference but
failed the initial flags check: CRT supplied 0x000a. That baseline is preserved
separately under `/private/tmp/vsa-output-alias-machine/startup-baseline/`.
The present snapshot deliberately pins 0x200a in both cases. It does not describe
those flags as the observed natural startup value.

## Replay

From the repository root, after installing this package at
`experiments/smt/output-alias/`, choose a fingerprint-checked private dependency
build. The recorded build was `/private/tmp/vsa-full-build.sQd0gM`. Do not infer
current fingerprint validity from its path or this historical receipt.

```sh
python3 experiments/smt/output-alias/check_run.py --repo .
lake env sh -c 'LEAN_PATH="/private/tmp/vsa-full-build.sQd0gM${LEAN_PATH:+:$LEAN_PATH}" lean experiments/smt/output-alias/AliasMachine.lean'
lake env sh -c 'LEAN_PATH="/private/tmp/vsa-full-build.sQd0gM${LEAN_PATH:+:$LEAN_PATH}" lean --run experiments/smt/output-alias/AliasMachine.lean 2000000' > /private/tmp/output-alias-result.jsonl 2> /private/tmp/output-alias.stderr
python3 experiments/smt/output-alias/check_run.py --repo . --results /private/tmp/output-alias-result.jsonl
```

Fuel is bounded separately for startup and each case. An exhausted run fails.
The observed Sail diagnostic `TODO: cancel_reservation` appeared on stderr;
execution and all recorded checks completed successfully.

Fixed ELF SHA256:
`b146c6edb76ea9a0f0f30be381f8176ed2de9717e1ae9b37feff4b2b9ca1d0f0`.
The checker verifies its exact equality with `Vsa.ElfBytes` before accepting a
result. `execution-evidence.json` records artifact hashes and observed counts;
`invocation.txt` records the scratch invocation used for this run.
