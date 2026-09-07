# Validation audit

The previous campaigns did not validate every state admitted by `Loaded`.
Parser-generated programs and selected SMT projections missed initial-memory
aliasing and access failures. The live ownership boundary now excludes the three
bad snapshots and admits a repaired control.

## Required gate

Use a current private Lean build and a new artifact directory:

```sh
python3 scripts/check_validation.py --backend /path/to/private-build \
  --output /tmp/new-validation-run
```

`check_all.sh` runs this gate even with `--skip-build`. Set `VSA_PRIVATE_BUILD`
to the private build. Build reuse requires current fingerprints for every Vsa
module and VsaRun. The serial build retains the module-time budget check.

The default gate rejects mismatches in currently admitted snapshots. Historical
excluded cases must retain their expected failures. `--self-test` accepts
expected detection for testing the harness. Artifact mutation tests use actual
Sail results; missing cases, errors, fuel exhaustion, and missing terminal
attempts fail.

| Initial-state case | Source | Machine |
|---|---|---|
| Historical AST/output alias | One newline | Two newlines; halt 0 |
| Historical unreadable AST | Empty output; termination | Sail error after 70 steps |
| Historical binding-name alias | Two newlines | One newline; Sail error after 3,813 steps |
| Stable control | Two newlines | Two newlines; halt 0 |

The fixture pins the ELF, boundary, source proofs, validator/build scripts, local
Sail sources, and exact case inventory. Each case carries a typed admission or
exclusion proof for its exact dense snapshot. Twelve theorem reports are required.
Sparse replay is not a dense execution certificate. The historical native-name
dense execution proof remains unfinished.

## Closed validation gaps

- Lean probe failures, timeouts, missing axiom reports, unrelated reports, and
  unsafe axioms no longer count as successful refutation or survival. Positive
  acceptance cases require positive proofs. Unsupported extraction is inconclusive.
- Solver failures, malformed output, inconsistent premises, empty obligations,
  and opaque antecedents cannot produce unconditional validation. Results remain
  scoped to their encoded fragment. Helper assumptions are reported as conditional.
- Houdini checks current source provenance and publishes a receipt binding each
  verdict to the completed invocation, exact queries, clauses, scope, and inputs.
  Revalidation invalidates the old receipt before work begins. The production
  ledger rejects missing or stale receipts. Houdini `--require-valid` makes
  failed or conditional projection checks return nonzero; the default mode
  produces diagnostic reports. Production remote checks use the strict flag.
- Differential testing rejects omitted corpus cases, misplaced ELF edits, stale
  traces, failed child processes, fuel-limited traces, missing halt events,
  unobserved clauses, empty sample sets, and unmatched selections. Emission
  requires a current private backend. Emulator reuse requires a source/toolchain
  and binary receipt from an explicit checked build.
- The evidence matrix includes ownership, readable memory, and initial-state
  admission. Missing coverage stays explicit. `--require-complete` fails while
  the full completion surface is unproved. Candidate retention is not labeled
  validation success.

These changes close the concrete audit findings. Four regression cases are not
exhaustive exploration of `Loaded`. Full SMT/differential campaigns and the
unconditional `RemainingWork interpRunLayout` proof remain outstanding.

## Previous verification checkpoint

- Full private Lean build: 1,433 modules, exit 0.
- Python suite: 169 tests, no skips, exit 0. Artifact mutations used the actual
  four-case Sail run in `/private/tmp/vsa-validation-gate-final`.
- Default combined validation before ownership migration: exit 1 for the alias finding. All four
  expected regression outcomes were detected.
- Both Lean fuzzer acceptance suites passed. A seeded fragment battery passed
  4/4 cases. Real Z3 checks accepted a tautology and rejected a false statement
  and inconsistent premises.
- Shell syntax, Python compilation, and scoped whitespace checks passed.

The emulator rebuild command was tested with subprocess mocks. No new emulator
binary or full SMT/differential campaign was produced during this audit.

## Current verification

The ownership migration passed a 1,453-module build, a 50-declaration type/axiom
audit, and all twelve fixture theorem reports. Fresh Sail replay passed all four
cases. The default gate returned zero; all 171 Python tests passed, including
artifact and admission-label mutations. The three bad snapshots are excluded;
the repaired control is admitted.

Evidence: `/private/tmp/vsa-initial-ownership/receipt.json` and
`validation/summary.json`. The earlier 169-test checkpoint and its receipts
predate this migration. Full SMT/differential campaigns remain outstanding.
