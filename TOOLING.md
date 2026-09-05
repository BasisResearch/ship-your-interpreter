# Proof tooling

[PROOF_CLOSURE_PLAN.md](experiments/smt/PROOF_CLOSURE_PLAN.md) records proof
status, remaining obligations, and validation requirements.
[CLAUDE.md](CLAUDE.md) specifies proof discipline.

## Build and tests

```sh
python3 -B scripts/build_private.py \
  --output-root /private/tmp/vsa-full-build.sQd0gM \
  --include-executable --resume
python3 -B -m unittest discover -s scripts/tests
python3 -B scripts/gen_m4_term_row.py --check
python3 -B scripts/gen_term_case_bundle.py --check
git diff --check
```

Reuse the private cache and its manifest. On a new checkout, create an external
directory with `mktemp -d` and retain it. The driver compiles current sources
serially, including modules outside `Vsa.lean` and `VsaRun.lean`.
Dependencies must already be built. `--list` inspects the import order.

`check_all.sh` contains generator, discipline, forbidden-token, and axiom
checks. Follow the plan's gate procedure with current private objects.
`check_discipline.py` checks `discipline_rules.tsv`; its outstanding
findings are recorded in the plan.

## Proof generators

Run `scripts/abs_inventory.sh` before extending a proof. Search for an
existing theorem or generated segment with the required shape.

| Task | Tool |
|---|---|
| Whole-function blocks and supported loop folds | `gen_fn.py` |
| Segment and framed arm bridge | `genseg.py` |
| Site battery from instruction TSV | `gen_sites.py` |
| Disassembly to site table or segment draft | `disasm_to_sites.py`, `disasm_to_segment.py` |
| Annotated segment composition | `gen_segment.py` |
| Checked source variants | `twin_spec.py` |
| Recursive rows and case bundle | `gen_m4_term_row.py`, `gen_exec_row.py`, `gen_bin_dispatch_row.py`, `gen_term_case_bundle.py` |
| Entry and call bridges | `gen_arm_bridge.py`, `gen_stagepre.py` |
| Error routing and spill rows | `gen_m5_error_routing.py`, `gen_err_spill_rows.py` |
| Layout, image and transport facts | `gen_layout.py`, `gen_image_pins.py`, `gen_transport.py` |
| Decode imports | `gen_decode_index.py` |
| Assembly record | `experiments/gen_assembly_skeleton.py` |
| Code pins and environment sites | `experiments/gen_code_lemmas.py`, `experiments/gen_envget_sites.py` |

Script paths are under `scripts/` unless shown otherwise. Use `--help`
and the generator's source for its schema. Preserve TSV, TOML, JSON and
template inputs for retained generators. Complete draft proof obligations
before adding generated modules to `Vsa/`.

## Validation

| Task | Tool |
|---|---|
| Compiled supplier census | `field_census.py` |
| Statement counterexamples | `statement_fuzz.py` |
| SMT refutation, inhabitation and joint-contract checks | `smt_check.py` |
| Candidate statement amendments | `cegis_cure.py` |
| Bounded invariant selection | `houdini_ih.py` |
| Bounded proof-construction experiments | `autoprove.py` |
| Summary mining and residual queries | `houdini_summary.py` |
| Trace, semantic and effect checks | `difftest.py`, `difftest.sh` |
| Typed evidence accounting | `residual_coverage_ledger.py` |

The statement checker and fuzzer write `vsa-smt-check.log` and
`vsa-statement-fuzz.log` under the system temporary directory.
Candidate amendment reports go under its `vsa-cures/` directory.
Lean acceptance inputs remain under `experiments/invariants/`,
`experiments/cegis/` and `experiments/fleet/obstructions/`.

## Differential tests

```sh
scripts/difftest.sh --mine --out /tmp/difftest
```

The default corpus is `c/tests/*.wl` and `c/difftests/*.wl`.
The driver builds separate corpus ELFs and checks the proof-image hash.
Its phases check span reachability, summary clauses, instruction semantics,
exit states and writes against traces from the Sail model.

Use `--mine` after encoder changes. The opt-in
`VSA_DIFFTEST=1 scripts/check_all.sh` stage does not pass it automatically.
Run the campaign with exclusive compiler access.

Keep `c/while-riscv-htif.elf` unchanged. Build interpreter variants in a
temporary copy of `c/`. Interpret SMT verdicts with their capability,
assumption and provenance records, as specified in the proof plan.
