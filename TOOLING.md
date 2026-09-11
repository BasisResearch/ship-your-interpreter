# Proof tooling

[PROOF_CLOSURE_PLAN.md](experiments/smt/PROOF_CLOSURE_PLAN.md) records proof
status, remaining obligations, and validation requirements.
[CLAUDE.md](CLAUDE.md) specifies proof discipline.

## Build and tests

```sh
# Source-only gate. This does not require or validate compiled objects.
scripts/check_all.sh --static-only
python3 -B -m unittest scripts.tests.test_check_all

# Compiled checks.
python3 -B scripts/build_private.py \
  --output-root /private/tmp/vsa-full-build.sQd0gM \
  --include-executable --resume
python3 -B -m unittest discover -s scripts/tests
VSA_PRIVATE_BUILD=/private/tmp/vsa-full-build.sQd0gM scripts/check_all.sh --skip-build
git diff --check
```

`check_all.sh --static-only` runs generator drift, discipline, the informational
IH summary, and forbidden-token checks. Its success message explicitly excludes
compiled checks. The full gate requires `VSA_PRIVATE_BUILD`; `--skip-build`
still checks compiled-object freshness, boundary validation, and theorem axioms.

Reuse the private cache and its manifest. On a new checkout, create an external
directory with `mktemp -d` and retain it. The driver compiles current sources
serially, including modules outside `Vsa.lean` and `VsaRun.lean`.
Dependencies must already be built. `--list` inspects the import order.

`check_all.sh` runs generator, discipline, and forbidden-token checks before
requesting the backend or starting compiled checks. Follow the plan's gate
procedure with current private objects.
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
| Induction-hypothesis clause modules | `gen_ih_clause.py` |
| Footprint row modules (IH tower, Level 1) | `gen_footprint_row.py` |
| Entry and call bridges | `gen_arm_bridge.py`, `gen_stagepre.py` |
| Error routing and spill rows | `gen_m5_error_routing.py`, `gen_err_spill_rows.py` |
| Layout, image and transport facts | `gen_layout.py`, `gen_image_pins.py`, `gen_transport.py` |
| Decode imports | `gen_decode_index.py` |
| Assembly record | `experiments/gen_assembly_skeleton.py` |
| Owned source recursion | `python3 -B -m scripts.gen_allocator_cases` |
| Code pins and environment sites | `experiments/gen_code_lemmas.py`, `experiments/gen_envget_sites.py` |

Script paths are under `scripts/` unless shown otherwise. Use `--help`
and the generator's source for its schema. Preserve TSV, TOML, JSON and
template inputs for retained generators. Complete draft proof obligations
before adding generated modules to `Vsa/`.

`python3 -B -m scripts.gen_allocator_cases` reuses the constructor parser
from `gen_ih_clause.py` to generate owned source recursion. `AllocatorCases`
supplies the five leaves, expression statements, both equality branches,
block statements, and all sequence constructors. `mExecSeq` retains owned
returns for each physical copy. `seqConsNormal` and `seqConsAbrupt` select the checked
supplier for that copy; `Residuals` has 40 fields. `AuxMotives` carries six
auxiliary relation contracts. All nine source relations have an induction
entry point. Run the generator with `--check` to detect drift.

`genseg.py` and `gen_sites.py` accept `--default-limits` to omit elaboration
limit overrides. The initial null-call proofs use that mode:

```sh
python3 -B scripts/genseg.py scripts/arms/initialValueNullCall.toml \
  --default-limits -o Vsa/Sim/rows/InitialValueNullCall.lean
python3 -B scripts/gen_sites.py scripts/initial_null_sites.tsv \
  --code-loaded Vsa.Sim.Code.Interp_runLoaded --suffix _initialNull \
  --default-limits -o Vsa/Sim/InitialNullSites.lean
python3 -B scripts/gen_sites.py scripts/initial_exec_sites.tsv \
  --code-loaded Vsa.Sim.Code.Interp_runLoaded --suffix _initialExec \
  --default-limits -o Vsa/Sim/InitialExecSites.lean
python3 -B scripts/gen_sites.py scripts/sequence_dispatch_sites.tsv \
  --code-loaded Vsa.Sim.Code.Eval_exprLoaded --suffix _sequenceDispatch \
  --default-limits -o Vsa/Sim/SequenceDispatchSites.lean
python3 -B scripts/gen_sites.py scripts/closure_body_sites.tsv \
  --code-loaded Vsa.Sim.Code.Eval_exprLoaded --suffix _closureBody \
  --default-limits -o Vsa/Sim/ClosureBodySites.lean
python3 -B scripts/gen_sites.py scripts/closure_param_sites.tsv \
  --code-loaded Vsa.Sim.Code.Eval_exprLoaded --suffix _closureParam \
  --default-limits -o Vsa/Sim/ClosureParamSites.lean
python3 -B scripts/gen_fixed_image.py \
  --projection Value_null --projection Exec_stmt --projection Eval_expr \
  --projection Value_int --projection Value_bool --projection Value_str \
  --projection Value_truthy --projection __muldi3 --projection __divdi3 \
  --projection __umoddi3 --projection __hidden___udivdi3 \
  --projection __moddi3 --projection Env_define --projection Strcmp --check
```

The in-frame helper-call `jal` sites of `exec_stmt` (`HelperCall` instances) are
generated the same way:

```sh
python3 -B scripts/gen_sites.py scripts/helper_call_sites.tsv \
  --code-loaded Vsa.Sim.Code.Exec_stmtLoaded --suffix _hc \
  --default-limits -o Vsa/Sim/HelperCallSites.lean
```

Induction-hypothesis clauses are declared in `scripts/ih_clauses.tsv` (name,
kind `extra`/`extraM`/`motive`, the predicate, imports,
non-`EvalE` motive overrides, a `guard` on the expression, per-case discharge
tags). Kind `motive` takes the `EvalE` motive ITSELF
(`SpecSt → Nat → Addr → Expr → SpecSt → Value → Prop`, generated `clauseMotive`)
for a fact that depends on the returned VALUE, which an `EvalExtraM` cannot see:
clause `FootprintCov` at `EvalIHFP noArenaFoot` (footprint ∧ the returned value's
payload coverage), whose left-child coverage is what the four string-comparison
cells of `BinaryFootprintCells` need. A `guard` (a Lean `Prop` over the `mEvalE` binders, e.g.
`Vsa.Sim.IHClauseGeneric.noAllocExpr e = true`) makes the `EvalE` motive
`<guard> → EvalIHWithM extraM …`, so every clause child IH and the clause
parent carry it and a step outside the guard is vacuous (clause `FootprintNA`).
A guarded clause wires a step stated WITHOUT the guard with
`unguarded:<term>|<proj_1>|…|<proj_k>`, where `proj_i` maps the parent guard to
the i-th `EvalE` child's guard (none for a leaf). Each line emits
`Vsa/Sim/rows/IHClause_<Name>.lean`: `extraM` (or `clauseMotive`), the nine
clause motives (`mEvalE` = `EvalIHWithM extraM`, resp. `clauseMotive`), `Residuals` (one field per recursor case with a clause motive; a
`Layout` parameter for the census), `of_residuals`/`execSeq_of_residuals`
(the recursor over the product motive old ∧ clause), and `Residuals.ofUnwired`
for the fields wired to a discharger. Regenerate and check with

```sh
python3 -B scripts/gen_ih_clause.py            # write every clause module
python3 -B scripts/gen_ih_clause.py --check    # drift (stage a3)
python3 -B scripts/gen_ih_clause.py --stdout --clause Footprint
```

Footprint rows are declared in `scripts/footprint_rows.tsv` (arm, family, module,
result value, residual, cell guards, cell/shared/node footprints, boxing helper,
supplier, per-arm extras). Each line emits
`Vsa/Sim/rows/Eval<Arm>RowFootprint.lean`: the node footprint and its `_noArena`
lemma, `eval<Arm>SimF` (the landed sim through the footprint-carrying blocks), the
row at `EvalEntry`, and the arm's contract and supplier (`Bin<Op>CellF` +
`bin<Op>CellF_of`, or `eval<Arm>IHF`). A family is one template plus the arm's slot
values; proof fragments that differ structurally between two arms of a family live
in the generator's `ARM_FRAGMENTS`. The shared cell footprints `intCellFoot` and
`truthyArgCellFoot` (`Vsa/Sim/ExitFootprint.lean`) close the cell half of every
`<arm>NodeFoot_noArena`.

```sh
python3 -B scripts/gen_footprint_row.py            # write every footprint row
python3 -B scripts/gen_footprint_row.py --check    # drift (stage a3)
python3 -B scripts/gen_footprint_row.py --stdout --arm neg
```

A NEW FAMILY (the allocating `allocFoot` family, an exec-side arm) adds one
`TEMPLATES` entry — the landed module with its per-arm names replaced by
`%%SLOT%%` — one `SLOTS_FROM_TSV` entry naming the slots the table fills, and one
TSV line per arm; `--check` then fails on any drift between table and modules.

Use `gen_transport.py value_int --exact-range` to regenerate
`rows/TransportValue_intRange.lean`. This mode requires agreement only on the
callee's code interval. `--stdout` emits without writing; compile through the
private backend, not the generator's direct `--check` mode.

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
| Clause residual status, hook probes, candidate drafts | `ih_clause_status.py` |
| Clause step refutation | `ih_clause_fuzz.py` |
| Clause field evidence ledger | `ih_clause_ledger.py` |

The default `check_validation.py` gate imports every compiled module and
inventories inherited residual fields before running boundary regressions.
Run supplier search separately:

```sh
python3 -B scripts/field_census.py \
  --backend /private/tmp/vsa-full-build.sQd0gM --output /private/tmp/vsa-census
```

Use `--inventory-only` for field enumeration or repeat `--field NAME` for a
subset. Probes run serially. `FOUND` requires a checked proof and standard
axioms. `NO_MATCH` is inconclusive. Reports retain source and backend hashes;
supplier search does not construct the final residual record.

For a development check of a known supplier, use a persistent private overlay:

```sh
python3 -B -m scripts.proof_slice \
  --backend /private/tmp/vsa-full-build.sQd0gM \
  --output /private/tmp/vsa-proof-work \
  --module Vsa.Sim.IntegerCellSuppliers \
  --field hIAdd --supplier Vsa.Sim.ScaffoldRows.field_hIAdd \
  --audit Vsa.Sim.ScaffoldRows.field_hIAdd --plan-only
```

Remove `--plan-only` to run. The preview lists required builds and cache reuse.
Repeated runs reuse fingerprint-matching objects in the overlay. The original
backend is read-only. Use `--module` and `--audit` repeatedly for a declaration
audit without a field check. `--field` requires `--supplier`; Lean checks that
term against the actual inherited field type through the census elaborator.

Each successful run writes a separate receipt containing source/dependency
fingerprints, object hashes, timings, exact axiom reports, and the field-check
result. Failed runs retain diagnostics without a success receipt. A slice
checks only its selected dependency closure. The complete-library census,
resumed integration build, and checkpoint regression gates remain required.
Run with exclusive compiler access, as specified above.

For an obligation checkpoint, add `--checkpoint <description.json>`. The
description names the requested obligation and its exact acceptance type:

```json
{
  "target_obligation": "remainingWork_closed",
  "target_type": "Vsa.Sim.RemainingWork Vsa.Sim.interpRunLayout",
  "consumer": "Vsa.Sim.remainingWork_closed",
  "role": "target",
  "remaining_premises": []
}
```

This is the final acceptance description; it passes only once that consumer
exists at the stated type. Use fully qualified names and explicit, single-line
type expressions. Holes, commands, comments, and implicit free parameters are
not accepted. List outstanding premises as `{"name": "child", "type": "..."}`;
the check prepends these dependent binders to the target type and reports
`conditional`. With no remaining premises it reports `complete` for that
specified obligation. To record a helper, use `"role": "prerequisite"` and
add its exact `consumer_type`; this always reports `prerequisite`.

The generated consumer application is checked and audited before a successful
receipt is written. An axiom audit of a helper alone cannot close the target.
The caller must supply the correct requested type and all remaining premises;
the tool does not infer the user's intended obligation or enumerate project-wide
prerequisites. Existing full-library and residual-coverage flags remain false.

Slice receipts also retain actual build/reuse counts, a UTC start time, and
elapsed wall time for planning, dependency compilation, consumer checking,
evidence validation, and the unattributed remainder. These are wall durations,
not CPU measurements. The measured interval ends before receipt serialization.
An unattributed interval is not evidence of duplicate attempts or avoidable cost.

Native checkpoint tests use disposable projects and external build outputs.
Run them only with exclusive compiler access:

```sh
VSA_NATIVE_CHECKPOINT_TESTS=1 python3 -B -m unittest \
  scripts.tests.test_proof_checkpoint_native
```

The default Python suite skips these compiler tests.

The statement checker and fuzzer write `vsa-smt-check.log` and
`vsa-statement-fuzz.log` under the system temporary directory.
Candidate amendment reports go under its `vsa-cures/` directory.
Lean acceptance inputs remain under `experiments/invariants/`,
`experiments/cegis/` and `experiments/fleet/obstructions/`.

### Induction-hypothesis clause fields

The generated clause records `Vsa.Sim.IHClause.<Name>.Residuals` (one field per
recursor case, `scripts/ih_clauses.tsv`) have their own automation over the
same elaborators. `check_all.sh` stage a5 prints the status summary without
failing the gate. `--backend` accepts the full private backend or a
`proof_slice` overlay that contains the clause modules; run Lean-backed modes
with exclusive compiler access.

```sh
python3 -B scripts/ih_clause_status.py --summary               # WIRED / HOOK / MANUAL / STALE
python3 -B scripts/ih_clause_status.py --backend <B> --output <D> \
  --verify-census --suggest                                      # hook lemmas, census re-check, drafts
python3 -B scripts/ih_clause_fuzz.py --output <D> [--lean --backend <B>]
python3 -B scripts/ih_clause_ledger.py build --dir <D>
python3 -B scripts/field_census.py --backend <B> --output <C> \
  --structure Vsa.Sim.IHClause.Trivial.Residuals                 # supplier search (full backend only)
python3 -B -m scripts.proof_slice --backend <B> --output <O> \
  --module Vsa.Sim.rows.IHClause_Trivial \
  --structure Vsa.Sim.IHClause.Trivial.Residuals --field hInt --supplier <ident>
```

`ih_clause_status.py` writes `ih_clause_status.tsv/json`; a HOOK field names the
expected lemma `Vsa.Sim.IHClauseGeneric.<id>.<case>` with its source-scan and
backend (`#print axioms`) result. `--suggest` drafts every hook lemma and
`*_of_old` discharger of `Vsa/Sim/IHClauseSupport.lean` (plus `--candidate`)
per open field into `<D>/drafts/Draft_<Name>.lean`, checks them in one Lean run
per clause, runs `houdini_ih.py`/`autoprove.py` with the field registered at
its encoding (`--bounded-target <case>=<encoding>`; the default is an honest
`encode-gap`), and records DIRECT / WITH-IH / FAILED / UNSUPPORTED in
`ih_clause_suggest.tsv`. Nothing is written into `Vsa/`.

Each clause-wide candidate compilation also writes a new read-only JSON receipt
under `<D>/attempts/`. It retains the generated statements, candidates and
diagnostics, target names, toolchain and dependency fingerprints, and measured
compiler wall time. Missing or changed comparison inputs are explicit. Such an
attempt receives no comparable key. These records are attempt evidence; they do
not certify a proof or suppress another run.
Receipts time input capture separately; include that overhead when comparing costs.

Use `--rerun-reason "..."` to retain the reason for a repeated candidate run.
Measure the retained receipts before deciding whether retry suppression is
worth implementing:

```sh
python3 -B scripts/attempt_receipts.py <D>/attempts
```

Counts refer to clause-wide compilations. Separate candidates within one
compilation are not separate timed attempts. Historical logs without complete
input fingerprints cannot establish duplicate attempts or potential time savings.

`ih_clause_fuzz.py` extracts each step into `<D>/statements/<Name>_<case>.lean`
(`def Step_<case> (_L : Layout) : Prop`, the `statement_fuzz.py --file` shape)
and reports REFUTED / NOT-REFUTED / UNSUPPORTED. A wired field is NOT-REFUTED
by its compiled wiring; an unwired step concludes a motive over machine runs,
outside the address-map fragment, so it is UNSUPPORTED unless `--lean` runs
the fuzzer's witness probe against a fingerprint-current backend.
`smt_check.py` is not applied (a motive conclusion is an opaque atom to it).

`ih_clause_ledger.py` emits one row per field and evidence kind (execution,
smt, oracle, lean-bridge) from those artifacts and an optional `--execution`
TSV; a missing artifact is an explicit hole.

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
