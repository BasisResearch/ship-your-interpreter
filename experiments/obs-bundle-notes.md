# `obs_*_other` bundle helper — placement map, form choice, dry-run counts

Deliverables: `Vsa/Sim/ObsAvoid.lean` (bundled wrappers), `scripts/apply_obs_bundle.py`
(mechanical rewriter). Pays off the #1 tree-wide elaboration wall
(`experiments/decision-census-patterns.md`): the StepObs `obs_*_other` register-frame
disequality ladder (~30k `(by decide)` blocks; `obs_alu_other` alone ~17.5k across 24
files).

## What the wrappers do

Each base `obs_*_other` takes 7 or 8 separate `(by decide)` register-disequality
arguments. Each bundled `<base>'` replaces them with ONE `∧`-conjunction hypothesis
`hdis` (the base's own conjuncts, in the base's own `(Register.K == R) = false` form),
discharged at the callsite by a single ground `(by decide)` and destructured internally
by `.1`/`.2.1`/… projections. Conclusion, implicit args, and explicit arg ORDER match
the base verbatim — a mechanical drop-in.

## Base-lemma inventory (head → defining file, decide count, arg order)

| base head | file | decides | order | wrapper |
|---|---|--:|---|---|
| `obs_alu_other` | `Muldi3Spec` | 8 | `hobs R` | `obs_alu_other'` |
| `obs_jal_other` | `DivSites2` | 8 | `hobs R` | `obs_jal_other'` |
| `obs_store_other` | `MemcpySpec` | 7 | `hobs R` | `obs_store_other'` |
| `obs_store_other_val` | `ValueSpec` | 7 | `hobs R` | `obs_store_other_val'` |
| `obs_btaken_other` | `Muldi3Spec` | 7 | `hobs R` | `obs_btaken_other'` |
| `obs_bnottaken_other` | `Muldi3Spec` | 7 | `hobs R` | `obs_bnottaken_other'` |
| `obs_jr_other` | `Muldi3Spec` | 7 | `hobs R` | `obs_jr_other'` |
| `obs_branch_taken_other` | `ValueTruthySpec` | 7 | `hobs R` | `obs_branch_taken_other'` |
| `obs_branch_nottaken_other` | `ValueTruthySpec` | 7 | `hobs R` | `obs_branch_nottaken_other'` |
| `obs_store_other_sn4` | `SnprintfSpec4` | 7 | `R hobs` | `obs_store_other_sn4'` (restated) |
| `obs_store_other_sn3` | `SnprintfSpec3` | 7 | `R hobs` | `obs_store_other_sn3'` (restated) |

The 8-decide family has the extra `(rd == R) = false` conjunct (ALU/JAL write `rd`);
the 7-decide family omits it (store/branch/jr write no GPR). `_sn3`/`_sn4` are
copy-lemmas identical in body to `obs_store_other`, but take `R` before `hobs`.

## Placement in the import DAG — and why it is cycle-free

`readback` and every `post_*_other` frame lemma live in `Muldi3Spec`; the
`get?_sigmaPost_store`/`_branch_*` frame lemmas live lower (`StepStore`/`StepBranch`,
under `StepObs`). The base `obs_*_other` lemmas are scattered across five files:
`Muldi3Spec`, `DivSites2`, `MemcpySpec`, `ValueSpec`, `ValueTruthySpec`.

**`ObsAvoid.lean` imports exactly those five.** Reachability check (script over all
`import` lines, transitive):

* NONE of `Muldi3Spec`, `DivSites2`, `MemcpySpec`, `ValueSpec`, `ValueTruthySpec`
  reaches ANY of the 24 consumer files ⇒ every consumer can `import Vsa.Sim.ObsAvoid`
  with **no cycle**.
* `DivSites2`, `MemcpySpec`, `ValueSpec`, `ValueTruthySpec`, `SnprintfSpec4` all
  themselves import `Muldi3Spec`, and `SnprintfSpec4` imports the first three — so the
  five imports collapse to a shallow cone rooted at `Muldi3Spec`.
* Every consumer that actually uses a given family already transitively imports the
  file that defines that family's base (verified per-file), so no consumer gains a
  *new* heavy dependency it did not already have — except the `Snprintf*` cohort, which
  gains `ValueSpec`/`ValueTruthySpec` only if it uses branch wrappers (it does).

**`SnprintfSpec4` is deliberately NOT imported**: it reaches consumer `DivSpec3`, so
importing it into `ObsAvoid` (which `DivSpec3` would then import) would form a cycle.
Because of that, `obs_store_other_sn4'` and `obs_store_other_sn3'` are **restated
standalone** — their bodies are the bases' bodies verbatim (`hobs.1 R …` read-back +
`get?_sigmaPost_store … R …` frame), which are reachable via
`Muldi3Spec → StepObs → StepStore`. This keeps `ObsAvoid` low in the DAG and lets the
`Snprintf` files use the primed store variant without importing `SnprintfSpec3/4`.

`StrcmpSites` appears in the census top-25 but does NOT reach `Muldi3Spec` and uses
NONE of the `obs_*_other` family (its decide tax is `hG.mseccfg`/`hG.misa`, a different
shape out of scope here). It is not a consumer of these wrappers.

## Form choice — `∧`-conjunction discharged by ONE `decide`

Chosen: `hdis : (Register.mcycle == R) = false ∧ … ∧ (Register.minstret_increment == R)
= false` — the base lemma's OWN conjuncts, right-nested, closed at the callsite by one
`(by decide)` and extracted internally by `And` projections.

Rejected: a `Bool`-fold `(R != r1 && … ) = true` + an `avoids`/`ne_of_avoids`
extraction layer. Reason: the base lemmas want `(K == R) = false`; a `!=`-fold forces a
`(K == R) = false ↔ (R != K) = true` symmetry bridge at every one of the 7-8
projections — MORE per-callsite work, and bare-core `List` membership lemmas are thin,
so a `List.all` fold would need custom head/tail lemmas anyway. The `∧` form's
extraction is pure `.1`/`.2.1` term projection: zero tactic, zero `whnf`, zero
typeclass search (`fast-reflection-rules` rules 1/6). The single discharging `decide`
reduces a bounded `Bool`-`and` of `Register.decEq` on two concrete literals — a
microsecond kernel reduction, strictly cheaper than the 7-8 separate `decide`
elaborations (each of which pays its own instance/`whnf` setup) it replaces.

No `sorry`/`axiom`/`native_decide`/`bv_decide`. `set_option maxHeartbeats 4000000`
(inherited house budget; the wrappers are term-mode one-liners so heartbeats are
irrelevant).

## Rewriter (`scripts/apply_obs_bundle.py`)

Regex-driven, conservative: matches only a head from the table followed by two SIMPLE
operand tokens (identifier / `Register.xNN`, no nested parens), then EXACTLY the head's
expected `(by decide)` count, then a single identifier tail. Wrong count (too few OR
too many), nested-paren operands, already-primed heads, and comment lines are all left
untouched and (with `--verbose`/`--dry-run`) reported. Longest-head-first ordering +
word boundaries prevent `obs_store_other` from matching inside `obs_store_other_val` /
`_sn4`. On modify it inserts `import Vsa.Sim.ObsAvoid` after the last existing import.
Idempotent (re-run → 0 sites).

    scripts/apply_obs_bundle.py --dry-run Vsa/Sim/SnprintfSpec17.lean   # report only
    scripts/apply_obs_bundle.py           Vsa/Sim/SnprintfSpec17.lean   # rewrite in place

## Dry-run rewrite counts (SnprintfSpec17 / SnprintfSpec49 / JmpSpec)

Matches the census per-shape site counts almost exactly.

### `Vsa/Sim/SnprintfSpec17.lean` — 336 sites, ~2204 `(by decide)` removed
| head | sites |
|---|--:|
| `obs_alu_other` | 175 |
| `obs_store_other_sn4` | 60 |
| `obs_branch_nottaken_other` | 55 |
| `obs_branch_taken_other` | 33 |
| `obs_jal_other` | 13 |

### `Vsa/Sim/SnprintfSpec49.lean` — 320 sites, ~2090 `(by decide)` removed
| head | sites |
|---|--:|
| `obs_alu_other` | 170 |
| `obs_bnottaken_other` | 62 |
| `obs_store_other_sn4` | 52 |
| `obs_btaken_other` | 36 |

### `Vsa/Sim/JmpSpec.lean` — 283 sites, ~1846 `(by decide)` removed
| head | sites |
|---|--:|
| `obs_alu_other` | 148 |
| `obs_store_other_val` | 119 |
| `obs_jr_other` | 16 |

### Grand total (three files) — 939 sites, **6140 `(by decide)` blocks removed**
| head | sites |
|---|--:|
| `obs_alu_other` | 493 |
| `obs_store_other_val` | 119 |
| `obs_store_other_sn4` | 112 |
| `obs_bnottaken_other` | 62 |
| `obs_branch_nottaken_other` | 55 |
| `obs_btaken_other` | 36 |
| `obs_branch_taken_other` | 33 |
| `obs_jr_other` | 16 |
| `obs_jal_other` | 13 |

Extrapolated tree-wide (census family totals): applying the same passes across all 24
consumers removes ≈ 6× per-site the family counts — on the order of ~25k `(by decide)`
blocks, ~7/8 of the whole `obs_*_other` decision tax. `obs_store_other_sn3'` (17 sites,
`SnprintfSpec3`) is covered by the rewriter but not among the three sampled files.

## Verification status

Authored only (a serial baseline build owns all cores; per task constraint, no
`lean`/`lake` run here). Bodies are direct forwards to / verbatim restatements of the
verified base lemmas, so they inherit axiom-cleanliness (`propext`/`Classical.choice`/
`Quot.sound` only). Recommended first build: `ObsAvoid.lean` ALONE, confirm axiom-clean
and each `decide` <2s, before fanning the rewriter across the 24 consumers.

## Pilot results — `Vsa/Sim/SnprintfSpec17.lean` (2026-08-29)

End-to-end validation of the rewrite on one file (`time lake env lean`, repo root,
serial, warm oleans).

| measurement | wall |
|---|--:|
| BEFORE (1 run) | **48.2s** (53.9s user) |
| AFTER run 1 | **16.2s** (18.5s user) |
| AFTER run 2 | **16.1s** (18.6s user) |
| AFTER (`-o` olean regen run) | 16.2s |

**Δ = −32.0s, −66% wall.** Well above the 20% fan-out threshold.

* Sites rewritten: **336** (exactly the dry-run counts: alu 175, sn4 60,
  branch_nottaken 55, branch_taken 33, jal 13); ≈2204 `(by decide)` removed;
  `import Vsa.Sim.ObsAvoid` inserted. Diff = 337 insertions / 336 deletions
  (1:1 line replacement + the import).
* Sites reverted / hand-fixed: **0**. Compile was green on the FIRST attempt after the
  mechanical rewrite — no argument-order, parenthesization, or regex-mangling issues.
  Spot-checked all five heads against the wrapper signatures (`hobs R` for
  alu/jal/branch, `R hobs` for `_sn4'`): correct.
* Wrapper bugs found: **none**.
* Axiom check (scratch import, fresh `-o`-regenerated olean since `lake env lean`
  alone does not refresh the cached olean): `Vsa.Sim.slotHolds_writeMap4_i2`,
  `Vsa.Sim.iov2Tail_spec`, `Vsa.Sim.iov2ToSsprintCall_spec` all depend only on
  `[propext, Classical.choice, Quot.sound]`.
* Theorem statements untouched (internal proof callsites only), so the importer
  stays green.
