# Build-speed plan: apply the exponentiating strategy to `lake build`

**Thesis.** The build is slow for the same reason the proofs were slow before block
reflection: work is done by per-site search (`omega`/`decide` walls, repeated `whnf`
on reflected terms) instead of computed once on a normal form. The same lever that
cut `EvalGtRow` from 226s to 68s cuts the whole-tree wall. Attack two axes: the
per-file elaboration cost, and the import-DAG cone that a single edit invalidates.

## Measured baseline (2026-08-29)

- Fully cached build (no `.lean` changed): ~1-2s (final relink only).
- A+B merge rebuild (14 strcmp/value_equal files touched, whole downstream cone):
  ~30-40 min wall, 1100 jobs.
- The cost is elaboration, not compilation. Prior measured hotspot
  (`elab-wall-diagnosis`): `EvalGtRow` 226s/file; ~900 `omega` across 7 Eval* files
  ≈ 15 min in one cohort; block reflection took gt 226→68s, le 213→38s, lt 233→38s.

### Decision-tactic density (top offenders, `omega`+`decide`+`bv_decide` count / lines)

| count | lines | file |
|------:|------:|------|
| 3194 | 2239 | `Vsa/Sim/SnprintfSpec17.lean` |
| 2611 | 1346 | `Vsa/Sim/SnprintfSpec49.lean` |
| 2430 | 1535 | `Vsa/Sim/JmpSpec.lean` |
| 1980 | 1548 | `Vsa/Sim/ExecBrkCont.lean` |
| 1861 | 1532 | `Vsa/Sim/SnprintfSpec5.lean` |
| 1731 | 2186 | `Vsa/Sim/StrlenSpec.lean` |
| 1313 | 1611 | `Vsa/Sim/DivSpec3.lean` |
| 1307 | 1152 | `Vsa/Sim/StrcmpSpecW2.lean` |

Snprintf specs dominate; the arithmetic/string specs (`Jmp`, `Strlen`, `Div`,
`StrcmpW2`) follow. A file with 3000+ `omega`/`decide` calls is 3000+ independent
decision procedures the elaborator runs on every build of that file.

### Import fan-out (most-imported modules = cone-invalidation cost)

| importers | module |
|----------:|--------|
| 573 | `Vsa.Elf` |
| 523 | `Vsa.Sim.InitValues` |
| 47  | `Vsa.Sim.ValueSites` |
| 31  | `Vsa.Sim.DecodeTable.Batch01Part04` |
| 22  | `Vsa.Triple` |
| 17  | `Vsa.Sim.ValueSpec` / `RegAccess` / `ExecuteAlu` |
| 16  | `Vsa.Sim.StepObs` |

`Elf` and `InitValues` sit under nearly everything. Editing either rebuilds the
world. `DecodeTable` is already batch-split (`Batch01Part04` etc.), which is the
DAG-splitting move applied once already and worth generalising.

## Axis 1: kill the per-file decision walls (the exponentiating core)

The move is identical to the proof-side win. Replace a ladder of N per-site
`omega`/`decide`/`by decide` with ONE `decide` on a reflected normal form, or with a
precomputed lemma the site closes by `rfl`/`exact`.

1. **Reflect the pin/bound facts.** The Snprintf and strcmp specs re-derive address
   bounds, alignment, and HTIF-window disjointness per site with fresh `omega`. Lift
   these to a per-region reflected predicate proved once (as `chain_out` did for
   `sailOutput`, and `seg_frame_facts` for cross-block frames). The site then reads a
   field, no `omega`.
2. **Memoise reflected terms as `rfl`-normal defs.** `writeMap8` towers,
   `evalBlocks … .log`, `chainEndPC` — compute each to a canonical normal form in a
   `def` marked for reduction, so downstream sites hit a cached `rfl` instead of
   re-`whnf`'ing the tower. This is what made B's `eqDispatch_mem_tower` a one-line
   `rfl`; generalise it to the Snprintf digit-loop and strlen word-loop towers.
3. **Batch the `by decide` disequality walls.** The register-frame proofs run a
   `(by decide)` per register per site (the `f_14/f_15` ladders). `chain_out`'s
   `noiseAvoid`/`consAvoid`/`appendAvoid` already fold these for output; extend the
   same fold to the register frame so a whole segment's avoidance is one `decide`
   over the unioned write-set, not one per site.
4. **Prefer `Nat`/`BitVec` normal-form lemmas over `omega` for fixed addresses.**
   Where an address is a concrete literal, a `by decide` on the closed `BitVec` beats
   `omega`'s linear-arithmetic search; where it is `sp + k`, a single
   `sp_off_toNat`-style lemma (B introduced one) closes it without `omega`.

Target: the top-8 files above from ~1500-3000 decisions to a few hundred. On the
measured 226→68s ratio, that is the difference between a 35-min tree and a ~10-min
tree.

## Axis 2: shrink the invalidation cone

The wall-clock is the critical path (longest single-file chain), so the goal is to
make a typical edit touch a small cone, and to keep the two root modules frozen.

1. **Freeze `Elf` and `InitValues`.** They are imported by 500+ files; any edit is a
   full rebuild. Split each into a tiny stable interface module (the
   `def`s/notations everything needs) and a heavy implementation module that few
   things import. Put a CI note: changes to the interface require a full-build
   justification.
2. **Push heavy elaboration into leaves.** A hot base file (`StrcmpSpec`,
   `ValueSpec`) that many files import forces its elaboration cost onto every
   rebuild of the cone. Move the expensive lemmas down into leaf files (imported by
   one or two), leaving the base with lightweight signatures. This is why relocating
   `blockC_lt` out of `EvalBinSim4` (2129→112 lines) helped.
3. **Generalise the batch-split.** `DecodeTable` is already `BatchNNPartNN`. Apply
   the same partitioning to the Snprintf spec family (17/49/5/3/43/45/7/46 are
   separate files already, good) so no single file is both hot and widely imported.

## Axis 3: measure and gate (so gains do not regress)

1. **Rank by real profiler, not static counts.** `set_option profiler true` /
   `trace.profiler` per file, or `lake build` with per-file timing, to turn the
   static table above into a measured wall-time ranking. Static `omega` count is a
   proxy; confirm before cutting.
2. **Per-file elab budget as a CI gate.** `fast-reflection-rules` already states
   ">2s leaf `decide` = revert" and ">10% or >2s per-file elab = revert". Wire that
   into `scripts/check_all.sh` (or a sibling) as a hard per-file wall-time ceiling so
   a regression cannot land silently.
3. **Track the critical path.** Record the longest single-file chain each build;
   that number, not total job count, is the wall-clock to drive down.

## Sequence

1. Profile the top-8 hot files; confirm the static ranking against wall time.
2. Land the reflected-bound + memoised-tower rewrite on the single worst file
   (`SnprintfSpec17`) as the template; measure the delta.
3. Fan the template out across the Snprintf and strcmp/strlen cohorts.
4. Split `Elf`/`InitValues` into interface + impl; measure the cone shrink.
5. Add the per-file elab-budget gate to `check_all`.

## Risk

- The reflected-normal-form rewrite is exactly the elaboration discipline in
  `fast-reflection-rules`; the risk is a rewrite that trades `omega` for a `decide`
  on a term that does NOT reduce cheaply (a searchy typeclass, a `whnf` that unfolds
  `writeLog`). Enforce the same per-file budget on the rewrite itself, and revert any
  leaf whose `decide` exceeds the ceiling.
- Splitting `Elf`/`InitValues` is a wide, load-bearing edit; do it as one atomic
  changeset with a full-build gate, exactly as blocker A was run.
