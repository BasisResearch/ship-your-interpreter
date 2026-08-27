# Elab-wall strategy — MEASURED: the wall is per-call `omega` in the row/eval-sim cohort

Companion to `exponentiation-plan.md`. That plan collapses `O(cases×sites)` hand-proof into
`O(1)` machinery + `O(cases)` trivial rows — and it is right. The failure is that a cohort of files
**bypasses that machinery entirely** and pays a fixed per-call tactic tax thousands of times.
This doc is grounded in HARD MEASUREMENTS from `scripts/elab_profile.sh` (serial, warm oleans),
not `decide`-counting. Priorities below reflect what the profiler actually showed, which overturned
two plausible-but-wrong guesses (see "What we ruled out").

## Measured baseline (`experiments/elab-timings.tsv`, warm-olean single-file wall)

| file | wall | why |
|------|------|-----|
| **`rows/EvalGtRow.lean`** | **226 s** | ~130 `omega` @0.2–0.6s + `instantiate metavars` 10.3s + ~6 `rewriteSeq` @0.2s |
| `Code/Eval_expr.lean` (12.4k lines) | 12 s | no single decl >100ms; pure import+structural, NOT a monster |
| `SvfprintfSlice.lean` (7.2k) | 4 s | — |
| `StrcmpSites.lean` (714 `decide`) | 3 s | raw decides are individually cheap |
| `BlockMem.lean` (reflection layer, control) | 3 s | the abstraction layer IS fast — rules hold there |

**The wall is not any single pathological file and not the code image.** It is the *aggregate* of a
COHORT of hand-written `Eval*` proof files, each ~200s, dominated by a fixed per-invocation `omega`
tax paid thousands of times. Full clean build ≈ 15 min because ~7+ of these sum to ~25 min of the
total (parallelized down to 15).

## VALIDATED: omega is ~51% of the elab (throwaway substitution probe)

Replacing every `omega` in `EvalGtRow` with `sorry` (perl `s/\bomega\b/sorry/g`, throwaway) and
timing the compile: **226s → 111s**. So omega's true marginal cost is **~115s, 51% of the file's
elaboration** — eliminating it (pay it once in `SpillSafe` lemmas, apply by name) is the validated
P0 win. (Caveat learned: BSD `sed` silently ignores `\b`; the first probe was a false negative that
nearly discarded the right approach — always verify the substitution count.) The full-threshold
aggregate profile (`refine 112s / omega 66s / metavars 10s / obtain 10s / typecheck 8s / rw 7s`)
under-counts omega because its cost is partly nested in `refine`; the marginal substitution probe is
the ground truth.

## The cohort (same 226s pattern — this IS the wall)

| file | lines | `decide` | `omega` | `#derive_case` |
|------|------:|------:|------:|:---:|
| `rows/EvalGtRow` | 2021 | 511 | 132 | **0** |
| `rows/EvalLeRow` | 1977 | 496 | 132 | **0** |
| `EvalBinSim4` | 2129 | 526 | 135 | **0** |
| `EvalBinSim2` | 1755 | 336 | 138 | **0** |
| `EvalBinSim3` | 1667 | 302 | 138 | **0** |
| `EvalLogical3` | 1571 | 170 | 208 | **0** |
| `EvalLogical4` | 1605 | 173 | 208 | **0** |

`#derive_case = 0` everywhere: these files **bypass the entire L1/L2/L3 abstraction the plan built.**
They are hand-threaded. ~130 `omega` × 7 files ≈ **900 `omega` invocations**, each paying omega's
~0.3–0.5s *fixed setup overhead* regardless of goal triviality ≈ **5–8 minutes of pure omega tax.**

## Root mechanism — the redundant trivial work, named exactly

Each `omega` (and much of the metavar blowup) discharges a **spill-slot address** obligation:
```lean
spill_addr sp (0x090#12) 944 (by decide) (by omega) hsp1088
--                                        ^^^^^^^^^  proves `944 ≤ 1088` — GROUND, no variables
```
`sp` cancels; the goal is a ground numeric fact. `omega` is ~1000× overkill for `944 ≤ 1088`, yet is
called ~900×. The inline `have`s (`sp.toNat - 968 + 8 = sp.toNat - 960 := by omega`) DO need `sp`'s
bound — but there are only a *bounded set of distinct (imm, k) spill offsets* in the whole binary.

**The fix already exists and is unused.** `EvalSimCommon.lean` has named offset lemmas
(`epi_off430`, `epi_off420`, …) that bake the `decide`/`omega` in ONCE at their own definition
(paid once, cached in the olean). The row files ignore them and re-inline `spill_addr sp imm k
(by decide)(by omega) h` at every site.

## Where the 132 omegas actually go (EvalGtRow, exact breakdown)

- **10** = ground `spill_addr … (by decide)(by omega) hsp1088` address args (`K ≤ 1088`). Trivially
  `decide`-able — but only 8% of the tax.
- **~122** = per-site **store/read SAFETY side-conditions**: after `rw [haddrK]` normalizes the
  address to `sp.toNat - K`, an `omega` (using `hsp1088 : 1088 ≤ sp.toNat` + `sp.isLt`) proves it is
  in-bounds / `≠ tohost` / disjoint, or a `show sp.toNat - K + i = … from by omega` re-indexing.
  These use the `sp` variable so they are NOT `decide`-able — but they are the **same shape ~122×**.

Conclusion: a plain `omega→decide` sed is insufficient (touches only the 10). The bulk is a single
reusable obligation instantiated ~122×. That is exactly what one lemma (omega paid ONCE) or SegEval's
first-order safety predicate collapses.

## Thesis — pay each arithmetic fact ONCE, reference by name; then route through SegEval

Three waves, cheapest-first, each measured against the 226s baseline:

- **P0a (trivial): `spill_safe` reusable lemma.** One lemma
  `spill_safe : 1088 ≤ sp.toNat → K ≤ 1088 → <store-safety-pred> (sp.toNat - K)` (and its
  `≠ tohost` / re-index siblings), omega proven ONCE inside. Rewrite the ~122 `(by rw […]; omega)`
  sites → `spill_safe hsp1088 (by decide)`. **~122 omega/file → ~0** (the omega is in the lemma,
  cached). This plus P0 below is the immediate measured win on the cohort.

- **P0 (immediate, mechanical, low-risk): `SpillOffsets.lean`.** Enumerate the *finite* distinct
  `(imm → k)` spill offsets used across the cohort; emit one named zero-`omega`-at-callsite lemma
  per offset (`spillOff_944 sp hsp : ((sp-1088)+sext 0x090).toNat = sp.toNat - 944`). The `omega`/
  `decide` is paid ONCE per distinct offset (~20–40 total) at definition, cached. Then mechanically
  rewrite every `spill_addr sp IMM K (by decide)(by omega) h` → `spillOff_K sp h`. **~900 omega
  calls → ~30.** Generated by a metaprogram (`experiments/gen_spill_offsets.py`) that scans the
  cohort for the (imm,k) set — no hand enumeration. Expected: 226s → tens of s per file.
- **P1 (structural, the plan's intent): route the cohort through `#derive_case`/SegEval.** These
  files are hand-threaded `EvalE`/`EvalBin` cases; the plan's L1/L2/L3 (`seg_eval`+`marshal`+
  `#derive_case`) is *exactly* what replaces the spill/address/store threading AND the
  `instantiate metavars` blowup (canonical write-log NF, rule 5). Once P0 proves the multiplier on
  one file, migrate the cohort to `#derive_case` rows so the `omega`/`rewriteSeq` bodies vanish
  entirely, not just the arithmetic tax.

## The omega-shape taxonomy (build one lemma per shape → kills all instances, all 7 files)

Inventory of `rows/EvalGtRow.lean` (the cohort is near-identical, so shapes are shared):

| shape | callsite pattern | count | helper | status |
|-------|------------------|------:|--------|--------|
| spill load/store safety (high addr) | `(by rw [haddrK]; omega)` ×3 + htif | ~45 | `spill_load_safe4/8` (SpillSafe.lean) | **DONE (green)** |
| spill `spill_addr` K≤1088 arg | `spill_addr … (by decide)(by omega)` | 10 | `(by decide)` | trivial |
| expr-relative load (`aExpr+n`) | `(by rw [hop8/hline4]; omega)` | ~8 | `expr_load_safe` (hexprLo/hexprHi bounds) | TODO |
| low-addr slot/cs site | `(by rw [hslotAddr/hcsAddr…]; left; omega)` | ~6 | `slot_load_safe` (Or.inl variant) | TODO |
| code-region disjointness | `(by rcases hcodeStk with h\|h <;> omega)` | ~5 | `code_disjoint` | TODO |
| value-region disjointness | `(by rcases hviStk with h\|h <;> omega)` | ~5 | `vi_disjoint` | TODO |
| frame-agreement window | `read*_agreeP … (fun j hj => ⟨by omega, by omega⟩)` | ~8 | `frame_window` | TODO |
| loop-counter arithmetic | `show _ = c.steps + N; omega` | ~4 | inline `by decide`/lemma | TODO |

Each helper is proven ONCE (omega compiled into its olean); migrating a cohort file replaces the
callsite tactic with a by-name application. Because the 7 `Eval*` files share these shapes, the 7
helpers × migration kills the full ~900-omega, ~13-min aggregate tax. Execution: build the 6
remaining helpers (spine, serial), then FAN OUT the migration — the `Eval*` files are near-leaves
(nothing imports them) and disjoint, so dispatch worktree-isolated subagents (Wave-D protocol,
≤2–3 concurrent `lean`, coordinator merges serially) one per file, each given the helper API + this
table + "replace omega-bearing tactic blocks by-name, build green, axiom-clean, re-profile."

## What we ruled out (measurement corrected the guesses)

- **NOT the code image.** `Eval_expr.lean` (12.4k lines of `mem[a]?=some b` conjunctions) is 12s,
  no decl >100ms; blast radius only 6% of the tree. A ReflCode/RArray rewrite is a *volume/clean-
  build* nicety (kills ~22k redundant lines, helps CI) but is **not** the iteration wall. Deferred.
- **NOT the site batteries.** `StrcmpSites` (714 `decide`) is 3s — raw ground `decide`s are cheap.
- **NOT rebuild amplification for the cohort.** The `Eval*` files are near-leaves (nothing imports
  them); editing one only rebuilds itself → fast to iterate the fix on. (Separately, the *spine* —
  `ElfBytes`/`Elf`/`InitValues`, ~69% reverse-dep — should stay minimal/stable; the god-module
  `Vsa.lean` with 359 imports and the depth-41 critical path cap parallelism at ~21× and are a
  secondary clean-build lever, not today's target.)

## Metaprograms & tools (the multipliers)

- **`scripts/elab_profile.sh` — DONE.** Serial per-file wall + per-decl profiler; `pkill lean`
  between files; appends `experiments/elab-timings.tsv`. Rule 7 (the elab budget) mechanized. Gate
  every cohort commit: the touched file's wall must DROP (P0) and never regress >10% after.
- **`experiments/gen_spill_offsets.py` (P0)** — scan the cohort for the `spill_addr … IMM K` set,
  emit `SpillOffsets.lean` (named lemmas) + a sed-map rewriting call sites.
- **`#derive_case`/`#derive_segment` (P1, extends in-flight L3)** — the structural replacement.
- **elab-budget CI hook** — wire `elab_profile.sh` into `scripts/check_all.sh`.

## Resource discipline (unchanged, non-negotiable — from RESUME-after-restart.md)

- **SERIAL builds only.** One `lean` at a time; `pkill -9 lean` before each; watch
  `pgrep -x lean | wc -l`. NEVER parallel `lake` (corrupts `.lake` → the Cli re-clone breakage).
- The **generator rewrites and lemma designs are build-free** — those CAN be fanned out to
  subagents in parallel (they emit `.lean`/`.py`); the coordinator verifies each serially.
- Keep the old proof until the new is green; delete in the same commit; gate on `check_all.sh` +
  axioms ⊆ {propext, Classical.choice, Quot.sound} + no elab regression.
