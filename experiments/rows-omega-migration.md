# P0a rows omega-migration — NEGATIVE RESULT (helpers do not win on the refactored cohort)

Task: migrate the per-site `omega` tactic blocks in the hot `Eval*` row/sim cohort to the
by-name helper lemmas (`SpillSafe.lean` / `OmegaHelpers.lean`), so each site typechecks
instead of re-running omega.

**Outcome: reverted all target files to baseline. The migration is a measured net loss (or
noise-level neutral) on every target, because the premise that motivated it no longer holds
for these files.** All measurements below are `time lake env lean <file>` from repo root,
serial, one lean at a time, warm oleans (concurrent profiler running → ~10% wall variance;
`user`-time is the more stable metric and is what the deltas are read from).

## Why the premise no longer holds

`experiments/elab-wall-strategy.md` measured `rows/EvalGtRow.lean` at **226s / 2021 lines /
132 omega**, of which a throwaway `omega→sorry` probe attributed **~51% (115s) to omega**, and
concluded: build helper lemmas, pay omega once, apply by name.

Since that measurement the cohort was **refactored**: the heavy straight-line/ladder omega work
was extracted into per-operator `EvalGtChain.lean` / `EvalLeChain` / … lemmas
(`evalGtChain_run`, `evalGtLadderC/D/EF/G`, etc.), which are compiled ONCE into their oleans.
Today `rows/EvalGtRow.lean` is **838 lines / 125 omega / ~51s warm**. The omega that survives
in the row files is the *cheap residue* (address/reindex facts with a small hypothesis context);
the expensive omega already lives in the extracted-lemma oleans and is paid once there.

An `omega→sorry` probe on the CURRENT `EvalGtRow` still shows omega is ~90% of the file's 51s
(51s→5.3s all-sorry; 51s→23s when only the 33 grouped-safety `(by rw […]; omega)` args are
sorried). So omega is still the cost — but **replacing those omegas with by-name helper
applications costs as much or more than the omega it removes**, because the helper application
must unify a 4-conjunction stated over `(v2 + sign_extend imm).toNat` / `writeMap8` terms and
force `whnf` on them, and (for the store/load groups) marshal 4 projections per site.

## Measured before/after (user-time, back-to-back baseline↔migrated pairs)

| file | baseline (user) | migrated (user) | shapes migrated | verdict |
|------|------:|------:|-----------------|---------|
| `rows/EvalGtRow` | 55–59s | 56–62s | spill_addr(10)+code_disjoint(5)+vi_disjoint(5) | **slower ~4–6s** |
| `rows/EvalGtRow` (disjoint-only, no spill_addr) | 58.9s | 57.1s | code_disjoint(5)+vi_disjoint(5) | neutral (noise) |
| `rows/EvalGeRow` | 50.8s | 56.0s | spill_addr(10)+code_disjoint(5)+vi_disjoint(5) | **slower ~5s** |
| `EvalLogical4` | 90.9s | 95.0s | spill_addr(10) | **slower ~4s** |
| `EvalLogical3` | 94.5s | 90.8s (2nd run); 66.7s (1st, low-load outlier) | spill_addr(10) | neutral (noise) |

`rows/EvalLeRow` (41.8s), `rows/EvalLtRow` (43.3s), `rows/EvalSubRow` (42.3s),
`rows/EvalAddRow` (45.1s) were also migrated to green + axiom-clean with the same three shapes
(+`vi_disjoint_int` for the two arithmetic rows, whose value region is `value_int`
`[0x8000280c,0x8000281c)` not `value_bool`), but given Gt/Ge show the identical shape-set
regresses, they were reverted with the rest rather than measured pairwise.

### Root cause of the regression, isolated

Two clean A/B facts pin it:
1. **disjoint-only (`code_disjoint`+`vi_disjoint`, replacing the two-branch
   `rcases hStk <;> omega`) is NEUTRAL** — 58.9s→57.1s. Replacing a 2-branch omega with a
   by-name lemma neither helps nor hurts measurably.
2. **`spill_addr … (by omega) → (by decide)` (10 ground `K ≤ 1088` args) REGRESSES** — it is the
   component that pushes Gt/Ge/Logical4 ~4–6s slower. The `decide` on `K ≤ 1088` in the row
   files' hypothesis context is apparently *slower* than the `omega` it replaced (or destabilises
   a downstream elaboration), despite the strategy table listing it as "trivial `by decide`".

### A failed richer attempt (recorded so it isn't retried)

Migrating the ~33 grouped LOAD/STORE safety args (`(by rw [hop8]; omega)` etc. — the a/b/c/d/e
`hlo/hhi/hhtif/hal` preconditions of `evalGtChain_run`/`evalGtLadder*`) to
`spill_load_safe4/8` / `expr_load_safe4` / new `spill_store_safe4/8` conjunctions, bound as
`have`s and projected `.1/.2.1/.2.2.1/.2.2.2`:
- Binding the conjunctions as `have`s **blew up to 220s** (4M→timeout): every downstream omega
  (~70) sees the extra conjunction hypotheses and enumerates their atoms. `clear`-ing the
  `have`s immediately after each `obtain` fixes the blowup but nets **63s (vs 51s baseline)** —
  a loss. Inlining (no `have`, 4 helper copies per group) also nets a loss.
- Nuance found & needed for any future attempt: the SAME spill offset has DIFFERENT span/alignment
  in different callers (e.g. `0x090→944` is 4-byte `%4` in `evalGtChain_run` but 8-byte `%8` in
  `evalGtLadderD`), and store sites take a PLAIN `tohostAddr+16 ≤ addr` htif (not the `Or.inr`
  disjunction of loads) — so helpers must be chosen per (offset, span, load/store) context.

## Recommendation

The by-name-helper (P0a) lever **does not move the needle on the current, already-refactored
cohort** — the win it was designed to capture was captured by the earlier Chain-lemma
extraction. Two forward options, both outside P0a:

- **P1 (structural, the plan's real intent):** route these hand-threaded rows through
  `#derive_case`/SegEval so the omega/rewriteSeq bodies vanish entirely (canonical write-log NF),
  rather than swapping one ground tactic for another.
- If iteration wall is the concern, the remaining lever is the *spine/critical-path* clean-build
  structure (god-module `Vsa.lean`, depth-41 path), not per-site omega in these near-leaf rows.

`SpillSafe.lean` and `OmegaHelpers.lean` are left unchanged (baseline); no target file was
modified. Axiom discipline held throughout — every experimental compile was
`[propext, Classical.choice, Quot.sound]`-clean, no `sorry`/`axiom`/`native_decide`/`bv_decide`
in any retained state (the `sorry` substitutions were throwaway probes only).
