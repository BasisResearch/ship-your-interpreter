# Straggler-file elaboration migration — 3 measured-heavy files

Companion to `experiments/elab-wall-strategy.md`. That doc tackled the `rows/Eval*` cohort
(omega tax). This pass targets three DIFFERENT stragglers whose cost turned out to be
`simp`/`omega` shapes NOT covered by the SpillSafe/OmegaHelpers family. All numbers are
**profiler CPU-time** (`-Dprofiler.threshold=10`, summed by category) — the only
contention-robust metric available (a concurrent migration agent was compiling in parallel,
which made bare wall/user-time A/B unusable; see "measurement notes").

## Results (profiler total-tactic-time, before → after; 2 after-runs agree)

| file | shape found | before | after | delta | status |
|------|-------------|-------:|------:|------:|--------|
| `EnvGetSpec4.lean`   | `cases R <;> simp_all` (33-way × heavy simp_all) | simp 56.2s / total 56.7s | simp 0 / total 0.4s | **−99%** | LANDED |
| `EvalCallNative2.lean` | ~245 term-mode `by omega` in one ~600-line theorem | omega 52.3s / total 75.8s | omega 27.1s / total 50.1s | **−34%** | LANDED |
| `EvalSimCommon.lean` | 3708 chunk-transfer `simp_all only []` | simp 39.6s / total 66.7s | (unchanged) | resisted | REVERTED |

Wall-clock (touched, warm oleans, contention-affected): EvalCallNative2 ~49s; EnvGetSpec4
~1.6s; EvalSimCommon ~50s. All three green, statements byte-identical, axioms ⊆
{propext, Classical.choice, Quot.sound}.

## What each shape was, and what was added where

### 1. `EnvGetSpec4.lean` — the big win (56.7s → 0.4s tactic time)

Root cause was NOT omega/decide (this file isn't in the census top-25 for a reason): a single
line `cases R <;> simp_all [AbiPreserved]` (inside `env_get_scan_body`'s `hghost4`) proving
`(Register.x1 == R) = false` from `hR : AbiPreserved R = true`. `cases R` fans out ~33
Register constructors and `simp_all` re-scans the enclosing ~150-hypothesis context on each →
712 simp invocations, 56s. Replaced in place with the 3-line decidable-contradiction idiom
(the body of `EnvNewSpec.abi_ne`, inlined because `abi_ne` isn't importable from here without a
new cross-import):

```lean
have hx1 : (Register.x1 == R) = false := by
  rcases hb : (Register.x1 == R) with _ | _
  · rfl
  · rw [beq_iff_eq] at hb; rw [← hb] at hR; exact absurd hR (by decide)
```

No `cases R`, no `simp_all`. **Lesson:** `cases <Register> <;> simp_all` in a large proof
context is a 50s+ footgun; the profiler flags it as a huge `simp` count with tiny source
footprint. Grep the tree for other `cases R <;> simp` sites — likely more of these.

### 2. `EvalCallNative2.lean` — omega-cluster migration (75.8s → 50.1s)

One ~600-line theorem (`nativeAssertInternal`) with ~245 term-mode `by omega`, each ingesting
the theorem's full linear-arith context (~150 hyps) even for trivial goals. Sorry-bisection
(on a `/tmp` scratch copy) isolated where the cost actually sits — it was NOT uniform:

- **store-safety `site_*_na` args (~25s)** — 4 preconditions per store site, each a
  `(by rw [haddrK]; …; omega)` over the store address. Collapsed via a new bundled lemma
  `naStore_safe4` (omega compiled once) → each site passes 4 projections, no omega.
- **`hbufout` window-disjointness (~5s)** — `getElem_writeMap8_disjoint … (by omega)` for
  addresses outside `[fsp-80, fsp+40)`. New `winStore_disjoint`.
- **stack re-index `show fsp-64+d = fsp-80+d' from by omega` (~7s over 16 sites)** — new
  `reidxNat` (saturating-subtraction re-index, omega once).
- **cheap clusters left as-is / trivially swapped**: 36 aligned-slot-disjoint omegas
  (→ `slotStore_disjoint`, net-neutral, tiny context) and 22 `habm0 N (by omega)` literal
  `N < 24` bound checks (→ `by decide`, ignores context). These were the CHEAP omegas —
  swapping them barely moved the needle, confirming the sorry-bisect diagnosis that cost
  concentrates in the big-context store-safety args.

All new lemmas live in the new file **`Vsa/Sim/OmegaHelpers2.lean`** (own olean, nothing else
imports it yet — safe to write): `reidxNat`, `reidxNat0`, `winStore_disjoint`,
`slotStore_disjoint`, `naStore_safe4`. `EvalCallNative2` imports it.

**Dead end recorded:** precomputing the 9 `naStore_safe4` bundles into top-level `have hnsK`
(to avoid the 4×-per-site inline recompute) caused a `whnf` heartbeat TIMEOUT — the `_`
address placeholder in a `have` triggers a deep-whnf unification blowup. The inline-projection
form works because the `haddrK` argument pins the address by matching the goal directly. Kept
inline; the 4× recompute is cheap (typecheck only, no omega).

### 3. `EvalSimCommon.lean` — RESISTED (reverted to original)

Cost is `loaded_eval_expr_agreeP`: 58 `eval_exprChunkN` transfers, each
`simp only [chunkN] at cN ⊢; repeat' apply And.intro; all_goals (rw [← ha]; simp_all only [])`.
This splits into 57×64 + 3768 = ~3708 goals, each closed by a `simp_all only []` (~10ms warm).
Tried:
- **`clear` other chunk hyps before the closer** — under COLD compile it cut simp 58s→<10ms/call,
  but under WARM oleans (the real steady state) each `simp_all` is already <10ms and the
  profiler shows the SAME 3708 calls / 39s simp. Net zero; the apparent "83→43s" was a
  cold-vs-warm + contention artifact.
- **destructure `cN` (obtain ⟨64⟩) + `assumption`** — cut simp 39s→0.6s but the 57×64-conjunct
  `obtain` cost 25s AND total tactic time BALLOONED to 168s (huge proof terms). Net loss.

The 3708 simp/obtain calls are intrinsic to the split-and-close structure over a
3712-conjunct membership predicate. A real fix needs reflecting `eval_exprChunk` into a
first-order form (out of scope / high-risk for a straggler pass). **Reverted to original,
byte-identical.**

## Measurement notes (why profiler-time, not wall)

- A concurrent agent compiled `rows/Eval*` throughout; bare `time lake env lean` swung
  50s↔100s+ for the SAME file. Profiler CPU-time-in-category (summed) is the contention-robust
  proxy — it measures work done, not clock.
- `lake env lean <file>` short-circuits (~2s) if the source hash matches a recent in-session
  success; **always `touch` before a timed run** or the measurement is a stale-cache lie. Two
  early false readings (a "1.6s" EvalSimCommon) came from this.
- Profiler `simp`/`omega` aggregate lines only surface at moderate thresholds and when the
  category actually exceeds it; the Firefox-format `-Dtrace.profiler.output` JSON is
  sampling-based (no per-tactic source positions) — use sorry-bisection on a `/tmp` copy to
  localize expensive tactic instances instead.
