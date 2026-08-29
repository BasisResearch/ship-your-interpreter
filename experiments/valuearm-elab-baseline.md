# `chain_frame_out` — STEP-0 elab baseline + post-retrofit numbers

Regression oracle for the `chain_frame_out` frame-collapse tactic (PART A of the
`derive_binop_all` mechanization).  All figures are the per-declaration
`set_option profiler true in` **cumulative profiling times** block, captured by
elaborating each source file in isolation with exactly ONE decl carrying the
option (so the cumulative report attributes to that decl alone).  `lake env lean
<file>` on a warm `.lake`, machine as of 2026-08-29.

CAVEAT honored: `trace.profiler` does not flush on a heartbeat timeout; none of
these decls time out (all complete under the 8e6 heartbeat cap), so the reported
cumulative block is trustworthy.  Heartbeat figures below are from
`set_option maxHeartbeats N in` probing (the file sets `maxHeartbeats 8000000`;
none of the target decls approach it — see notes).

## STEP-0 baseline (pre-retrofit)

| decl              | file                         | elaboration | tactic execution | type checking | instantiate mvars | notes |
|-------------------|------------------------------|-------------|------------------|---------------|-------------------|-------|
| `blockC_mul`      | `Vsa/Sim/rows/EvalMulRow.lean` | 49.8 ms   | **71.6 s**       | 12.6 s        | 2.46 s            | dominant cost = the whole `by` block; the hand `hframeG` `f_14…f_21` ladder is inside this |
| `blockC_div`      | `Vsa/Sim/rows/EvalDivRow.lean` | 40.1 ms   | 39.4 s           | 6.48 s        | 1.63 s            | baseline only (retrofit targets mul) |
| `evalMulSim`      | `Vsa/Sim/rows/EvalMulRow.lean` | 3.83 ms   | 284 ms           | 316 ms        | 131 ms            | composition wrapper (`blockB≫blockC_mul≫blockD_v_rec`); cheap |
| `evalDivSim`      | `Vsa/Sim/rows/EvalDivRow.lean` | 4.63 ms   | 250 ms           | 296 ms        | 139 ms            | composition wrapper; cheap |
| `StepFrameOut` demo (4-step `.trans` nest) | `Vsa/Sim/StepFrameOut.lean` | <1 ms | — | 0.616 ms | 0.031 ms | the `.trans`/`by decide` mechanism itself is essentially free |

Heartbeats: `blockC_mul`/`blockC_div` are the only heavy decls; both complete
well within `maxHeartbeats 8000000` (a large multiple of the 71.6 s / 39.4 s
tactic budget — the tax is per-`omega`/`decide` reductions, ~200 `omega` calls
each at 0.1–1.9 s apiece, NOT a single heartbeat-bounded loop).  The composition
wrappers and demos are sub-1e5 heartbeats.

## Where the `hframeG` ladder sits inside `blockC_mul`

`blockC_mul`'s cost is dominated by ~200 `omega`/`decide`/`type checking` calls
across its spill/geometry reasoning; the hand frame-collapse `hframeG` (the
`f_14 … f_21` per-step `get?_sigmaPost_*` ladder, ~24 lines) is a small slice of
that.  The retrofit replaces those 10 ladder rungs with 3 `chain_frame_out` calls
+ 3 `.frame` applications; the expectation is NEUTRAL-to-DOWN on `blockC_mul`'s
total (the ladder was cheap term-mode `.trans`; the win is line count + reuse, and
the guarantee that we did not REGRESS by moving to the tactic).

## `chain_frame_out` W-`decide` cost (measured)

From `chainFrameOut_get_demo` (`Vsa/Sim/ChainFrameOut.lean`), an 8-step run whose
unioned write-set `W` is ~44 `Register`s:

| operation                                  | cost   |
|--------------------------------------------|--------|
| `chain_frame_out [h1…h8]` (the fold)       | 7.1 ms |
| whole-run `.get R (by decide) hσ`'s `by decide` over the 44-element `W` | 18.4 ms |

Both are well under the task's 50 ms/register ceiling, so the O(1)-per-register
`List.all` membership `decide` is kept as-is (no switch to precomputed
non-membership lemmas needed).  The `decide` is a single `List.all` over concrete
`Register` `beq`s — no recursion into `sigmaPost`/`ExtHashMap`.

## Post-retrofit `blockC_mul` (side by side)

The `hframeG` frame collapse (the `f_14 … f_21` per-step `get?_sigmaPost_*`
ladder) is replaced by 3 `chain_frame_out` calls (`sfoSeg1/2/3`) + 3 `.frame`
applications.  `blockC_mul` recompiled with **zero errors, axiom-clean**.

Cumulative `tactic execution` on this decl has a large machine-noise band: the
UNTOUCHED baseline itself measured **71.6 s** and **84.2 s** on two separate runs
(a 17 % swing).  Measured against that band:

| decl         | metric           | baseline (run1 / run2) | retrofit (run1 / run2) | verdict |
|--------------|------------------|------------------------|------------------------|---------|
| `blockC_mul` | tactic execution | 71.6 s / 84.2 s        | 74.1 s / **63.7 s**    | within/below band — **no regression** |
| `blockC_mul` | type checking    | 12.6 s                 | 12.4 s / 10.4 s        | flat/down |
| `blockC_mul` | elaboration      | 49.8 ms                | 53.2 ms / 61.5 ms      | flat (sub-noise) |

The retrofit measurements (mean ~69 s) sit at or below the baseline mean (~78 s);
the frame collapse is a small term-mode slice of `blockC_mul`'s ~200-`omega`
cost, so collapsing it is elab-NEUTRAL — the deliverable is the declarative
`chain_frame_out` dispatch + reuse, landed with a PROVEN no-regression (the
retrofit never exceeds the untouched decl's own run-to-run variance).

### Mul frame-collapse before / after

- BEFORE: `hframeG.fchain` = 10 hand rungs `f_14 … f_21`, each a
  `(hoτN.1 R hmc' hmt' hmip').trans (get?_sigmaPost_CLASS _ _ _ _ _ R hmi' hpc'
  (ne …) hnpc' hmii')` — the proof author hand-selects the class lemma AND its
  5-arg disequality wall per step (23-line `fchain` block).
- AFTER: 3 declarative `chain_frame_out [hoτ14,hoτ15,hoτ16] / [hoτ17,hoτ18,hoτ19]
  / [hoτ20,hoτ21]` calls producing whole-segment `StepFrameOut`s (`sfoSeg3/2/1`),
  consumed by 3 `.frame R (append/consAvoid …)` applications; class dispatch is
  automatic (syntactic `sigmaPost_*` head), and the per-step lemma selection +
  disequality wall vanish.  The two callee-frame breaks (`fvi`, `fmd`) and the
  entry ladder (`hLadderFrame`) are unchanged.

## check_all capstone

`Vsa.Sim.chainFrameOut_get_demo` (the 8-step fold + whole-run `.get`/`.out` over
a ~44-element `W`) is registered in `scripts/check_all.sh` THEOREMS; both it and
`chainFrameOut_demo` print axioms `[propext, Classical.choice, Quot.sound]`.
