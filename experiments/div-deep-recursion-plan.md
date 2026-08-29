# Plan: kill the kernel deep-recursion in the multi-block `ChainFacts` assembly (div)

## ✅ RESOLVED (2026-08-28, `Vsa/Sim/SegFrameFactsAuto.lean`)

`divDispatch_facts` (the whole four-block `div` `ChainFacts`) now type-checks in
seconds, axiom-clean, **with no seal and no heartbeat bump** — `divDispatchRow_frame`
composes it into a live `Triple`.  Both are in `check_all` (Acceptance 2).

The plan's Fix 1a was **necessary but not sufficient**; instrumentation (per-leaf
`dbg_trace` + `IO.monoMsNow` timing, since `trace.profiler` doesn't flush on a heartbeat
timeout) found the dominant cost was **two** places, both fixed structurally in the
tactic — neither a seal, `native_decide`, nor `maxHeartbeats`:

1. **Per-leaf `hsrc`/guard `srcVal` `by rfl`** (the plan's Fix 1a).  Added
   `srcVal_runGM_ne` + the `srcval_peel` tactic: it peels the `runGM` pin tower
   layer-by-layer with the register-preservation lemma (`O(1)` structural per layer),
   replacing the `rfl` that reduced the whole tower.  Also discharges the divisor
   guard's `srcVal 17 L = Wr`.  (Caveat: `srcval_peel`'s `∀ a ∈ body, a.rd ≠ n` premise
   is FALSE for `n = 0` because stores carry `rd = 0`; don't peel the `x0` side of a
   guard — it's `0` definitionally anyway.)

2. **`sffNormMem`'s `g.change` (the actual blowup).**  Normalising a leaf's memory into
   the block-entry form via `g.change` runs `isDefEq(stepMemM-tower, writeLog M)`; on the
   THIRD cross-block load (2 `stepMemM` layers) `isDefEq` couldn't match heads and
   **whnf'd the RHS `writeLog M` fold** → the deep reduction.  Replaced with
   `sffPeelMemEq`: peel only the identity (non-store, decided by decoding `a.kind` ALONE)
   `stepMemM` layers via an EXPLICIT chained-`rfl` equation (each layer a one-step match
   reduction that never touches `writeLog`/`runGM`), lift by `congrArg` on the memory
   arg, and `replaceTargetEq` — no `isDefEq` on the fold.

The tactic now closes every frame window AND the two int-kind `bne` guards (`rfl` on the
bounded pin tower — `lookupG` short-circuits before any noncomputable `popByte` byte),
leaving exactly the seg's genuine semantic guard (`Wr ≠ 0`) for the caller — the plan's
predicted residual.  Every cross-block arm (div, and mod/eq/ne / recursive M4 arms whose
loads span stores) is now closed by the uniform `seg_frame_facts` tool.

Original plan (kept for provenance) below.

---


## Symptom
`divDispatch_facts : ∃ lds, ChainFacts σ.mem σ.mem (divDispL …) lds divDispatch`
elaborates only under a `local irreducible` seal on `wlogM`/`writeLog`, and then the
**kernel** (which ignores reducibility hints) hits *deep recursion detected* while
type-checking the assembled proof (~105s to even reach it). `eq` (one block) is fine;
`div` (four blocks) is not. Bumping the kernel stack is NOT a fix — it hides that the
proof term *requires* a deep reduction to type-check.

## Root cause (precise)
`ChainFacts` is defined by recursion on the block list and THREADS the machine state:

```
ChainFacts mc m L lds (b :: bs) =
  BBlockFacts mc m L lds b ∧
  ChainFacts mc (writeLog m (wlogM b.body L lds)) (runGM b.body L lds) (ldsRunM b.body lds) bs
```

So the *type* of a 4-block `ChainFacts` unfolds to a 4-deep `And` whose block-N
conjunct carries the accumulated

- memory `writeLog (writeLog (writeLog σ.mem (wlogM D1 …)) (wlogM D2 …)) (wlogM D3 …)`,
- pin list `runGM D3.body (runGM D2.body (runGM D1.body (divDispL …) …) …) …`,
- load stream `ldsRunM …`.

The kernel type-checks our nested `And.intro` against this unfolded type. Two places
force it to REDUCE these deep folds:

1. **Every leaf's `hsrc : srcVal a.rs1 L = base` proved `by rfl`.** For a later block,
   `L` is a nested `runGM` over the prior blocks; `rfl` reduces the *whole* tower to
   read out `x2`. This is `O(instructions-so-far)` deep reduction **per leaf**, and it
   recurses through `stepGM`/`eraseG`/`lookupG` **and** `mkLine` decode (a long
   `if`-chain) at every instruction. This is the prime suspect for the blow-up — the
   same `by rfl` is cheap for `eq` (one block, shallow `L`) and catastrophic by block 4.

2. **Seam mismatch: reduced vs. canonical threaded state.** If `chain_facts` /
   `sffNormMem` hand a leaf goal whose `m`/`L`/`lds` are in a *different* syntactic
   shape than the `ChainFacts`-recursion produces, the kernel reconciles the two by
   reducing both — again over the deep tower. (`sffNormMem` peels `stepMemM`; the peeled
   result must land EXACTLY on the canonical `writeLog m (wlogM b.body L lds)` the next
   `ChainFacts` layer expects, or the kernel reduces to bridge the gap.)

This is exactly the failure `fast-reflection-rules` rule 5 warns about
("canonical write-log normal form so seams compose by `rfl`") and rule 1
("reflect on the compact first-order model, never re-reduce the Sail-shaped state").

## Fix 1 — kill the per-leaf deep reduction (do this first; likely sufficient)

### 1a. Register-preservation lemmas (replace every leaf's `by rfl` hsrc)
We already have `srcVal_stepGM_ne` (a source read survives a `stepGM` on a different
`rd`). Lift it to the whole block and the whole chain, WITHOUT reducing the fold:

```
srcVal_runGM_ne  : (∀ a ∈ body, a.rd ≠ n) → srcVal n (runGM body L lds) = srcVal n L
srcVal_runChain_ne : (∀ b ∈ bs, ∀ a ∈ b.body, a.rd ≠ n) → srcVal n (runChain bs L lds) = srcVal n L
```
(both by induction, each step `srcVal_stepGM_ne`; the `∀ a, a.rd ≠ 2` premise is
`decide`-able on the concrete body — no `runGM` reduction).

Then change `frame_ld_read` / `frame_ld_read_thru` / `frame_sd_auto` to take `hsrc`
as a hypothesis the tactic discharges via these lemmas (`srcVal 2 L = base` becomes
`(srcVal_runChain_ne … ▸ h2pin)` where `h2pin : srcVal 2 (divDispL …) = base` is a
one-step `rfl` on the ENTRY pins, not the threaded `L`). No leaf ever reduces the
threaded pin list again.

### 1b. Canonical threaded-state form at every seam
Audit that the state handed to each leaf is the canonical
`writeLog m (wlogM b.body L lds)` / `runGM b.body L lds` / `ldsRunM b.body lds`:
- keep `sffNormMem`'s peel producing exactly the block-entry `writeLog …` form (it
  already targets this — verify with `set_option pp.all` that no `applyW`/`insert`
  tower leaks in);
- state `frame_ld_read_thru`'s conclusion memory as `writeLog m0 log` and confirm it
  unifies with the goal *syntactically* (m0, log as-is), never by reducing `writeLog`.

### 1c. Compose via a `chainFacts_cons` lemma, not the raw definitional `And`
```
theorem chainFacts_cons (b : BBlock) (bs) …
  (hb : BBlockFacts mc m L lds b)
  (hbs : ChainFacts mc (writeLog m (wlogM b.body L lds)) (runGM b.body L lds)
           (ldsRunM b.body lds) bs) :
  ChainFacts mc m L lds (b :: bs) := ⟨hb, hbs⟩
```
Building the proof as `chainFacts_cons leaf1 (chainFacts_cons leaf2 …)` makes the
kernel check each application by matching `hbs`'s type against the *stated* threaded
form — syntactic, no `ChainFacts`-unfold-and-reduce. (`chain_facts` can be adjusted to
emit this shape, or add a post-processing `chainFacts_cons`-fold.)

**Verification for 1:** re-run `divDispatch_facts` WITHOUT any seal or heartbeat bump;
expect it to type-check in seconds like `eq`. Instrument first (see below) to confirm
1a removed the dominant cost.

## Fix 2 — if 1 is not enough: reflect the whole chain through `SegEval`
`segToTriple` already proves a whole segment via the compact first-order `SegEval`
model (write-log list) + ONE soundness bridge (`segEval_sound`), so the kernel reduces
the *small* abstract state, never the nested Sail-shaped `writeLog`/`runGM`. Route the
`ChainFacts` obligation the same way: prove
`chainFacts_of_segEval : (SegEval-side facts) → ChainFacts …` once, and have the tactic
discharge the abstract obligations (decodes via `chain_facts`, windows via the frame
lemmas). Then `divDispatch_facts` never materialises the 4-deep threaded `And` type.

## Fix 3 — structural fallback: generalise the intermediate memory
Before assembling, `generalize`/`set` each block boundary state:
`set m₂ := writeLog σ.mem (wlogM D1.body … lds) with hm₂` (and `L₂`, `lds₂`), so blocks
2–4 are proved over opaque `m₂`/`L₂`. The kernel then treats them as variables and
cannot reduce the tower. Requires threading the `set` equations through `chain_facts`
(more invasive than Fix 1).

## Diagnosis harness (run before Fix 1 to pin the dominant cost)
1. `set_option maxHeartbeats 400000 in` a copy of `divDispatch_facts`, and replace all
   but block-1 leaves with `sorry`; add blocks back one at a time; watch where cost
   super-linearly jumps (isolates threading depth vs. a single leaf).
2. Temporarily give ONE store leaf's `hsrc` a `by rfl` vs. a preservation-lemma proof;
   diff the kernel time. Confirms 1a is the lever.
3. `count_heartbeats in` around the `#print axioms`-free theorem, and `#reduce`
   (guarded) the block-4 threaded `L` alone to measure its reduced size.

## Why this is the right shape (not a hack)
- No kernel-stack bump, no `native_decide`, no `maxHeartbeats` slop.
- Fix 1 makes the proof term *syntactically* well-typed at each seam (rule 5), so the
  kernel's lazy defeq never descends the tower — the cost becomes `O(#instructions)`
  flat, matching `eq`.
- The abstraction the read needed (`wlogM_store_offsets`/`wlogM_below`) and the
  cross-block reader (`frame_ld_read_thru`) are already landed and axiom-clean; Fix 1
  is the *analogous* move for the pin list (`srcVal_runGM_ne`) plus a canonical-form
  seam audit — small, local, and reusable for every multi-block arm (mod/eq/ne EVAL,
  the recursive M4 arms).
```
