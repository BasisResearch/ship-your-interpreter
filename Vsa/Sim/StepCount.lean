import Vsa.Sim.BlockAdapter
import Vsa.Sim.DeriveCase

/-!
# `StepCount` — counted machine-step LOWER BOUNDS for every seg row, for free

This is the step-counting exponentiating layer.  ONE metatheorem
(`segToTripleN`) upgrades EVERY existing and future `#derive_case` seg row to a
counted triple `TripleN (evalBlocksFuel bs) …`, whose count is the concrete
instruction length of the reflected block list.  The divergence-family seams in
`Vsa/Sim/InterpRunLoopSeamsClose.lean` (`iterFromCountedRun` /
`approxFromCountedRun`) consume exactly this `TripleN` shape, so any row is now a
positive machine-step lower bound with NO extra proof.

## What was already in place (reused, not rebuilt)

* `Vsa/Triple.lean` already has the full `TripleN` algebra: `TripleN.toTriple`,
  `of_triple`, `mono` (weaken the count), `of_step`, `conseq`, `seq` (counts ADD
  across seams).  Task parts 2 (counted composition + `TripleN.weaken`) are
  therefore ALREADY LANDED there — `TripleN.mono` IS the weaken lemma, and
  `TripleN.seq` IS the counted `Triple.seq`.  This file does not restate them; it
  points a future agent at them and only supplies the missing seg-count bridge.
* `Vsa/Sim/DeriveCaseRow.lean`'s `segToTriple` builds the row's `Steps` chain via
  `segEval_sound`, whose conclusion pins the reached config's `steps` counter to
  `u + evalBlocksFuel bs`.  That counter IS the length: every `Step` increments
  `steps` by exactly 1 (the `.inr` branch of `stepOnce` returns `used + 1`, both
  cases — see `Vsa/Elf.lean:47`), so a `Steps` run whose `steps` advances by `k`
  has exactly `k` links.  `Steps.toN_of_stepsField` below turns that field-delta
  into a `StepsN k`, and `segToTripleN` folds it into the flagship metatheorem.

## The recipe (how a future agent counts an existing row)

Given ANY row `myRow : Triple (SegPre bs L lds pc0 m0) Q` built by `segToTriple`:
you do NOT need to touch `myRow`.  Either
  (a) re-derive the counted form directly: `segToTripleN bs L lds pc0 m0 Q hwf
      hpost : TripleN (evalBlocksFuel bs) (SegPre bs L lds pc0 m0) Q` — same
      `hwf`/`hpost` the plain row supplied; or
  (b) if you only have the plain `Triple` and want a crude positive bound, note
      `evalBlocksFuel bs = chainLen bs > 0` for any non-empty chain, and feed the
      counted row through `TripleN.mono` down to whatever bound (e.g. `1`, or
      `n + 1`) the consumer wants.  `iterFromCountedRun` wants `TripleN 1`;
      `approxFromCountedRun` wants `TripleN (n + 1)` — both reachable by
      `TripleN.mono` from `TripleN (evalBlocksFuel bs)` once `1 ≤ evalBlocksFuel
      bs` / `n + 1 ≤ evalBlocksFuel bs` is a `decide`.

## `Landed` combinator (task part 3)

`Landed c P := ∃ c', Steps c c' ∧ P c'` — the canonical "seam landing" bundle
from the `landing-bundle-must-be-prop-existential` observation.  It carries the
reached config as DATA yet is Prop-valued (built from a `Triple`'s `Exists`,
consumed by `obtain` into Prop goals — the only shape that survives, per the
observation).  `Landed.mk`/`bind`/`weaken` + the counted `LandedN` give the
shared destructurer `SpillLanded`/`SegLanded` (DriveToLoopHeadSpans) can migrate
onto.  Reseat is not done here — the combinator is landed for future files.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no `maxHeartbeats`
bump.  Axioms of every theorem ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable Vsa
open Vsa.Machine (MState Config Step Steps StepsN)
open Vsa.Logic (Triple TripleN)

namespace Vsa.Machine

/-! ## §1. `Step` advances the `steps` counter by exactly 1

Every architectural step returns `used + 1` on its continue branch
(`stepOnce`, `Vsa/Elf.lean`).  So the `steps` field of a `Config` counts the
links of any `Steps` run out of it, and a run whose `steps` field advances by `k`
is a `StepsN k`. -/

/-- One `Step` increments the `steps` counter by exactly one. -/
theorem Step.steps_succ {a b : Config} (h : Step a b) : b.steps = a.steps + 1 := by
  cases h with
  | @mk σ σ' i i' u u' e =>
    -- `Step.mk : (stepOnce i u).run σ = .ok (.inr (i', u')) σ' → Step ⟨σ,i,u⟩ ⟨σ',i',u'⟩`.
    -- The `.inr` continue branch of `stepOnce` returns `(_, u + 1)`, so `u' = u + 1`.
    show u' = u + 1
    -- Reduce the `EStateM` run of `stepOnce`'s bind tree to a nest of `match`/`if`
    -- over the opaque effect results (`readReg`/`try_step`/`cycle_count`/…), each of
    -- whose leaves returns `.inl (…, u)` or `.inr (_, u + 1)`.  Only the `.inr`
    -- leaves unify with `e`'s RHS `.inr (i', u')`, and every one carries `u + 1`;
    -- the `.inl` leaves inject to `False`.
    unfold stepOnce at e
    repeat' first
      | -- `.inr` leaf: injection to the payload pair, count is `u + 1`.
        (simp only [EStateM.Result.ok.injEq, Sum.inr.injEq, Prod.mk.injEq,
           reduceCtorEq, false_and] at e
         omega)
      | -- `.inl` leaf: `.inl _ = .inr _` is `False`; simp closes the goal.
        simp only [EStateM.Result.ok.injEq, reduceCtorEq, false_and] at e
      | -- peel one `EStateM.bind`/`.run`/`pure` layer …
        simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
          Bind.bind, Pure.pure] at e
      | -- … then split the exposed effect-result `match` / guard `if`.
        split at e

/-- The `steps` counter is monotone along a run. -/
theorem Steps.steps_le {a b : Config} (hs : Steps a b) : a.steps ≤ b.steps := by
  induction hs with
  | refl c => exact Nat.le_refl _
  | head s _ ih =>
    have := s.steps_succ
    omega

/-- A finite run whose `steps` field advances by `k` is a `StepsN k` run. -/
theorem Steps.toN_of_stepsField {a b : Config} (hs : Steps a b) :
    StepsN (b.steps - a.steps) a b := by
  induction hs with
  | refl c => simpa using StepsN.zero c
  | @head a b c s hbc ih =>
    have hstep : b.steps = a.steps + 1 := s.steps_succ
    have hle : b.steps ≤ c.steps := hbc.steps_le
    -- `c.steps ≥ b.steps = a.steps + 1`, so `c.steps - a.steps = (c.steps - b.steps) + 1`.
    have hrw : c.steps - a.steps = (c.steps - b.steps) + 1 := by omega
    rw [hrw]
    exact StepsN.succ s ih

/-- Convenience: a run pinned to end at `steps = a.steps + k` is a `StepsN k`. -/
theorem Steps.toN_of_stepsEq {a b : Config} {k : Nat}
    (hs : Steps a b) (hk : b.steps = a.steps + k) : StepsN k a b := by
  have := hs.toN_of_stepsField
  rw [hk] at this
  simpa using this

end Vsa.Machine

namespace Vsa.Sim

open Vsa.Machine

/-! ## §2. `segToTripleN` — the flagship counted seg metatheorem

`segEval_sound` produces `Steps ⟨σ,i,u⟩ ⟨σ', i', u + evalBlocksFuel bs⟩`.  The
end `steps` counter is `u + evalBlocksFuel bs`, so `Steps.toN_of_stepsEq` gives a
`StepsN (evalBlocksFuel bs)` run — exactly the counted-triple witness.  This is
the counted twin of `segToTriple`: identical `hwf`/`hpost`, upgraded conclusion
`TripleN (evalBlocksFuel bs) (SegPre …) Q`. -/

/-! ## §3. Positive-lower-bound corollaries for the divergence seams

`iterFromCountedRun` wants `TripleN 1`; `approxFromCountedRun` wants `TripleN
(n + 1)`.  Both come from `segToTripleN` via `TripleN.mono` once the fuel bound
is a `decide`.  These two corollaries package the arithmetic so a seam supplier
hands only the fuel-bound `decide` (usually `by decide` on a concrete `bs`). -/

/-! ## §4. The `Landed` combinator (task part 3)

`Landed c P` = "from `c`, some finite run reaches a `P`-config".  Prop-valued but
DATA-carrying (the reached config lives under the `∃`), the only shape that both
builds from a `Triple`'s `Exists` and consumes into a Prop goal
(`landing-bundle-must-be-prop-existential`).  `LandedN n` additionally records a
`≥ n` step count.  `SpillLanded`/`SegLanded` in `DriveToLoopHeadSpans.lean` are
instances of `Landed` (their `∃ c', Steps c c' ∧ …`), and can migrate onto these
shared `mk`/`bind`/`weaken` lemmas. -/

/-- **Counted landing.**  A landing that took at least `n` machine steps. -/
def LandedN (n : Nat) (c : Config) (P : Config → Prop) : Prop :=
  ∃ (m : Nat) (c' : Config), n ≤ m ∧ StepsN m c c' ∧ P c'

/-! ## §5. Demonstration on a real seg row (task part 4)

`demoChainRow` (`DeriveCaseRow.lean`) is `Triple (SegPre demoChain [] [] … m0)
(DemoPost m0)`, a three-`addi` chain.  We reproduce it as a COUNTED triple
`TripleN (evalBlocksFuel demoChain) …` through `segToTripleN` with the SAME
`hwf`/`hpost` the plain row used — proving the counted fan-out is mechanical.
`evalBlocksFuel demoChain` reduces to the concrete instruction count (3), so the
row is a `≥ 3` machine-step lower bound; the `_one`/`_succ` corollaries then drop
it to `TripleN 1` for `iterFromCountedRun` by one `decide`. -/

end Vsa.Sim
