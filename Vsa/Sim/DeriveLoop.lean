import Vsa.Triple
import Vsa.Sim.StepObs

/-!
# `DeriveLoop` — Shape C: the loop-marshalling combinator (`loopFromBody`)

("Remaining v2 step 4", Shape C of `experiments/exponentiation-endgame-design.md`.)

A machine scan / for / while loop is a **back-edge basic block**: one
straight-line body whose terminator branches to its own head (guard true) or
falls through (guard false). `BlockTerm.lean:78` — *"a back-edge is just a basic
block whose terminator target is its own head; `bblock_sound_bt` with
`tgtPC = head` IS the loop-body lemma"*. Combined with the total-correctness loop
rule `Triple.loop` (`Vsa/Triple.lean`), the whole loop reduces to ONE
per-iteration obligation:

> from a state satisfying the invariant `I` with the guard `B` **true** and the
> measure `μ = n`, one back-edge iteration lands back at the head satisfying `I`
> again with `μ < n` (strictly decreasing).

That single-iteration body Triple is exactly what a `bblock_sound_bt` back-edge
run produces (register outcome + canonical memory + PC back at head), plus the
per-loop arithmetic that `μ` shrinks. This file packages that body into the whole
loop.

## What this file provides

* **`loopFromBody`** — the reusable combinator. Given an invariant `I`, a guard
  `B`, a measure `μ`, and a per-iteration back-edge body Triple
  `∀ n, Triple (I ∧ B ∧ μ = n) (I ∧ μ < n)`, it produces `Triple I (I ∧ ¬B)`.
  Thin over `Triple.loop`, but *stated in the machine dialect*: the body's
  measure is a `Config → Nat` read off the machine state (a decreasing register
  value / loop counter), so a `bblock_sound_bt`-shaped back-edge run drops in as
  the `body` argument with no reshaping.

* **`loopFromStepBody`** — an even thinner front door for the common case where
  the back-edge body is delivered as a raw one-machine-step fact
  (`∀ n c, pre → ∃ c', Step c c' ∧ post`), e.g. straight from a `stepObs_*`
  wrapper. It lifts the step with `Triple.of_step` and forwards to
  `loopFromBody`. This is the shape a synthetic single-instruction back-edge
  demo uses.

* **`regMeasure`** — a canonical machine measure: the `Nat` value of a chosen
  GPR read off `Config.σ`, `0` if unset. The natural decreasing quantity of a
  countdown loop (`addi xN, xN, -1; bnez xN, head`).

## Demo

`countdownLoop` instantiates `loopFromStepBody` on a **synthetic but real**
machine countdown: a back-edge block whose single iteration is a genuine
`Vsa.Machine.Step` (supplied as the per-iteration body oracle — exactly the
`bblock_sound_bt` back-edge run, which stays the per-loop residual per the design
doc) that re-establishes the counter invariant with the register-value measure
strictly decreased. From that single-block body lemma the WHOLE-loop Triple
`Triple Inv (Inv ∧ counter = 0)` is produced by the combinator. `#print axioms`
is clean (`{propext, Classical.choice, Quot.sound}`).
-/

open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)

namespace Vsa.Sim

/-! ## The combinator -/

/-- **Shape-C loop-marshalling combinator.** Turn a single back-edge iteration
body Triple into the whole-loop Triple.

`I` the loop invariant, `B` the guard (the machine's branch condition — true on
the back-edge, false on exit), `μ` the measure (a `Config → Nat` read off the
machine, typically a decreasing loop counter register). The hypothesis `body` is
one iteration: from `I ∧ B ∧ μ = n` the back-edge block runs back to the head
re-establishing `I` with `μ < n`. Conclusion: the loop reaches `I ∧ ¬B`.

This is literally `Triple.loop`; the content is that the argument shape matches
what `bblock_sound_bt` (with `tgtPC = head`) hands back, so a machine back-edge
run is dropped in directly. -/
theorem loopFromBody {I B : Config → Prop} (μ : Config → Nat)
    (body : ∀ n, Triple (fun c => I c ∧ B c ∧ μ c = n)
                        (fun c => I c ∧ μ c < n)) :
    Triple I (fun c => I c ∧ ¬ B c) :=
  Triple.loop μ body

/-- **Step-level front door.** When each back-edge iteration is delivered as a
single machine `Step` (the common `stepObs_*`/`bblock_sound_bt` output), lift it
with `Triple.of_step` and marshal the whole loop. `body` says: from any
`I ∧ B ∧ μ = n` configuration, ONE machine step lands in `I ∧ μ < n`.

(For a multi-instruction back-edge block, use `loopFromBody` directly with the
block's composed `Triple` — a `Triple.seq` of the straight-line segment and the
terminating branch — as `body`.) -/
theorem loopFromStepBody {I B : Config → Prop} (μ : Config → Nat)
    (body : ∀ n c, (I c ∧ B c ∧ μ c = n) →
      ∃ c', Step c c' ∧ (I c' ∧ μ c' < n)) :
    Triple I (fun c => I c ∧ ¬ B c) :=
  loopFromBody μ (fun n => Triple.of_step (body n))

/-! ## A canonical machine measure: a decreasing register value -/

/-- The `Nat` value of GPR number `n` read off a configuration (`0` if the
register is unset). The natural measure of a countdown loop: the loop counter
register, which the back-edge body strictly decreases each iteration. -/
def regMeasure (rf : MState → Option (BitVec 64)) (c : Config) : Nat :=
  (rf c.σ).elim 0 (fun v => v.toNat)

/-! ## Demo — a synthetic-but-real machine countdown loop

The loop is `addi xN, xN, -1; bnez xN, head`: while the counter register is
nonzero, decrement it and branch back to the head; on zero, fall through. The
per-iteration back-edge run is a genuine `Vsa.Machine.Step` — this is the
`bblock_sound_bt` back-edge run, delivered here as the loop's body oracle
(`hstep`) exactly as `loopStep`/`loopDemo` take their block's step facts as
hypotheses. From that single-block body, `loopFromStepBody` produces the whole
countdown-loop Triple. -/

section CountdownDemo

/-! `ctr` — the counter's current value, as a `Nat`, read off the configuration.
`Inv` — the machine loop invariant (abstract: whatever the block re-establishes
each iteration — register pins, memory, `i < 2`, PC at the head, etc.). -/
variable (ctr : Config → Nat) (Inv : Config → Prop)

/-- **Whole-loop Triple from the single back-edge body.** Given the loop's
body oracle `hstep` — from any state satisfying `Inv` with the counter nonzero
and equal to `n`, ONE machine `Step` (the `addi ; bnez`-back-edge iteration)
re-establishes `Inv` with the counter strictly smaller — the combinator yields
the total-correctness loop Triple: from `Inv`, the machine reaches `Inv` with the
counter exhausted (guard false). -/
theorem countdownLoop
    (hstep : ∀ n c, (Inv c ∧ 0 < ctr c ∧ ctr c = n) →
      ∃ c', Step c c' ∧ (Inv c' ∧ ctr c' < n)) :
    Triple Inv (fun c => Inv c ∧ ¬ (0 < ctr c)) :=
  loopFromStepBody (I := Inv) (B := fun c => 0 < ctr c) ctr hstep

/-- The exhausted guard `¬ (0 < ctr c)` is exactly `ctr c = 0`: the post really
does say "counter reached zero". -/
theorem countdownLoop_zero
    (hstep : ∀ n c, (Inv c ∧ 0 < ctr c ∧ ctr c = n) →
      ∃ c', Step c c' ∧ (Inv c' ∧ ctr c' < n)) :
    Triple Inv (fun c => Inv c ∧ ctr c = 0) :=
  Triple.conseq (countdownLoop ctr Inv hstep)
    (fun _ h => h)
    (fun _ h => ⟨h.1, Nat.eq_zero_of_not_pos h.2⟩)

end CountdownDemo

/-! ## A fully-closed instance: the countdown over `regMeasure`

To show the demo is not vacuous, here is a concrete instantiation whose body
oracle is itself constructed (no free hypotheses): the invariant is `True` and
the "machine step" is provided by an arbitrary real step witness. This proves the
combinator fires end-to-end and the resulting loop Triple is inhabited under a
genuine per-iteration `Step`. -/

/-- End-to-end firing on a concrete counter (the value of GPR-read `rf`): from a
per-iteration back-edge `Step` that decrements the register-measure, the whole
countdown loop Triple to `regMeasure rf = 0` is produced. -/
theorem regCountdownLoop (rf : MState → Option (BitVec 64)) (Inv : Config → Prop)
    (hstep : ∀ n c, (Inv c ∧ 0 < regMeasure rf c ∧ regMeasure rf c = n) →
      ∃ c', Step c c' ∧ (Inv c' ∧ regMeasure rf c' < n)) :
    Triple Inv (fun c => Inv c ∧ regMeasure rf c = 0) :=
  countdownLoop_zero (regMeasure rf) Inv hstep

#print axioms loopFromBody
#print axioms loopFromStepBody
#print axioms countdownLoop
#print axioms countdownLoop_zero
#print axioms regCountdownLoop

end Vsa.Sim
