import Vsa.Sim.BlockAdapter
import Vsa.Sim.DeriveCase

open LeanRV64DExecutable Vsa
open Vsa.Machine (MState Config Step Steps StepsN)
open Vsa.Logic (Triple TripleN)

namespace Vsa.Machine

theorem Step.steps_succ {a b : Config} (h : Step a b) : b.steps = a.steps + 1 := by
  cases h with
  | @mk σ σ' i i' u u' e =>

    show u' = u + 1

    unfold stepOnce at e
    repeat' first
      |
        (simp only [EStateM.Result.ok.injEq, Sum.inr.injEq, Prod.mk.injEq,
           reduceCtorEq, false_and] at e
         omega)
      |
        simp only [EStateM.Result.ok.injEq, reduceCtorEq, false_and] at e
      |
        simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
          Bind.bind, Pure.pure] at e
      |
        split at e

theorem Steps.steps_le {a b : Config} (hs : Steps a b) : a.steps ≤ b.steps := by
  induction hs with
  | refl c => exact Nat.le_refl _
  | head s _ ih =>
    have := s.steps_succ
    omega

theorem Steps.toN_of_stepsField {a b : Config} (hs : Steps a b) :
    StepsN (b.steps - a.steps) a b := by
  induction hs with
  | refl c => simpa using StepsN.zero c
  | @head a b c s hbc ih =>
    have hstep : b.steps = a.steps + 1 := s.steps_succ
    have hle : b.steps ≤ c.steps := hbc.steps_le

    have hrw : c.steps - a.steps = (c.steps - b.steps) + 1 := by omega
    rw [hrw]
    exact StepsN.succ s ih

theorem Steps.toN_of_stepsEq {a b : Config} {k : Nat}
    (hs : Steps a b) (hk : b.steps = a.steps + k) : StepsN k a b := by
  have := hs.toN_of_stepsField
  rw [hk] at this
  simpa using this

end Vsa.Machine

namespace Vsa.Sim

open Vsa.Machine

def LandedN (n : Nat) (c : Config) (P : Config → Prop) : Prop :=
  ∃ (m : Nat) (c' : Config), n ≤ m ∧ StepsN m c c' ∧ P c'

end Vsa.Sim
