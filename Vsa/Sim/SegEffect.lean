import Vsa.Sim.BridgeSegFramed
import Vsa.Sim.SegReadback
import Vsa.Sim.TripleCat

namespace Vsa.Sim

open LeanRV64DExecutable Vsa
open Vsa.Machine (Config Steps)
open Vsa.Logic (Triple)

/-- A dependent register map is unchanged on the selected register predicate.
The codomain remains indexed by the register, matching the machine register
file rather than erasing values to an untyped word. -/
structure EffectStable (keep : Register → Prop)
    (left right : (R : Register) → Option (RegisterType R)) : Prop where
  eq : ∀ R, keep R → left R = right R

/-- Opaque transitivity for dependent register maps. -/
theorem EffectStable.trans
    (h₁ : EffectStable keep left middle)
    (h₂ : EffectStable keep middle right) :
    EffectStable keep left right := by
  exact ⟨fun R hR => (h₁.eq R hR).trans (h₂.eq R hR)⟩

/-! ## Compositional machine frames -/

/-- Observations guaranteed unchanged by a machine run.  The memory field is
an address predicate, so an exact write footprint `foot` is represented by
`fun a => ¬ foot a`.  Store/allocation representations remain typed predicates
and can be carried with `FramedTriple.carry` below. -/
structure FrameEffect where
  regs : Register → Prop
  mem : Nat → Prop
  output : Prop

/-- `EffectLe weak strong` says that every observation requested by `weak`
is supplied by `strong`.  It is the order used when forgetting frame facts. -/
structure EffectLe (weak strong : FrameEffect) : Prop where
  regs : ∀ R, weak.regs R → strong.regs R
  mem : ∀ a, weak.mem a → strong.mem a
  output : weak.output → strong.output

namespace EffectLe

theorem trans (h₁ : EffectLe first middle) (h₂ : EffectLe middle last) :
    EffectLe first last := by
  exact
    { regs := fun R hR => h₂.regs R (h₁.regs R hR)
      mem := fun a ha => h₂.mem a (h₁.mem a ha)
      output := fun ho => h₂.output (h₁.output ho) }

end EffectLe

/-! ## Finite effect descriptions -/

/-! ## Relation-indexed framed refinements -/

universe u v w

end Vsa.Sim
