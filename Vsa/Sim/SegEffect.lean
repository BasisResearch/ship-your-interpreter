import Vsa.Sim.SegReadback
import Vsa.Sim.TripleCat
import Vsa.Sim.BridgeSeg

namespace Vsa.Sim

open LeanRV64DExecutable Vsa
open Vsa.Machine (Config Steps)
open Vsa.Logic (Triple)

structure EffectStable (keep : Register → Prop)
    (left right : (R : Register) → Option (RegisterType R)) : Prop where
  eq : ∀ R, keep R → left R = right R

theorem EffectStable.trans
    (h₁ : EffectStable keep left middle)
    (h₂ : EffectStable keep middle right) :
    EffectStable keep left right := by
  exact ⟨fun R hR => (h₁.eq R hR).trans (h₂.eq R hR)⟩

structure FrameEffect where
  regs : Register → Prop
  mem : Nat → Prop
  output : Prop

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

universe u v w

end Vsa.Sim
