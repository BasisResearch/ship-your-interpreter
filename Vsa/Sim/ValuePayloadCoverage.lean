import Vsa.Sim.ReprSurvival

namespace Vsa.Sim
open Vsa.MemRepr Vsa.While

/-- Widen the allowed bytes of the actual semantic value's indirect payload. -/
theorem ValuePayloadCovered.mono {P Q : Nat → Prop} {m : Mem} {a : Nat} {v : Value}
    (h : ValuePayloadCovered P m a v) (hpq : ∀ k, P k → Q k) :
    ValuePayloadCovered Q m a v := by
  cases v <;> simp only [ValuePayloadCovered] at h ⊢
  all_goals first
    | exact True.intro
    | exact fun p hp k hk => hpq _ (h p hp k hk)

#print axioms ValuePayloadCovered.mono
end Vsa.Sim
