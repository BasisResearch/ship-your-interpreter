import Vsa.Sim.RuntimeOwnership

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While

namespace Vsa.Sim.RuntimeOwnership

/-- Shared strings remain owned when the shared domain grows. -/
theorem SharedCString.mono {m : Mem} {shared shared' : Nat → Prop} {p : Nat} {s : String}
    (h : SharedCString m shared p s) (includes : ∀ k, shared k → shared' k) :
    SharedCString m shared' p s :=
  ⟨h.repr, fun k hk => includes _ (h.bytes k hk)⟩

/-- Enlarging the shared domain retains each value's exact payload pointer. -/
theorem ValueOwned.mono {m : Mem} {shared shared' : Nat → Prop} {a : Nat} {v : Value}
    (h : ValueOwned m shared a v) (includes : ∀ k, shared k → shared' k) :
    ValueOwned m shared' a v := by
  cases v <;> simp only [ValueOwned] at h ⊢
  all_goals first
    | exact True.intro
    | (obtain ⟨p, hp, hs⟩ := h
       exact ⟨p, hp, hs.mono includes⟩)

#print axioms SharedCString.mono
#print axioms ValueOwned.mono

end Vsa.Sim.RuntimeOwnership
