import Vsa.Sim.RuntimeOwnership
import Vsa.Sim.ReprCopy

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While

namespace Vsa.Sim.RuntimeOwnership

/-- A total value copy retains the owned payload pointer and its shared bytes. -/
theorem ValueOwned.copy_total {m m' : Mem} {shared : Nat → Prop}
    {src dst : Nat} {v : Value}
    (h : ValueOwned m shared src v)
    (hcopy : ∀ k, k < 24 → m'[dst + k]? = some ((m[src + k]?).getD 0))
    (ha : AgreeP shared m m') : ValueOwned m' shared dst v := by
  cases v <;> simp only [ValueOwned] at h ⊢
  all_goals first
    | exact True.intro
    | (obtain ⟨p, hp, hs⟩ := h
       exact ⟨p, read64_copy_total hcopy (by decide : 8 + 8 ≤ 24) hp,
         hs.transport ha⟩)

#print axioms ValueOwned.copy_total

end Vsa.Sim.RuntimeOwnership
