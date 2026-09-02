import Vsa.Sim.EvalSimCommon
open Vsa.MemRepr Vsa.Alloc Vsa.Sim
namespace SmtAcc
def BinArmMemExt : Prop :=
  ∀ (SL : StackLayout) (sp : BitVec 64) (m0 : Mem),
    ∀ m : Mem,
      (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → m[a]? = m0[a]?) →
      MemExtends m0 m
end SmtAcc


namespace SmtReplay
private def m0W : Mem := (∅ : Mem).insert 0 (0#8)
set_option maxHeartbeats 1000000 in
theorem refuted : ¬ SmtAcc.BinArmMemExt := by
  intro H
  have hagree : (∀ a : Nat, ¬ ((0 : Nat) ≤ a ∧ a < (18446744073709551615 : Nat)) → ((∅ : Mem)[a]? : Option (BitVec 8)) = (m0W)[a]?) := by
    intro a ha
    have haA : ((0 : Nat) == a) = false := by
      by_cases he : (0 : Nat) = a
      · exact absurd ⟨by omega, by omega⟩ (he ▸ ha)
      · simp [he]
    simp only [m0W, Std.ExtHashMap.getElem?_empty, Std.ExtHashMap.getElem?_insert]
    rw [if_neg (by simpa using haA)]
    simp [Std.ExtHashMap.getElem?_empty]
  have hme := H ⟨0, 1000000⟩ (18446744073709551615#64) (m0W) hagree
  have hm0A : (m0W)[0]? = some (0#8) := by
    simp only [m0W, Std.ExtHashMap.getElem?_insert]; simp
  obtain ⟨b', hb'⟩ := hme 0 (0#8) hm0A
  simp only [Std.ExtHashMap.getElem?_empty] at hb'
#print axioms refuted
end SmtReplay
