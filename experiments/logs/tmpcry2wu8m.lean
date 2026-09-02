import Vsa.Sim.EvalSimCommon
open Vsa.MemRepr Vsa.Alloc Vsa.Sim
namespace SmtAcc
def McallPresence : Prop :=
  ∀ (SL : StackLayout) (sp : BitVec 64) (m0 : Mem),
    ∀ mcall : Mem,
      (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mcall[a]? = m0[a]?) →
      ∀ a : Nat, sp.toNat - 1120 ≤ a → a < sp.toNat → (∃ b, mcall[a]? = some b)
end SmtAcc


namespace SmtReplay
private def m0W : Mem := (∅ : Mem).insert 0 (0#8)
set_option maxHeartbeats 1000000 in
theorem refuted : ¬ SmtAcc.McallPresence := by
  intro H
  have hagree : (∀ a : Nat, ¬ ((0 : Nat) ≤ a ∧ a < (16 : Nat)) → ((∅ : Mem)[a]? : Option (BitVec 8)) = (m0W)[a]?) := by
    intro a ha
    have haA : ((0 : Nat) == a) = false := by
      by_cases he : (0 : Nat) = a
      · exact absurd ⟨he ▸ Nat.le_refl _, by omega⟩ ha
      · simp [he]
    rw [show ((∅ : Mem)[a]? : Option (BitVec 8)) = none from by
          simp only [Std.ExtHashMap.getElem?_empty]]
    rw [show ((m0W)[a]? : Option (BitVec 8)) = none from by
          simp only [m0W, Std.ExtHashMap.getElem?_insert, haA]
          rw [if_neg (by decide), Std.ExtHashMap.getElem?_empty]]
  have hme := H ⟨0, 1000000⟩ (16#64) m0W (∅ : Mem) hagree
  have hpz := hme 0 (by decide) (by decide)
  obtain ⟨b', hb'⟩ := hpz
  rw [show ((∅ : Mem)[0]? : Option (BitVec 8)) = none from by
        simp only [Std.ExtHashMap.getElem?_empty]] at hb'
  exact absurd hb' (by simp)
#print axioms refuted
end SmtReplay
