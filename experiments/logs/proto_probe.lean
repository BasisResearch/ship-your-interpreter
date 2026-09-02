import Vsa.Sim.TermAssembly
open Vsa Vsa.Sim Vsa.MemRepr
open Std (ExtHashMap)

-- N1 (A): FALSE. window [0x90000,0x90010) negated agree; demand VALUE at 0x90000.
-- Adversary: erase 0x90000 (or set it to a different value). Demand address IS
-- in the erased window => not covered => corrupt there.
def NovelResidA : Prop :=
  ∀ (m0 : ExtHashMap Nat (BitVec 8)) (base : BitVec 64),
    m0[(0x90000 : Nat)]? = some (0x2a : BitVec 8) →
    ∀ mq : ExtHashMap Nat (BitVec 8),
      (∀ k, ¬ (0x90000 ≤ k ∧ k < 0x90010) → m0[k]? = mq[k]?) →
      mq[(0x90000 : Nat)]? = some (0x2a : BitVec 8)

-- Adversary construction for A: m0 = ∅.insert 0x90000 0x2a ; mq = m0 corrupted
-- at 0x90000 by ERASING (some other value). Use mq = ∅ (0x90000 absent).
theorem refuteA : ¬ NovelResidA := by
  intro H
  have hm0 : ((∅ : ExtHashMap Nat (BitVec 8)).insert 0x90000 (0x2a : BitVec 8))[(0x90000:Nat)]? = some (0x2a : BitVec 8) := by
    simp
  have hagree : ∀ k, ¬ (0x90000 ≤ k ∧ k < 0x90010) →
      ((∅ : ExtHashMap Nat (BitVec 8)).insert 0x90000 (0x2a : BitVec 8))[k]? = (∅ : ExtHashMap Nat (BitVec 8))[k]? := by
    intro k hk
    -- k ≠ 0x90000 because 0x90000 is in the window
    have hne : (0x90000 : Nat) ≠ k := by
      intro he; apply hk; rw [← he]; exact ⟨Nat.le_refl _, by decide⟩
    simp only [Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_empty]
    rw [if_neg (by simp [beq_iff_eq]; omega)]
  have hbad := H ((∅ : ExtHashMap Nat (BitVec 8)).insert 0x90000 (0x2a : BitVec 8)) 0 hm0 (∅ : ExtHashMap Nat (BitVec 8)) hagree
  simp at hbad

#print axioms refuteA
