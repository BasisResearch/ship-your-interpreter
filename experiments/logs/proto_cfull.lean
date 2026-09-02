import Vsa.Sim.TermAssembly
open Vsa Vsa.Sim Vsa.MemRepr
open Std (ExtHashMap)

def crange : Nat → ExtHashMap Nat (BitVec 8)
  | 0 => ∅
  | n+1 => (crange n).insert n (0x1 : BitVec 8)
theorem crange_get : ∀ N k, k < N → (crange N)[k]? = some (0x1 : BitVec 8) := by
  intro N; induction N with
  | zero => intro k hk; exact absurd hk (by omega)
  | succ n ih => intro k hk; simp only [crange, Std.ExtHashMap.getElem?_insert]
                 by_cases he : n = k
                 · subst he; simp
                 · rw [if_neg (by simp [beq_iff_eq]; omega)]; exact ih k (by omega)
theorem crange_none : ∀ N k, N ≤ k → (crange N)[k]? = none := by
  intro N; induction N with
  | zero => intro k hk; simp [crange]
  | succ n ih => intro k hk; simp only [crange, Std.ExtHashMap.getElem?_insert]
                 rw [if_neg (by simp [beq_iff_eq]; omega)]; exact ih k (by omega)

def NovelResidC : Prop :=
  ∀ (m0 : ExtHashMap Nat (BitVec 8)),
    (∀ k, k < 0x100 → m0[k]? = some (0x1 : BitVec 8)) →
    ∀ mq : ExtHashMap Nat (BitVec 8),
      (∀ k, k < 0x100 → m0[k]? = mq[k]?) →
      (∀ k, 0x200 ≤ k → m0[k]? = mq[k]?) →
      ∀ a, 0x100 ≤ a ∧ a < 0x200 → mq[a]? = m0[a]?

theorem refuteC : ¬ NovelResidC := by
  intro H
  -- demand address a = 0x100 (in gap [0x100,0x200))
  have hpop : ∀ k, k < 0x100 → (crange 0x100)[k]? = some (0x1 : BitVec 8) :=
    fun k hk => crange_get 0x100 k hk
  have hag1 : ∀ k, k < 0x100 → (crange 0x100)[k]? = ((crange 0x100).insert 0x100 (0x1:BitVec 8))[k]? := by
    intro k hk
    simp only [Std.ExtHashMap.getElem?_insert]
    rw [if_neg (by simp [beq_iff_eq]; omega)]
  have hag2 : ∀ k, 0x200 ≤ k → (crange 0x100)[k]? = ((crange 0x100).insert 0x100 (0x1:BitVec 8))[k]? := by
    intro k hk
    simp only [Std.ExtHashMap.getElem?_insert]
    rw [if_neg (by simp [beq_iff_eq]; omega)]
  have hbad := H (crange 0x100) hpop ((crange 0x100).insert 0x100 (0x1:BitVec 8)) hag1 hag2 0x100 ⟨by omega, by omega⟩
  -- hbad : mq[0x100]? = m0[0x100]?  i.e. some 1 = none
  rw [crange_none 0x100 0x100 (by omega)] at hbad
  simp at hbad

#print axioms refuteC
