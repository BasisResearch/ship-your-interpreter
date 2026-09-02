import Vsa.Sim.TermAssembly
/-! UNCONTAMINATED fuzzer-v2 test: novel statements, same disease class,
FRESH parameters/names/shape variants the tool has never seen. -/
open Vsa Vsa.Sim Vsa.MemRepr
open Std (ExtHashMap)

-- N1: FALSE, same class, novel window (a totally different range 0x90000..)
-- and novel demand (a *specific byte value* survives, not just presence).
def NovelResidA : Prop :=
  ∀ (m0 : ExtHashMap Nat (BitVec 8)) (base : BitVec 64),
    m0[(0x90000 : Nat)]? = some (0x2a : BitVec 8) →
    ∀ mq : ExtHashMap Nat (BitVec 8),
      (∀ k, ¬ (0x90000 ≤ k ∧ k < 0x90010) → m0[k]? = mq[k]?) →
      mq[(0x90000 : Nat)]? = some (0x2a : BitVec 8)

-- N2: TRUE variant (the cure shape at novel parameters): agreement ON the
-- window is demanded, so the adversary is excluded.
def NovelResidB : Prop :=
  ∀ (m0 : ExtHashMap Nat (BitVec 8)),
    m0[(0x90000 : Nat)]? = some (0x2a : BitVec 8) →
    ∀ mq : ExtHashMap Nat (BitVec 8),
      (∀ k, (0x8f000 ≤ k ∧ k < 0x91000) → m0[k]? = mq[k]?) →
      mq[(0x90000 : Nat)]? = some (0x2a : BitVec 8)

-- N3: FALSE, shape VARIANT — two disjoint agree-windows, demand in the gap
-- between them (neither window covers it). Structurally new: conjunction of
-- two agree-hyps.
def NovelResidC : Prop :=
  ∀ (m0 : ExtHashMap Nat (BitVec 8)),
    (∀ k, k < 0x100 → m0[k]? = some (0x1 : BitVec 8)) →
    ∀ mq : ExtHashMap Nat (BitVec 8),
      (∀ k, k < 0x100 → m0[k]? = mq[k]?) →
      (∀ k, 0x200 ≤ k → m0[k]? = mq[k]?) →
      ∀ a, 0x100 ≤ a ∧ a < 0x200 → mq[a]? = m0[a]?



private def crange : Nat → Mem
  | 0 => (∅ : Mem)
  | n+1 => (crange n).insert n (0x1 : BitVec 8)
private theorem crange_get : ∀ N k, k < N → (crange N)[k]? = some (0x1 : BitVec 8) := by
  intro N; induction N with
  | zero => intro k hk; exact absurd hk (by omega)
  | succ n ih => intro k hk; simp only [crange, Std.ExtHashMap.getElem?_insert]
                 by_cases he : n = k
                 · subst he; simp
                 · rw [if_neg (by simp [beq_iff_eq]; omega)]; exact ih k (by omega)
private theorem crange_none : ∀ N k, N ≤ k → (crange N)[k]? = none := by
  intro N; induction N with
  | zero => intro k hk; simp [crange]
  | succ n ih => intro k hk; simp only [crange, Std.ExtHashMap.getElem?_insert]
                 rw [if_neg (by simp [beq_iff_eq]; omega)]; exact ih k (by omega)

namespace VsaFuzzSem
set_option maxHeartbeats 1000000 in
theorem probe : ¬ NovelProbe.NovelResidA := by
  first
  | (intro Hp
     have hbad := Hp (crange 589825) (fun k hk => crange_get 589825 k (by omega)) ((crange 589825).erase 589824) (by intro k hk; simp only [Std.ExtHashMap.getElem?_erase];
     rw [if_neg (by first | (revert hk; simp only [not_and, not_lt, not_le]; intro hk; simp only [beq_iff_eq]; omega) | (simp only [beq_iff_eq]; omega))])
     rw [(by simp [Std.ExtHashMap.getElem?_erase] : ((crange 589825).erase 589824)[589824]? = none)] at hbad; exact absurd hbad (by simp))
  | (intro Hp
     have hbad := Hp (crange 589825) ((crange 589825).erase 589824) (by intro k hk; simp only [Std.ExtHashMap.getElem?_erase];
     rw [if_neg (by first | (revert hk; simp only [not_and, not_lt, not_le]; intro hk; simp only [beq_iff_eq]; omega) | (simp only [beq_iff_eq]; omega))])
     rw [(by simp [Std.ExtHashMap.getElem?_erase] : ((crange 589825).erase 589824)[589824]? = none)] at hbad; exact absurd hbad (by simp))
  | (intro Hp
     have hbad := Hp (0#64) (crange 589825) (fun k hk => crange_get 589825 k (by omega)) ((crange 589825).erase 589824) (by intro k hk; simp only [Std.ExtHashMap.getElem?_erase];
     rw [if_neg (by first | (revert hk; simp only [not_and, not_lt, not_le]; intro hk; simp only [beq_iff_eq]; omega) | (simp only [beq_iff_eq]; omega))])
     rw [(by simp [Std.ExtHashMap.getElem?_erase] : ((crange 589825).erase 589824)[589824]? = none)] at hbad; exact absurd hbad (by simp))
  | (intro Hp
     have hbad := Hp (0#64) (crange 589825) ((crange 589825).erase 589824) (by intro k hk; simp only [Std.ExtHashMap.getElem?_erase];
     rw [if_neg (by first | (revert hk; simp only [not_and, not_lt, not_le]; intro hk; simp only [beq_iff_eq]; omega) | (simp only [beq_iff_eq]; omega))])
     rw [(by simp [Std.ExtHashMap.getElem?_erase] : ((crange 589825).erase 589824)[589824]? = none)] at hbad; exact absurd hbad (by simp))

#print axioms probe
end VsaFuzzSem
