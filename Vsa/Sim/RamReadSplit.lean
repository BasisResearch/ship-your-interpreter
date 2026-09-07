import Vsa.Sim.RamReadPolicy

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register Sail.ConcurrencyInterfaceV1.PreSail
namespace Vsa.Sim

/-- Logarithm of the largest aligned chunk dividing a scalar access width. -/
def scalarChunkExp (a : BitVec 64) (k : Nat) : Nat :=
  min (Sail.BitVec.countTrailingZeros a) k

/-- Scalar width encoding has exactly its width exponent in trailing zeros. -/
theorem scalarWidth_ctz (k : Nat) (hk : k ≤ 3) :
    Sail.BitVec.countTrailingZeros (to_bits (l := 13) (2 ^ k)) = k := by
  have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hc with rfl | rfl | rfl | rfl <;> decide

/-- Exact executable split plan for every scalar power-of-two width. -/
theorem split_access_scalar
    (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64)
    (k : Nat) (hk : k ≤ 3) :
    (split_access a (2 ^ k)).run σ =
      .ok (((2 ^ (k - scalarChunkExp a k) : Nat) : Int),
        ((2 ^ scalarChunkExp a k : Nat) : Int)) σ := by
  have hctz : Sail.BitVec.countTrailingZeros
      (to_bits (l := (12 + 1 : Int).toNat) (2 ^ k)) = k := scalarWidth_ctz k hk
  simp only [split_access]
  rw [hctz]
  have hmin : min (Sail.BitVec.countTrailingZeros a : Int) (k : Int) =
      (scalarChunkExp a k : Int) := by
    simp only [scalarChunkExp]
    omega
  rw [hmin]
  have he : scalarChunkExp a k ≤ k := Nat.min_le_right _ _
  have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  have hex : scalarChunkExp a k = 0 ∨ scalarChunkExp a k = 1 ∨
      scalarChunkExp a k = 2 ∨ scalarChunkExp a k = 3 := by omega
  rcases hc with rfl | rfl | rfl | rfl <;>
    rcases hex with hex | hex | hex | hex
  all_goals first
    | omega
    | (simp [hex, simp_sail, EStateM.run, pure]; rfl)

/-- Every prefix of the trailing zero bits gives a divisibility fact. -/
theorem mod_pow_eq_zero_of_le_ctz (a : BitVec 64) (t : Nat)
    (ht : t ≤ Sail.BitVec.countTrailingZeros a) : a.toNat % 2 ^ t = 0 := by
  have hctz : t ≤ a.ctz.toNat := ht
  have hz : a.setWidth t = 0#t := by
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro i hi
    simp [hi, BitVec.getLsbD_false_of_lt_ctz (by omega : i < a.ctz.toNat)]
  have h := congrArg BitVec.toNat hz
  simpa using h

/-- A first set bit determines the trailing-zero count without evaluating reverse. -/
theorem countTrailingZeros_eq_of_low_bits {w : Nat} (a : BitVec w) (t : Nat)
    (hone : a.getLsbD t = true) (hzero : ∀ i, i < t → a.getLsbD i = false) :
    Sail.BitVec.countTrailingZeros a = t := by
  have hne : a ≠ 0#w := by
    intro h
    simp only [h, BitVec.getLsbD_zero] at hone
    contradiction
  have hc := BitVec.getLsbD_true_ctz_of_ne_zero hne
  have hlo : t ≤ a.ctz.toNat := by
    by_cases h : a.ctz.toNat < t
    · have hz := hzero _ h
      rw [hc] at hz
      contradiction
    · omega
  have hhi : a.ctz.toNat ≤ t := by
    by_cases h : t < a.ctz.toNat
    · have hz := BitVec.getLsbD_false_of_lt_ctz h
      rw [hone] at hz
      contradiction
    · omega
  change a.ctz.toNat = t
  omega

/-- Size and alignment of the chunk plan returned by the executable. -/
structure ScalarSplitFacts (a : BitVec 64) (k : Nat) : Prop where
  chunk_pos : 0 < 2 ^ scalarChunkExp a k
  count_pos : 0 < 2 ^ (k - scalarChunkExp a k)
  complete : 2 ^ (k - scalarChunkExp a k) * 2 ^ scalarChunkExp a k = 2 ^ k
  aligned : a.toNat % 2 ^ scalarChunkExp a k = 0

theorem scalarSplitFacts (a : BitVec 64) (k : Nat) : ScalarSplitFacts a k where
  chunk_pos := Nat.two_pow_pos _
  count_pos := Nat.two_pow_pos _
  complete := by
    rw [← Nat.pow_add]
    congr 1
    exact Nat.sub_add_cancel (Nat.min_le_right _ _)
  aligned := mod_pow_eq_zero_of_le_ctz a _ (Nat.min_le_left _ _)

/-- Physical address of a chunk in the increasing-order scalar split. -/
def scalarChunkAddress (a : BitVec 64) (k i : Nat) : BitVec 64 :=
  a + BitVec.ofNat 64 (i * 2 ^ scalarChunkExp a k)

/-- Each selected chunk stays inside the original RAM window and avoids HTIF. -/
structure ScalarChunkFacts (a : BitVec 64) (k i : Nat) : Prop where
  address : (scalarChunkAddress a k i).toNat = a.toNat + i * 2 ^ scalarChunkExp a k
  ram_lo : 0x80000000 ≤ (scalarChunkAddress a k i).toNat
  ram_hi : (scalarChunkAddress a k i).toNat + 2 ^ scalarChunkExp a k ≤ 0x100000000
  htif : (scalarChunkAddress a k i).toNat + 2 ^ scalarChunkExp a k ≤ tohostAddr ∨
    tohostAddr + 8 ≤ (scalarChunkAddress a k i).toNat
  aligned : (scalarChunkAddress a k i).toNat % 2 ^ scalarChunkExp a k = 0

theorem scalarChunkFacts (a : BitVec 64) (k i : Nat)
    (hi : i < 2 ^ (k - scalarChunkExp a k))
    (hlo : 0x80000000 ≤ a.toNat) (hhi : a.toNat + 2 ^ k ≤ 0x100000000)
    (hhtif : a.toNat + 2 ^ k ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat) :
    ScalarChunkFacts a k i := by
  have hf := scalarSplitFacts a k
  have hseg : i * 2 ^ scalarChunkExp a k + 2 ^ scalarChunkExp a k ≤ 2 ^ k := by
    calc
      _ = (i + 1) * 2 ^ scalarChunkExp a k := by rw [Nat.add_mul]; simp
      _ ≤ 2 ^ (k - scalarChunkExp a k) * 2 ^ scalarChunkExp a k :=
        Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ k := hf.complete
  have hoff : i * 2 ^ scalarChunkExp a k ≤ 2 ^ k :=
    Nat.le_trans (Nat.le_add_right _ _) hseg
  have haddr : (scalarChunkAddress a k i).toNat = a.toNat + i * 2 ^ scalarChunkExp a k := by
    simp only [scalarChunkAddress, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : i * 2 ^ scalarChunkExp a k < 2 ^ 64)]
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨haddr, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · rcases hhtif with h | h <;> omega
  · rw [haddr]
    simp [Nat.add_mod, hf.aligned]

#print axioms scalarChunkFacts

#print axioms countTrailingZeros_eq_of_low_bits
#print axioms mod_pow_eq_zero_of_le_ctz
#print axioms scalarSplitFacts

#print axioms scalarWidth_ctz
#print axioms split_access_scalar
end Vsa.Sim
