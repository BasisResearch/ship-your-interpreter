import Vsa.Sim.MemLoadTotal

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

abbrev magic7f : BitVec 64 := 0x7f7f7f7f7f7f7f7f#64

abbrev strlenWordVal (w : BitVec 64) : BitVec 64 :=
  (((w &&& magic7f) + magic7f) ||| w) ||| magic7f

theorem magic_bit : ∀ i : Fin 64, magic7f.getLsbD i.val = decide (i.val % 8 ≠ 7) := by
  decide

theorem strlenWordVal_bit (w : BitVec 64) (i : Nat) :
    (strlenWordVal w).getLsbD i =
      (((w &&& magic7f) + magic7f).getLsbD i || w.getLsbD i || magic7f.getLsbD i) := by
  simp only [strlenWordVal, BitVec.getLsbD_or]

theorem magic_carry (w : BitVec 64) (k : Nat) (hk : k < 8) :
    BitVec.carry (8*k+7) (w &&& magic7f) magic7f false
      = decide (w.toNat / 2^(8*k) % 128 ≠ 0) := by
  have hmv : magic7f.toNat = 0x7f7f7f7f7f7f7f7f := by decide
  have hand : (w &&& magic7f).toNat / 2^(8*k) % 128 = w.toNat / 2^(8*k) % 128 := by
    have hmd : magic7f.toNat / 2^(8*k) % 128 = 127 := by
      rw [hmv]; rcases k with _|_|_|_|_|_|_|_|k <;> first | rfl | omega
    rw [BitVec.toNat_and, Nat.and_div_two_pow, Nat.and_mod_two_pow (n := 7),
        show (128:Nat) = 2^7 from rfl] at *
    rw [hmd, show (127:Nat) = 2^7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]
  have ha : (w &&& magic7f).toNat % 2^(8*k) ≤ magic7f.toNat % 2^(8*k) := by
    rw [BitVec.toNat_and, Nat.and_mod_two_pow]; exact Nat.and_le_right
  have hn : (2:Nat)^(8*k+7) = 2^(8*k) * 128 := by rw [Nat.pow_add]
  have key : ((w &&& magic7f).toNat % 2^(8*k+7) + magic7f.toNat % 2^(8*k+7) + (false:Bool).toNat ≥ 2^(8*k+7))
      ↔ (w.toNat / 2^(8*k) % 128 ≠ 0) := by
    rw [hn, Nat.mod_mul, Nat.mod_mul, Bool.toNat_false, hmv, ← hand]
    rw [hmv] at ha
    rcases k with _|_|_|_|_|_|_|_|k
    all_goals (first | omega | (simp only [Nat.reduceMul, Nat.reducePow, Nat.reduceAdd] at ha ⊢; omega))
  unfold BitVec.carry
  rw [show ∀ a b : Nat, (a ≥b b) = decide (a ≥ b) from fun _ _ => rfl]
  exact decide_eq_decide.mpr key

theorem strlenWordVal_bit_high (w : BitVec 64) (k : Nat) (hk : k < 8) :
    (strlenWordVal w).getLsbD (8*k+7) = decide (w.toNat / 2^(8*k) % 256 ≠ 0) := by
  rw [strlenWordVal_bit]
  have hlt : 8*k+7 < 64 := by omega
  rw [BitVec.getLsbD_add hlt, BitVec.getLsbD_and]
  have hmb : magic7f.getLsbD (8*k+7) = false := by
    rcases k with _|_|_|_|_|_|_|_|k <;> first | rfl | omega
  rw [hmb, magic_carry w k hk]
  simp only [Bool.and_false, Bool.false_xor, Bool.or_false]
  have hwb : w.getLsbD (8*k+7) = decide (w.toNat / 2^(8*k) / 128 % 2 = 1) := by
    rw [← BitVec.testBit_toNat, show 8*k+7 = 7 + 8*k from by omega, Nat.testBit_add,
        Nat.testBit_eq_decide_div_mod_eq, show (2:Nat)^7 = 128 from rfl]
  rw [hwb, ← Bool.decide_or, decide_eq_decide]
  generalize w.toNat / 2^(8*k) = y
  omega

theorem extractLsb'_byte_ne_zero (w : BitVec 64) (k : Nat) :
    (w.extractLsb' (8*k) 8 ≠ 0) ↔ (w.toNat / 2^(8*k) % 256 ≠ 0) := by
  constructor <;> intro h <;> intro hc <;> apply h
  · apply BitVec.eq_of_toNat_eq
    show w.toNat >>> (8*k) % 256 = _
    rw [Nat.shiftRight_eq_div_pow, hc]; rfl
  · have : (w.extractLsb' (8*k) 8).toNat = 0 := by rw [hc]; rfl
    show w.toNat / 2^(8*k) % 256 = 0
    rw [← Nat.shiftRight_eq_div_pow]; exact this

theorem detect_all_ones (w : BitVec 64) :
    strlenWordVal w = BitVec.allOnes 64 ↔ ∀ k, k < 8 → w.extractLsb' (8*k) 8 ≠ 0 := by
  constructor
  · intro h k hk
    have hbit : (strlenWordVal w).getLsbD (8*k+7) = true := by
      rw [h, BitVec.getLsbD_allOnes]; simp only [decide_eq_true_eq]; omega
    rw [strlenWordVal_bit_high w k hk, decide_eq_true_eq] at hbit
    exact (extractLsb'_byte_ne_zero w k).mpr hbit
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_allOnes]
    simp only [hi, decide_true]
    by_cases hmod : i % 8 = 7
    · have hk : i / 8 < 8 := by omega
      have hi7 : i = 8*(i/8) + 7 := by omega
      rw [hi7, strlenWordVal_bit_high w (i/8) hk, decide_eq_true_eq]
      exact (extractLsb'_byte_ne_zero w (i/8)).mp (h (i/8) hk)
    · rw [strlenWordVal_bit]
      have hmbi : magic7f.getLsbD i = true := by
        have := magic_bit ⟨i, hi⟩
        simp only at this
        rw [this]; simp only [decide_eq_true_eq]; exact hmod
      rw [hmbi]; simp

end Vsa.Sim
