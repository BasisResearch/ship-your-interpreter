import Vsa.Sim.Muldi3Spec

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem or_two_pow_eq_add (a j : Nat) (h : a % 2^(j+1) = 0) :
    a ||| 2^j = a + 2^j := by
  have hdvd : 2^(j+1) ∣ a := Nat.dvd_of_mod_eq_zero h
  obtain ⟨q, hq⟩ := hdvd
  rw [hq]
  have hlt : 2^j < 2^(j+1) := Nat.pow_lt_pow_right (by decide) (by omega)
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_two_pow_mul_add q hlt i]
  rw [Nat.mul_comm (2^(j+1)) q, Nat.testBit_mul_two_pow q i (j+1), Nat.testBit_two_pow]
  by_cases hi : i < j + 1
  · simp only [hi, if_true]
    have h1 : decide (j + 1 ≤ i) = false := by simp only [decide_eq_false_iff_not, Nat.not_le]; omega
    rw [h1, Bool.false_and, Bool.false_or]
  · simp only [hi, if_false]
    have hge : decide (j + 1 ≤ i) = true := by simp only [decide_eq_true_eq]; omega
    have hjne : decide (j = i) = false := by simp only [decide_eq_false_iff_not]; omega
    rw [hge, Bool.true_and, hjne, Bool.or_false]

def DivK (d a2 a3 : BitVec 64) (j : Nat) : Prop :=
  a2.toNat = d.toNat * 2^j ∧ a3.toNat = 2^j ∧ d.toNat * 2^j < 2^64

theorem mod_add_pow (a j : Nat) (h : a % 2^(j+1) = 0) : (a + 2^j) % 2^j = 0 := by
  have hdvd : 2^(j+1) ∣ a := Nat.dvd_of_mod_eq_zero h
  have h1 : 2^j ∣ 2^(j+1) := Nat.pow_dvd_pow 2 (by omega)
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_add (Nat.dvd_trans h1 hdvd) (Nat.dvd_refl _))

theorem mod_drop_pow (a j : Nat) (h : a % 2^(j+1) = 0) : a % 2^j = 0 := by
  have hdvd : 2^(j+1) ∣ a := Nat.dvd_of_mod_eq_zero h
  have h1 : 2^j ∣ 2^(j+1) := Nat.pow_dvd_pow 2 (by omega)
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans h1 hdvd)

theorem or_a3_toNat (a0 a3 : BitVec 64) (j : Nat) (ha3 : a3.toNat = 2^j)
    (hmod : a0.toNat % 2^(j+1) = 0) : (a0 ||| a3).toNat = a0.toNat + 2^j := by
  rw [BitVec.toNat_or, ha3, or_two_pow_eq_add a0.toNat j hmod]

end Vsa.Sim
