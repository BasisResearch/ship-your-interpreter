import Vsa.Sim.DivSpec3
import Vsa.While.Semantics

open Vsa Vsa.Sim Vsa.While

namespace Vsa.Sim

set_option maxHeartbeats 800000

theorem digitChar_eq (d : Nat) (h : d < 10) : Nat.digitChar d = Char.ofNat (48 + d) := by
  match d, h with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl

theorem natDigits_fuel (f1 f2 n : Nat) (h1 : n + 1 ≤ f1) (h2 : n + 1 ≤ f2) :
    natDigits f1 n = natDigits f2 n := by
  induction f1 generalizing f2 n with
  | zero => omega
  | succ f1 ih =>
    cases f2 with
    | zero => omega
    | succ f2 =>
      unfold natDigits
      by_cases hlt : n < 10
      · simp [hlt]
      · simp only [hlt, if_false]
        rw [ih f2 (n/10) (by omega) (by omega)]

theorem natDigits_step (n : Nat) (h : 10 ≤ n) :
    natDigits (n + 1) n = natDigits (n / 10 + 1) (n / 10) ++ [Nat.digitChar (n % 10)] := by
  unfold natDigits
  have hlt : ¬ n < 10 := by omega
  simp only [hlt, if_false]
  congr 1
  exact natDigits_fuel n (n / 10 + 1) (n / 10) (by omega) (by omega)

theorem neg_magnitude (v : BitVec 64) (hneg : 2 ^ 63 ≤ v.toNat) :
    (- v).toNat = (- v.toInt).toNat := by
  have hv : v.toNat < 2 ^ 64 := v.isLt
  have hn : (- v) = (0#64) - v := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_neg, BitVec.toNat_sub]; simp
  rw [hn, neg_toNat_of_top v hneg, toInt_of_top v hneg]
  omega

theorem intToString_nonneg (v : BitVec 64) (h : v.toNat < 2 ^ 63) :
    intToString v.toInt = natToString v.toNat := by
  rw [toInt_of_notop v h]; rfl

theorem intToString_neg (v : BitVec 64) (h : 2 ^ 63 ≤ v.toNat) :
    intToString v.toInt = "-" ++ natToString (- v).toNat := by
  rw [neg_magnitude v h]
  have hlt : v.toInt < 0 := by rw [toInt_of_top v h]; have := v.isLt; omega
  rcases hi : v.toInt with m | m
  · exact absurd (hi ▸ hlt) (by simp)
  · rfl

theorem intToString_of_bv (v : BitVec 64) :
    intToString v.toInt =
      (if 2 ^ 63 ≤ v.toNat then "-" ++ natToString (- v).toNat
       else natToString v.toNat) := by
  by_cases h : 2 ^ 63 ≤ v.toNat
  · rw [if_pos h, intToString_neg v h]
  · rw [if_neg h, intToString_nonneg v (by omega)]

end Vsa.Sim
