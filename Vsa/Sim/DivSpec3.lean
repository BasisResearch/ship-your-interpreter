import Vsa.Sim.ObsAvoid
import Vsa.Sim.DecodeTable.Batch01Part10
import Vsa.Sim.DecodeTable.Batch08Part12
import Vsa.Sim.DecodeTable.Batch11Part19
import Vsa.Sim.DecodeTable.Batch11Part21
import Vsa.Sim.DecodeTable.Batch15Part23
import Vsa.Sim.DecodeTable.Batch15Part25
import Vsa.Sim.DecodeTable.Batch15Part28
import Vsa.Sim.DecodeTable.Batch15Part32
import Vsa.Sim.DivLoops

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem toInt_of_top (x : BitVec 64) (h : 2^63 ≤ x.toNat) :
    x.toInt = (x.toNat : Int) - 2^64 := by
  rw [BitVec.toInt_eq_toNat_cond]; have hx := x.isLt; rw [if_neg (by omega)]; simp

theorem toInt_of_notop (x : BitVec 64) (h : x.toNat < 2^63) :
    x.toInt = (x.toNat : Int) := by
  rw [BitVec.toInt_eq_toNat_cond]; rw [if_pos (by omega)]

theorem neg_toNat_of_top (x : BitVec 64) (h : 2^63 ≤ x.toNat) :
    ((0#64) - x).toNat = 2^64 - x.toNat := by
  rw [BitVec.toNat_sub]; have hx := x.isLt
  simp only [BitVec.toNat_ofNat, Nat.zero_mod]; omega

theorem natAbs_of_top (x : BitVec 64) (h : 2^63 ≤ x.toNat) :
    x.toInt.natAbs = 2^64 - x.toNat := by
  rw [toInt_of_top x h]; have hx := x.isLt
  rw [Int.natAbs_eq_iff]; right; push_cast; omega

theorem natAbs_of_notop (x : BitVec 64) (h : x.toNat < 2^63) :
    x.toInt.natAbs = x.toNat := by
  rw [toInt_of_notop x h]; simp

theorem tmod_nonpos_of_nonpos (a b : Int) (h : a ≤ 0) : a.tmod b ≤ 0 := by
  have := Int.tmod_nonneg (a := -a) b (by omega)
  rw [Int.neg_tmod] at this; omega

theorem tmod_of_natAbs_sign (a b q : Int)
    (hmag : q.natAbs = a.natAbs % b.natAbs)
    (hsign : 0 ≤ a → 0 ≤ q) (hsign2 : a < 0 → q ≤ 0) :
    q = a.tmod b := by
  have hnat : (a.tmod b).natAbs = a.natAbs % b.natAbs := Int.natAbs_tmod a b
  have habs : q.natAbs = (a.tmod b).natAbs := by rw [hmag, hnat]
  have hcases := Int.natAbs_eq_natAbs_iff.mp habs
  rcases Int.lt_trichotomy a 0 with ha | ha | ha
  · have hq0 := hsign2 (by omega)
    have htm := tmod_nonpos_of_nonpos a b (by omega)
    rcases hcases with h | h
    · exact h
    · omega
  · subst ha; simp only [Int.zero_tmod]
    have : q.natAbs = 0 := by rw [hmag]; simp
    exact Int.natAbs_eq_zero.mp this
  · have hq0 := hsign (by omega)
    have htm := Int.tmod_nonneg b (by omega : (0:Int) ≤ a)
    rcases hcases with h | h
    · exact h
    · omega

theorem tdiv_of_natAbs_sign (a b q : Int) (hb : b ≠ 0)
    (hmag : q.natAbs = a.natAbs / b.natAbs)
    (hsign : (0 ≤ a ↔ 0 ≤ b) → 0 ≤ q)
    (hsign2 : ¬(0 ≤ a ↔ 0 ≤ b) → q ≤ 0) :
    q = a.tdiv b := by
  have hnat : (a.tdiv b).natAbs = a.natAbs / b.natAbs := Int.natAbs_tdiv a b
  have habs : q.natAbs = (a.tdiv b).natAbs := by rw [hmag, hnat]
  have hcases := Int.natAbs_eq_natAbs_iff.mp habs

  by_cases hz : a.natAbs / b.natAbs = 0
  ·
    have hq0 : q = 0 := Int.natAbs_eq_zero.mp (by rw [hmag]; exact hz)
    have ht0 : a.tdiv b = 0 := Int.natAbs_eq_zero.mp (by rw [hnat]; exact hz)
    rw [hq0, ht0]
  ·
    rcases hcases with h | h
    · exact h
    · exfalso

      have htdne : a.tdiv b ≠ 0 := fun hc => hz (by rw [← hnat, hc]; simp)

      by_cases ha : 0 ≤ a <;> by_cases hb2 : 0 ≤ b
      · have hs : (0 ≤ a ↔ 0 ≤ b) := ⟨fun _ => hb2, fun _ => ha⟩
        have hq0 := hsign hs
        have htpos : 0 ≤ a.tdiv b := Int.tdiv_nonneg ha hb2
        omega
      · have hbneg : b < 0 := by omega
        have hs : ¬(0 ≤ a ↔ 0 ≤ b) := fun hi => absurd (hi.mp ha) (by omega)
        have hq0 := hsign2 hs
        have htneg : a.tdiv b ≤ 0 := by
          have := Int.tdiv_nonneg (a := a) (b := -b) ha (by omega); rw [Int.tdiv_neg] at this; omega
        omega
      · have haneg : a < 0 := by omega
        have hs : ¬(0 ≤ a ↔ 0 ≤ b) := fun hi => absurd (hi.mpr hb2) (by omega)
        have hq0 := hsign2 hs
        have htneg : a.tdiv b ≤ 0 := by
          have := Int.tdiv_nonneg (a := -a) (b := b) (by omega) hb2; rw [Int.neg_tdiv] at this; omega
        omega
      · have hs : (0 ≤ a ↔ 0 ≤ b) := ⟨fun hi => absurd hi ha, fun hi => absurd hi hb2⟩
        have hq0 := hsign hs
        have htpos : 0 ≤ a.tdiv b := by
          have := Int.tdiv_nonneg (a := -a) (b := -b) (by omega) (by omega)
          rwa [Int.neg_tdiv_neg] at this
        omega

theorem natAbs_le (x : BitVec 64) : x.toInt.natAbs ≤ 2^63 := by
  by_cases h : x.toNat < 2^63
  · rw [natAbs_of_notop x h]; omega
  · rw [natAbs_of_top x (by omega)]; have := x.isLt; omega

theorem mag_notop (x : BitVec 64) (h : x.toNat < 2^63) : x.toNat = x.toInt.natAbs :=
  (natAbs_of_notop x h).symm

theorem mag_neg_top (x : BitVec 64) (h : 2^63 ≤ x.toNat) : ((0#64) - x).toNat = x.toInt.natAbs := by
  rw [neg_toNat_of_top x h, natAbs_of_top x h]

theorem res_pos (n d A B : BitVec 64)
    (hA : A.toNat = n.toInt.natAbs) (hB : B.toNat = d.toInt.natAbs)
    (hnneg : 0 ≤ n.toInt) (hd0 : d.toInt ≠ 0) :
    (A % B).toInt = n.toInt.tmod d.toInt := by
  have hd0' : d.toInt.natAbs ≠ 0 := fun h => hd0 (Int.natAbs_eq_zero.mp h)
  have hBpos : 0 < B.toNat := by rw [hB]; omega
  have hBle : d.toInt.natAbs ≤ 2^63 := natAbs_le d
  have hmod : (A % B).toNat = n.toInt.natAbs % d.toInt.natAbs := by rw [BitVec.toNat_umod, hA, hB]
  have hlt : (A % B).toNat < 2^63 := by
    rw [hmod]; have := Nat.mod_lt (n.toInt.natAbs) (show 0 < d.toInt.natAbs by omega); omega
  have hresInt : (A % B).toInt = ((A % B).toNat : Int) := toInt_of_notop _ hlt
  apply tmod_of_natAbs_sign
  · rw [hresInt, Int.natAbs_natCast, hmod]
  · intro _; rw [hresInt]; exact Int.natCast_nonneg _
  · intro h; omega

theorem res_neg (n d A B : BitVec 64)
    (hA : A.toNat = n.toInt.natAbs) (hB : B.toNat = d.toInt.natAbs)
    (hnneg : n.toInt < 0) (hd0 : d.toInt ≠ 0) :
    ((0#64) - (A % B)).toInt = n.toInt.tmod d.toInt := by
  have hd0' : d.toInt.natAbs ≠ 0 := fun h => hd0 (Int.natAbs_eq_zero.mp h)
  have hBpos : 0 < B.toNat := by rw [hB]; omega
  have hBle : d.toInt.natAbs ≤ 2^63 := natAbs_le d
  have hmod : (A % B).toNat = n.toInt.natAbs % d.toInt.natAbs := by rw [BitVec.toNat_umod, hA, hB]
  have hlt : (A % B).toNat < 2^63 := by
    rw [hmod]; have := Nat.mod_lt (n.toInt.natAbs) (show 0 < d.toInt.natAbs by omega); omega
  by_cases hz : (A % B).toNat = 0
  · have h0 : ((0#64) - (A%B)) = 0#64 := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub]; simp [hz]
    rw [h0]
    apply tmod_of_natAbs_sign
    · simp only [BitVec.toInt_zero, Int.natAbs_zero]; rw [hmod] at hz; omega
    · intro h; omega
    · intro _; simp
  · have hres : ((0#64) - (A%B)).toNat = 2^64 - (A%B).toNat := by
      rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat, Nat.zero_mod]; have := (A%B).isLt; omega
    have hresTop : 2^63 ≤ ((0#64) - (A%B)).toNat := by rw [hres]; omega
    have hresInt : ((0#64)-(A%B)).toInt = (((0#64)-(A%B)).toNat : Int) - 2^64 := toInt_of_top _ hresTop
    apply tmod_of_natAbs_sign
    · rw [natAbs_of_top _ hresTop, hres, hmod]; omega
    · intro h; omega
    · intro _; rw [hresInt, hres]; omega

theorem toInt_lt_2p63 (n : BitVec 64) : n.toInt < 2^63 := by
  by_cases h : n.toNat < 2^63
  · rw [toInt_of_notop n h]; have := n.isLt; omega
  · rw [toInt_of_top n (by omega)]; have := n.isLt; omega

theorem udiv_le (n d A B : BitVec 64)
    (hA : A.toNat = n.toInt.natAbs) (hB : B.toNat = d.toInt.natAbs) :
    (A / B).toNat ≤ 2^63 := by
  rw [BitVec.toNat_udiv, hA, hB]
  have h1 : n.toInt.natAbs ≤ 2^63 := natAbs_le n
  calc n.toInt.natAbs / d.toInt.natAbs ≤ n.toInt.natAbs := Nat.div_le_self _ _
    _ ≤ 2^63 := h1

theorem udiv_lt_of_not_overflow (n d A B : BitVec 64)
    (hA : A.toNat = n.toInt.natAbs) (hB : B.toNat = d.toInt.natAbs)
    (hsame : 0 ≤ n.toInt ↔ 0 ≤ d.toInt) (hd0 : d.toInt ≠ 0)
    (hexcl : ¬(n.toInt = -2^63 ∧ d.toInt = -1)) :
    (A / B).toNat < 2^63 := by
  rw [BitVec.toNat_udiv, hA, hB]
  have h1 : n.toInt.natAbs ≤ 2^63 := natAbs_le n
  have hd0' : d.toInt.natAbs ≠ 0 := fun h => hd0 (Int.natAbs_eq_zero.mp h)
  have hnlt : n.toInt < 2^63 := toInt_lt_2p63 n
  by_cases hd1 : d.toInt.natAbs = 1
  · rw [hd1, Nat.div_one]
    by_cases hn : n.toInt.natAbs = 2^63
    · exfalso
      have hnval : n.toInt = -2^63 := by
        rcases Int.natAbs_eq n.toInt with he | he
        · rw [hn] at he; omega
        · rw [hn] at he; omega
      have hdval : d.toInt = -1 := by
        have hdneg : ¬ (0 ≤ d.toInt) := fun hc => absurd (hsame.mpr hc) (by omega)
        rcases Int.natAbs_eq d.toInt with he | he
        · rw [hd1] at he; omega
        · rw [hd1] at he; omega
      exact hexcl ⟨hnval, hdval⟩
    · omega
  · have hd2 : 2 ≤ d.toInt.natAbs := by omega
    calc n.toInt.natAbs / d.toInt.natAbs ≤ n.toInt.natAbs / 2 := Nat.div_le_div_left hd2 (by omega)
      _ < 2^63 := by omega

theorem res_div_same (n d A B : BitVec 64)
    (hA : A.toNat = n.toInt.natAbs) (hB : B.toNat = d.toInt.natAbs)
    (hsame : 0 ≤ n.toInt ↔ 0 ≤ d.toInt) (hd0 : d.toInt ≠ 0)
    (hnov : (A / B).toNat < 2^63) :
    (A / B).toInt = n.toInt.tdiv d.toInt := by
  have hmag : (A / B).toNat = n.toInt.natAbs / d.toInt.natAbs := by rw [BitVec.toNat_udiv, hA, hB]
  have hresInt : (A / B).toInt = ((A/B).toNat : Int) := toInt_of_notop _ hnov
  apply tdiv_of_natAbs_sign _ _ _ hd0
  · rw [hresInt, Int.natAbs_natCast, hmag]
  · intro _; rw [hresInt]; exact Int.natCast_nonneg _
  · intro h; exact absurd hsame h

theorem res_div_mixed (n d A B : BitVec 64)
    (hA : A.toNat = n.toInt.natAbs) (hB : B.toNat = d.toInt.natAbs)
    (hdiff : ¬(0 ≤ n.toInt ↔ 0 ≤ d.toInt)) (hd0 : d.toInt ≠ 0) :
    ((0#64) - (A / B)).toInt = n.toInt.tdiv d.toInt := by
  have hd0' : d.toInt.natAbs ≠ 0 := fun h => hd0 (Int.natAbs_eq_zero.mp h)
  have hmag : (A / B).toNat = n.toInt.natAbs / d.toInt.natAbs := by rw [BitVec.toNat_udiv, hA, hB]
  have hle : (A / B).toNat ≤ 2^63 := udiv_le n d A B hA hB
  by_cases hz : (A / B).toNat = 0
  · have h0 : ((0#64) - (A/B)) = 0#64 := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub]; simp [hz]
    rw [h0]
    apply tdiv_of_natAbs_sign _ _ _ hd0
    · simp only [BitVec.toInt_zero, Int.natAbs_zero]; rw [hmag] at hz; omega
    · intro _; simp
    · intro _; simp
  · have hres : ((0#64) - (A/B)).toNat = 2^64 - (A/B).toNat := by
      rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat, Nat.zero_mod]; have := (A/B).isLt; omega
    have hresTop : 2^63 ≤ ((0#64) - (A/B)).toNat := by rw [hres]; omega
    have hresInt : ((0#64)-(A/B)).toInt = (((0#64)-(A/B)).toNat : Int) - 2^64 := toInt_of_top _ hresTop
    apply tdiv_of_natAbs_sign _ _ _ hd0
    · rw [natAbs_of_top _ hresTop, hres, hmag]; omega
    · intro h; exact absurd h hdiff
    · intro _; rw [hresInt, hres]; omega

end Vsa.Sim
