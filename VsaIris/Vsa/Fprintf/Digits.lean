import VsaIris.Vsa.Fprintf.Scan
import VsaIris.Vsa.Fprintf.Arith
import Vsa.Sim.SnprintfSpec

/-!
# `_vfprintf_r`'s decimal loop (lane N5)

`%lld` of a magnitude above 9 runs the loop at `0x8000ca80`: `__umoddi3`
gives the low digit, stored below the write pointer `s11`; `__udivdi3`
divides by ten; the loop stops once the dividend was at most 9. The digits
land MSB-first in `[D - L, D)`: `natDigits (n + 1) n`, the digit list of
`Vsa.While.natToString` (`digBytes`). `natDigits_step` (`SnprintfSpec.lean`)
is the loop's induction step.
-/

namespace VsaIris.Sym.Fp

open Vsa.Sim Vsa.MemRepr VsaIris.Sym VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio Vsa.While
open scoped VsaIris.Sym.Stdout

variable {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
  {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

/-- A character's byte. -/
def chByte (c : Char) : BitVec 8 := BitVec.ofNat 8 c.toNat

/-- The decimal digits of `n`, as bytes. -/
def digBytes (n : Nat) : List (BitVec 8) := (natDigits (n + 1) n).map chByte

theorem natDigits_len (k : Nat) : ∀ f n, n < 10 ^ (k + 1) → (natDigits f n).length ≤ k + 1 := by
  induction k with
  | zero =>
    intro f n hn
    cases f with
    | zero => simp [natDigits]
    | succ f => simp only [natDigits]; split <;> simp_all
  | succ k ih =>
    intro f n hn
    cases f with
    | zero => simp [natDigits]
    | succ f =>
      simp only [natDigits]
      split
      · simp
      · simp only [List.length_append, List.length_singleton]
        have := ih f (n / 10) (by rw [Nat.pow_succ] at hn; omega)
        omega

theorem digBytes_len (n : Nat) (hn : n < 2 ^ 64) : (digBytes n).length ≤ 20 := by
  unfold digBytes; rw [List.length_map]
  exact natDigits_len 19 _ _ (by omega)

theorem digBytes_pos (n : Nat) : 1 ≤ (digBytes n).length := by
  unfold digBytes; rw [List.length_map]; unfold natDigits
  split
  · simp
  · simp

theorem chOfNat_toNat (m : Nat) (h : m < 55296) : (Char.ofNat m).toNat = m := by
  have hv : m.isValidChar := Or.inl h
  simp [Char.ofNat, Char.ofNatAux, hv, Char.toNat]

theorem digBytes_small (n : Nat) (h : n ≤ 9) : digBytes n = [BitVec.ofNat 8 (48 + n)] := by
  unfold digBytes natDigits
  rw [if_pos (show n < 10 by omega)]
  simp only [List.map_cons, List.map_nil, chByte, digitChar_eq n (by omega), chOfNat_toNat _ (by omega : 48 + n < 55296)]

theorem digBytes_step (n : Nat) (h : 10 ≤ n) :
    digBytes n = digBytes (n / 10) ++ [BitVec.ofNat 8 (48 + n % 10)] := by
  unfold digBytes
  rw [natDigits_step n h, List.map_append]
  simp only [List.map_cons, List.map_nil, chByte, digitChar_eq (n % 10) (by omega),
    chOfNat_toNat _ (by omega : 48 + n % 10 < 55296)]

/-- `addiw a0, a0, 48` of a digit. -/
theorem digit_word (d : Nat) (h : d < 10) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 d + 48#64)) =
      BitVec.zeroExtend 64 (BitVec.ofNat 8 (48 + d)) := by
  have hm : (BitVec.extractLsb 31 0 (BitVec.ofNat 64 d + 48#64)).msb = false := by
    rw [BitVec.msb_eq_decide]; simp; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq; simp; omega

/-- The registers the decimal loop keeps. -/
abbrev digKeep : List Nat := [2, 3, 4, 6, 7, 9, 16, 17, 18, 19, 20, 21, 24, 26, 28, 29, 30, 31]

/-- The stack bytes the decimal loop writes below the write pointer `D`,
inside `_vfprintf_r`'s conversion buffer `[sp + 248, sp + 348)`. -/
def DigReg (sp D : Nat) (a : Nat) : Prop := sp + 248 ≤ a ∧ a < D

/-- **The decimal loop** (`0x8000ca80`) on the magnitude `n`, write pointer
`s11 = D`: the digits of `n` in `[D - L, D)`, `s9 = D - L`, back at the join
`0x8000cab8`. -/
theorem vfp_digits (hlive : ∀ p ∈ stdioText, live p.1) (hlive' : ∀ p ∈ interpText, live p.1)
    (hsub : ∀ p ∈ interpText, p ∈ dataOf Dt DA) {t : String} {s sp : BitVec 64} {need : Nat}
    (hs1 : s.toNat - need + 1024 ≤ sp.toNat) (hs2 : sp.toNat + 592 ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0) :
    ∀ (n D : Nat) (R : Nat → BitVec 64) (Mt : Mem), n < 2 ^ 64 →
      sp.toNat + 248 + (digBytes n).length ≤ D → D ≤ sp.toNat + 348 →
      R 2 = sp → R 20 = 0#64 → R 22 = BitVec.ofNat 64 n → R 27 = BitVec.ofNat 64 D →
      (∀ (R' : Nat → BitVec 64) (Mt' : Mem), R' 25 = BitVec.ofNat 64 (D - (digBytes n).length) →
        (∀ x ∈ digKeep, R' x = R x) → Frame Mt' Mt (DigReg sp.toNat D) →
        (∀ i (h : i < (digBytes n).length), imgM Mt' (D - (digBytes n).length + i) = (digBytes n)[i]) →
        SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000cab8#64 R' Mt') →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000ca80#64 R Mt := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro D R Mt hn hD1 hD2 h2 h20 h22 h27 hk
  have hL1 := digBytes_pos n
  nx_run hlive using [h2, h22, h27, h20] at 2147501812
  refine umoddi3_sw hlive' hsub (BitVec.ofNat 64 n) 10#64 0x8000ca8c#64 _ Mt (by decide) (by rsimp)
    (by rsimp) (by rsimp) (by decide) fun R1 hm hk1 => ?_
  have hm' : R1 10 = BitVec.ofNat 64 (n % 10) := BitVec.eq_of_toNat_eq (by rw [hm]; simp; omega)
  have k1 : ∀ x ∈ digKeep ++ [8, 22, 27], R1 x = R x := fun x hx => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rw [hk1 x (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    rsimp; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have k2 : R1 2 = sp := (k1 2 (by decide)).trans h2
  have k20 : R1 20 = 0#64 := (k1 20 (by decide)).trans h20
  have k22 : R1 22 = BitVec.ofNat 64 n := (k1 22 (by decide)).trans h22
  have k27 : R1 27 = BitVec.ofNat 64 D := (k1 27 (by decide)).trans h27
  have hDn : (BitVec.ofNat 64 D).toNat = D := by rw [BitVec.toNat_ofNat]; have := sp.isLt; omega
  have eD : BitVec.ofNat 64 D + 18446744073709551615#64 = BitVec.ofNat 64 (D - 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_add_neg (k := 18446744073709551615) (by omega) (by rw [hDn]; omega), hDn,
      BitVec.toNat_ofNat]
    have := sp.isLt; omega
  nx_run hlive using [k2, k20, k22, k27, hm', eD, digit_word (n % 10) (Nat.mod_lt _ (by decide))]
    at 2147501740
  refine udiv_sw hlive' hsub (BitVec.ofNat 64 n) 10#64 0x8000ca6c#64 _ _ (by decide) (by rsimp)
    (by rsimp) (by rsimp) (by decide) fun R2 hq _ hk2 => ?_
  have hq' : R2 10 = BitVec.ofNat 64 (n / 10) := BitVec.eq_of_toNat_eq (by rw [hq]; simp; omega)
  have m : ∀ x, x ≠ 1 → x ≠ 8 → x ≠ 10 → x ≠ 11 → x ≠ 12 → x ≠ 13 → x ≠ 25 → R2 x = R1 x := fun x a b c d e f g => by
    rw [hk2 x c d e f]; rsimp; rw [if_neg a, if_neg d, if_neg c, if_neg b, if_neg g, if_neg c]
  have m2 : ∀ x ∈ digKeep ++ [22, 27], R2 x = R x := fun x hx => by
    have hx' := hx
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx'
    rw [m x (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact k1 x (by revert hx; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; omega)
  have m25 : R2 25 = BitVec.ofNat 64 (D - 1) := by
    rw [hk2 25 (by decide) (by decide) (by decide) (by decide)]; rsimp
  have n2 : R2 2 = sp := (m2 2 (by decide)).trans h2
  have n20 : R2 20 = 0#64 := (m2 20 (by decide)).trans h20
  have n22 : R2 22 = BitVec.ofNat 64 n := (m2 22 (by decide)).trans h22
  have hnn : (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat]; omega
  have hD1n : (BitVec.ofNat 64 (D - 1)).toNat = D - 1 := by rw [BitVec.toNat_ofNat]; have := sp.isLt; omega
  have hFr : Frame (writeLog Mt [((BitVec.ofNat 64 (D - 1)).toNat, 1,
      BitVec.zeroExtend 64 (BitVec.ofNat 8 (48 + n % 10)))]) Mt (DigReg sp.toNat D) :=
    Frame.store Mt _ fun b h1 h2 => by rw [hD1n] at h1 h2; unfold DigReg; omega
  have hkp : ∀ x ∈ digKeep, upd (upd (upd (upd R2 23 (BitVec.ofNat 64 n)) 15 9#64) 27
      (BitVec.ofNat 64 (D - 1))) 22 (BitVec.ofNat 64 (n / 10)) x = R x := by
    have := fun x (hx : x ∈ digKeep) => m2 x (List.mem_append_left _ hx)
    keep_chain this
  by_cases h9 : n ≤ 9
  · -- the dividend was at most 9: the last digit
    have hb : ((BitVec.ofNat 64 n).toNat ≤ (9#64).toNat) = True := eq_true (by rw [hnn]; exact h9)
    nx_run hlive using [n2, n20, n22, m25, hq', hb] at 2147535488 2147535544
    have hL := digBytes_small n (by omega)
    refine hk _ _ ?_ hkp hFr fun i hi => ?_
    · rsimp; rw [hL, List.length_singleton]; exact m25
    · simp only [hL, List.length_singleton] at hi ⊢
      obtain rfl : i = 0 := by omega
      simp only [List.getElem_cons_zero, Nat.add_zero]
      have e := imgM_sb_zext Mt ((BitVec.ofNat 64 (D - 1)).toNat) (BitVec.ofNat 8 (48 + n % 10))
      rw [hD1n] at e ⊢
      rwa [show n % 10 = n by omega] at e ⊢

  · -- the dividend was above 9: the next digit
    have hb : ((BitVec.ofNat 64 n).toNat ≤ (9#64).toNat) = False := eq_false (by rw [hnn]; exact h9)
    nx_run hlive using [n2, n20, n22, m25, hq', hb] at 2147535488 2147535544
    have hn10 : n / 10 < n := by omega
    have hL := digBytes_step n (by omega)
    have hLl : (digBytes n).length = (digBytes (n / 10)).length + 1 := by rw [hL]; simp
    refine ih (n / 10) hn10 (D - 1) _ _ (by omega) (by omega) (by omega) (by rsimp; exact n2)
      (by rsimp; exact n20) (by rsimp) (by rsimp) fun R' Mt' e25 hk' hF' hbs => ?_
    refine hk R' Mt' (by rw [e25, hLl]; congr 1; omega) (fun x hx => (hk' x hx).trans (hkp x hx))
      (hFr.trans (hF'.mono fun a h => by unfold DigReg at h ⊢; omega)) fun i hi => ?_
    rw [List.getElem_of_eq hL hi]
    rw [hLl] at hi ⊢
    by_cases hi' : i < (digBytes (n / 10)).length
    · rw [List.getElem_append_left hi', show D - ((digBytes (n / 10)).length + 1) + i =
        D - 1 - (digBytes (n / 10)).length + i by omega]
      exact hbs i hi'
    · have ei : i = (digBytes (n / 10)).length := by omega
      subst ei
      rw [List.getElem_append_right (by omega)]
      simp only [Nat.sub_self, List.getElem_cons_zero]
      rw [hF' _ (fun h => by unfold DigReg at h; omega), show D - ((digBytes (n / 10)).length + 1) +
        (digBytes (n / 10)).length = (BitVec.ofNat 64 (D - 1)).toNat by rw [hD1n]; omega]
      exact imgM_sb_zext _ _ _

end VsaIris.Sym.Fp
