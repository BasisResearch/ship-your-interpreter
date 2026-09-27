import Vsa.Compiler.RTLeaf

/-!
# `itos`: integers to string objects

`run_it`: from `itPos` with `a1 = x` and `a2 = d`, the routine writes the string
object of `intToString x.toInt` at `d` and returns with `a3` at its end. It
writes memory only in the object and in the digit buffer at `bufBase`.
-/

namespace Vsa.Compiler

open Vsa.Sim Vsa.While LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- The absolute last digit of `x` as a word, from the `tmod` word. -/
theorem digit_word (x : BitVec 64) :
    (if (BitVec.ofInt 64 (x.toInt.tmod 10)).toInt ≥ 0 then BitVec.ofInt 64 (x.toInt.tmod 10)
      else 0 - BitVec.ofInt 64 (x.toInt.tmod 10)) = BitVec.ofNat 64 (x.toInt.natAbs % 10) := by
  rw [abs_digit]
  have h1 : (x.toInt.tmod 10).natAbs = x.toInt.natAbs % 10 := by rw [Int.natAbs_tmod]; rfl
  split
  · next h =>
    have e : x.toInt.tmod 10 = ((x.toInt.natAbs % 10 : Nat) : Int) := by
      rw [← h1, Int.natAbs_of_nonneg h]
    rw [e, BitVec.ofInt_natCast]
  · next h =>
    have e : -(x.toInt.tmod 10) = ((x.toInt.natAbs % 10 : Nat) : Int) := by
      rw [← h1]; omega
    rw [BitVec.sub_eq_add_neg, zero_add64', ← BitVec.ofInt_neg, e, BitVec.ofInt_natCast]

/-- Registers the digit loop may change. -/
def itLoopClob : List Nat := [ra, t0, a0, a1, a2, a3, s4, s5, s6]

/-- Registers `itos` may change. -/
def itClob : List Nat := [ra, t0, t1, t2, a0, a1, a2, a3, a6, a7, s4, s5, s6, s9]

section
variable {code : List Ins} (hfit : Fits code) (hseg : Seg code itPos (itCode itPos))
include hfit hseg

theorem it_step {L' : GRegs} {m' : Mem} {o : Array String} {x : BitVec 64} {j : Nat}
    (h20 : Has L' s4 x) (h21 : Has L' s5 (BitVec.ofNat 64 j))
    (h22 : Has L' s6 (BitVec.ofNat 64 (bufBase + 8 * j))) (hj : j < 20) :
    Reaches code ⟨pcOf (itPos + 16), L', m', o⟩ (fun B => B.out = o ∧
      B.mem = applyW m' (bufBase + 8 * j, 8, BitVec.ofNat 64 (x.toInt.natAbs % 10 + 48)) ∧
      Has B.regs s4 (BitVec.ofInt 64 (x.toInt.tdiv 10)) ∧ Has B.regs s5 (BitVec.ofNat 64 (j + 1)) ∧
      Has B.regs s6 (BitVec.ofNat 64 (bufBase + 8 * (j + 1))) ∧ Keep itLoopClob L' B.regs ∧
      B.pc = (if BitVec.ofInt 64 (x.toInt.tdiv 10) = 0 then pcOf (itPos + 34) else pcOf (itPos + 16))) := by
  have hb : bufBase = 0x80080000 := rfl
  have ht : tohostAddr = 0x8001ad00 := rfl
  have k20 := has_mem h20 (by decide); have k21 := has_mem h21 (by decide)
  have k22 := has_mem h22 (by decide)
  have e20 := srcVal_of_has h20; have e21 := srcVal_of_has h21; have e22 := srcVal_of_has h22
  simp only [s4, s5, s6] at k20 k21 k22 e20 e21 e22
  have hbn : (BitVec.ofNat 64 (bufBase + 8 * j)).toNat = bufBase + 8 * j := toNat_ofNat_lt (by omega)
  -- from 23: the digit word is in a0
  have h23 : ∀ L'', Keep itLoopClob L' L'' → Has L'' a0 (BitVec.ofNat 64 (x.toInt.natAbs % 10)) →
      Has L'' s4 x → Has L'' s5 (BitVec.ofNat 64 j) → Has L'' s6 (BitVec.ofNat 64 (bufBase + 8 * j)) →
      Reaches code ⟨pcOf (itPos + 23), L'', m', o⟩ (fun B => B.out = o ∧
        B.mem = applyW m' (bufBase + 8 * j, 8, BitVec.ofNat 64 (x.toInt.natAbs % 10 + 48)) ∧
        Has B.regs s4 (BitVec.ofInt 64 (x.toInt.tdiv 10)) ∧ Has B.regs s5 (BitVec.ofNat 64 (j + 1)) ∧
        Has B.regs s6 (BitVec.ofNat 64 (bufBase + 8 * (j + 1))) ∧ Keep itLoopClob L' B.regs ∧
        B.pc = (if BitVec.ofInt 64 (x.toInt.tdiv 10) = 0 then pcOf (itPos + 34) else pcOf (itPos + 16))) := by
    intro L'' hk h10 g20 g21 g22
    have k20 := has_mem g20 (by decide); have k21 := has_mem g21 (by decide)
    have k22 := has_mem g22 (by decide); have k10 := has_mem h10 (by decide)
    have e20 := srcVal_of_has g20; have e21 := srcVal_of_has g21; have e22 := srcVal_of_has g22
    have e10 := srcVal_of_has h10
    simp only [s4, s5, s6, a0] at k20 k21 k22 k10 e20 e21 e22 e10
    have hd10 : x.toInt.natAbs % 10 < 10 := Nat.mod_lt _ (by decide)
    apply run_block hfit hseg 23 11 (itPos + 23) rfl
      (KP := fun L3 m3 o3 => o3 = o ∧
        m3 = applyW m' (bufBase + 8 * j, 8, BitVec.ofNat 64 (x.toInt.natAbs % 10 + 48)) ∧
        Has L3 s4 (BitVec.ofInt 64 (x.toInt.tdiv 10)) ∧ Has L3 s5 (BitVec.ofNat 64 (j + 1)) ∧
        Has L3 s6 (BitVec.ofNat 64 (bufBase + 8 * (j + 1))) ∧ Keep itLoopClob L' L3 ∧
        BitVec.ofInt 64 (x.toInt.tdiv 10) = 0)
      (fun L3 m3 o3 ⟨g1, g2, g3, g4, g5, g6, g7⟩ => reach_here ⟨g1, g2, g3, g4, g5, g6,
        by rw [if_pos g7]⟩)
      (by len_ok [itCode])
    have hne : bufBase + 8 * j ≠ tohostAddr := by omega
    wp_simp [itCode, itPos, psPos, k20, k21, k22, k10, e20, e21, e22, e10, hbn, hne]
    refine ⟨⟨by omega, by omega, by omega, by omega⟩, ?_⟩
    split
    · next hq =>
      refine reach_here ⟨rfl, rfl, ?_, ?_, ?_, ?_, by first | rfl | rw [if_neg (by simpa using hq)]⟩
      all_goals reg_simp
      all_goals first | exact hk | bv_eq
    · next hq =>
      refine ⟨?_, ?_, ?_, ?_, by simpa using hq⟩
      all_goals reg_simp
      all_goals first | exact hk | bv_eq
  -- 16 .. 22: the digit word
  have hdw := digit_word x
  apply run_block hfit hseg 16 6 (itPos + 16) rfl
    (KP := fun L3 m3 o3 => m' = m3 ∧ o = o3 ∧ Keep itLoopClob L' L3 ∧
      Has L3 a0 (BitVec.ofInt 64 (x.toInt.tmod 10)) ∧ (BitVec.ofInt 64 (x.toInt.tmod 10)).toInt < 0 ∧
      Has L3 s4 x ∧ Has L3 s5 (BitVec.ofNat 64 j) ∧ Has L3 s6 (BitVec.ofNat 64 (bufBase + 8 * j)))
    (fun L3 m3 o3 ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ => by
      subst g1 g2
      have k10 := has_mem g4 (by decide); have e10 := srcVal_of_has g4
      simp only [a0] at k10 e10
      apply run_block hfit hseg 22 1 (itPos + 16 + 6) rfl
        (KP := fun L4 m4 o4 => m' = m4 ∧ o = o4 ∧ Keep itLoopClob L' L4 ∧
          Has L4 a0 (BitVec.ofNat 64 (x.toInt.natAbs % 10)) ∧
          Has L4 s4 x ∧ Has L4 s5 (BitVec.ofNat 64 j) ∧ Has L4 s6 (BitVec.ofNat 64 (bufBase + 8 * j)))
        (fun L4 m4 o4 ⟨f1, f2, f3, f4, f5, f6, f7⟩ => by subst f1 f2; exact h23 L4 f3 f4 f5 f6 f7)
        (by len_ok [itCode])
      wp_simp [itCode, itPos, psPos, k10, e10]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · reg_simp; exact g3
      · reg_simp; rw [if_neg (by omega)] at hdw; exact hdw
      · reg_simp; exact g6
      · reg_simp; exact g7
      · reg_simp; exact g8)
    (by len_ok [itCode])
  wp_simp [itCode, itPos, psPos, k20, e20]
  split
  · next hge =>
    refine h23 _ ?_ ?_ ?_ ?_ ?_
    · reg_simp; exact Keep.refl _ _
    · reg_simp; rw [if_pos (by simpa using hge)] at hdw; exact hdw
    · reg_simp; exact h20
    · reg_simp; exact h21
    · reg_simp; exact h22
  · next hlt =>
    refine ⟨?_, ?_, by simpa using hlt, ?_, ?_, ?_⟩
    · reg_simp; exact Keep.refl _ _
    · reg_simp
    · reg_simp; exact h20
    · reg_simp; exact h21
    · reg_simp; exact h22

end

end Vsa.Compiler
