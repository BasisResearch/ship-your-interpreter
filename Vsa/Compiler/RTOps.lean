import Vsa.Compiler.VRepr

/-!
# The operator routines

Each routine takes the left operand in `(a0, a1)` and the right one in `(a2, a3)`
and either returns the representation of `binOpSem` of the represented values,
or reaches the error exit exactly when `binOpSem` has no result (for `+`, also
when the object heap is exhausted).
-/

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

/-- Integer operators have no result on anything but two integers. -/
theorem binOpSem_int_none {s : Store} {op : BinOp} {l r : Value}
    (hop : op = .sub ∨ op = .mul ∨ op = .div ∨ op = .mod)
    (h : ¬ ((∃ a, l = .int a) ∧ ∃ b, r = .int b)) : binOpSem s op l r = none := by
  rcases hop with rfl | rfl | rfl | rfl <;>
  cases l <;> cases r <;> simp_all [binOpSem]

theorem I64_wrap (z : Int) : I64 (wrap64 z) := wrap64_range z

theorem ofInt_sub' (a b : Int) :
    BitVec.ofInt 64 (a - b) = BitVec.ofInt 64 a - BitVec.ofInt 64 b := by
  rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]

theorem ofInt_wrap (z : Int) : BitVec.ofInt 64 (wrap64 z) = BitVec.ofInt 64 z := ofInt_wrap64 z

section
variable {code : List Ins} (hR : RTLoaded code)
include hR

/-- The operand registers hold `l` and `r`. -/
structure Operands (H : CloMap) (m : Mem) (h : Nat) (L : GRegs) (l r : Value)
    (t1 p1 t2 p2 : BitVec 64) : Prop where
  h10 : Has L a0 t1
  h11 : Has L a1 p1
  h12 : Has L a2 t2
  h13 : Has L a3 p2
  vl : VRepr H m h l t1 p1
  vr : VRepr H m h r t2 p2

theorem run_sub {H : CloMap} {s : Store} {m : Mem} {h : Nat} {L : GRegs} {o : Array String}
    {l r : Value} {t1 p1 t2 p2 rr : BitVec 64} (hop : Operands H m h L l r t1 p1 t2 p2)
    (hra : Has L ra rr) (hal : rr.toNat % 4 = 0) :
    Reaches code ⟨pcOf subPos, L, m, o⟩ (fun B => B.out = o ∧ B.mem = m ∧
      match binOpSem s .sub l r with
      | some v => B.pc = rr ∧ InA H m h B.regs v ∧ Keep [t0, a1] L B.regs
      | none => B.pc = pcOf errPos) := by
  obtain ⟨h10, h11, h12, h13, vl, vr⟩ := hop
  have k10 := has_mem h10 (by decide); have k11 := has_mem h11 (by decide)
  have k12 := has_mem h12 (by decide); have k13 := has_mem h13 (by decide)
  have k1 := has_mem hra (by decide)
  have e10 := srcVal_of_has h10; have e11 := srcVal_of_has h11; have e12 := srcVal_of_has h12
  have e13 := srcVal_of_has h13; have e1 := srcVal_of_has hra
  simp only [a0, a1, a2, a3, ra] at k10 k11 k12 k13 k1 e10 e11 e12 e13 e1
  apply run_seg hR.fits hR.sub 0 subPos (by simp) (subCode subPos) (by simp)
    (KP := fun _ _ _ => False) (fun _ _ _ h => h.elim)
  wp_simp [subCode, subPos, mulPos, addPos, ccPos, csPos, dpPos, nfPos, trPos, scPos, cpPos, itPos,
    psPos, k10, k11, k12, k13, k1, e10, e11, e12, e13, e1]
  by_cases hint : (∃ a, l = .int a) ∧ ∃ b, r = .int b
  · obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := hint
    obtain ⟨rfl, rfl, -⟩ := vl; obtain ⟨rfl, rfl, -⟩ := vr
    refine ⟨hal, reach_here ⟨rfl, rfl, ?_⟩⟩
    simp only [binOpSem]
    refine ⟨by first | rfl | trivial, ⟨(2 : BitVec 64), BitVec.ofInt 64 a - BitVec.ofInt 64 b, ?_, ?_, rfl, ?_,
      I64_wrap _⟩, ?_⟩
    · reg_simp; exact h10
    · reg_simp
    · rw [ofInt_wrap, ofInt_sub']
    · reg_simp; exact Keep.refl _ _
  · have hn := binOpSem_int_none (s := s) (.inl rfl) hint
    have ht : t1 ≠ 2#64 ∨ t2 ≠ 2#64 := Classical.byContradiction fun hc => by
      simp only [not_or] at hc
      exact hint ⟨vl.tag_int.mp (Classical.not_not.mp hc.1), vr.tag_int.mp (Classical.not_not.mp hc.2)⟩
    split
    · exact reach_here ⟨rfl, rfl, by rw [hn]⟩
    · split
      · exact reach_here ⟨rfl, rfl, by rw [hn]⟩
      · next h1 h2 => simp_all

theorem run_mul {H : CloMap} {s : Store} {m : Mem} {h : Nat} {L : GRegs} {o : Array String}
    {l r : Value} {t1 p1 t2 p2 rr : BitVec 64} (hop : Operands H m h L l r t1 p1 t2 p2)
    (hra : Has L ra rr) (hal : rr.toNat % 4 = 0) :
    Reaches code ⟨pcOf mulPos, L, m, o⟩ (fun B => B.out = o ∧ B.mem = m ∧
      match binOpSem s .mul l r with
      | some v => B.pc = rr ∧ InA H m h B.regs v ∧ Keep [ra, t0, a0, a1, a2, a3, s10] L B.regs
      | none => B.pc = pcOf errPos) := by
  obtain ⟨h10, h11, h12, h13, vl, vr⟩ := hop
  have k10 := has_mem h10 (by decide); have k11 := has_mem h11 (by decide)
  have k12 := has_mem h12 (by decide); have k13 := has_mem h13 (by decide)
  have k1 := has_mem hra (by decide)
  have e10 := srcVal_of_has h10; have e11 := srcVal_of_has h11; have e12 := srcVal_of_has h12
  have e13 := srcVal_of_has h13; have e1 := srcVal_of_has hra
  simp only [a0, a1, a2, a3, ra] at k10 k11 k12 k13 k1 e10 e11 e12 e13 e1
  apply run_seg hR.fits hR.mul 0 mulPos (by simp) (mulCode mulPos) (by simp)
    (KP := fun _ _ _ => False) (fun _ _ _ h => h.elim)
  by_cases hint : (∃ a, l = .int a) ∧ ∃ b, r = .int b
  · obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := hint
    obtain ⟨rfl, rfl, ha1, ha2⟩ := vl; obtain ⟨rfl, rfl, hb1, hb2⟩ := vr
    have hat : (BitVec.ofInt 64 a).toInt = a := toInt_ofInt_small a ha1 ha2
    have hbt : (BitVec.ofInt 64 b).toInt = b := toInt_ofInt_small b hb1 hb2
    wp_simp [mulCode, mulPos, subPos, mulPos, divPos, modPos, addPos, ccPos, csPos, dpPos, nfPos, trPos,
      scPos, cpPos, itPos, psPos, k10, k11, k12, k13, k1, e10, e11, e12, e13, e1, hat, hbt]
    refine ⟨hal, reach_here ⟨rfl, rfl, ?_⟩⟩
    simp only [binOpSem]
    refine ⟨by first | rfl | trivial, ⟨(2 : BitVec 64), BitVec.ofInt 64 a * BitVec.ofInt 64 b, ?_, ?_,
      rfl, ?_, I64_wrap _⟩, ?_⟩
    · reg_simp
    · reg_simp
    · rw [ofInt_wrap, BitVec.ofInt_mul]
    · reg_simp; exact Keep.refl _ _
  · have hn := binOpSem_int_none (s := s) (.inr (.inl rfl)) hint
    have ht : t1 ≠ 2#64 ∨ t2 ≠ 2#64 := Classical.byContradiction fun hc => by
      simp only [not_or] at hc
      exact hint ⟨vl.tag_int.mp (Classical.not_not.mp hc.1), vr.tag_int.mp (Classical.not_not.mp hc.2)⟩
    wp_simp [mulCode, mulPos, subPos, mulPos, divPos, modPos, addPos, ccPos, csPos, dpPos, nfPos, trPos,
      scPos, cpPos, itPos, psPos, k10, k11, k12, k13, k1, e10, e11, e12, e13, e1]
    split
    · exact reach_here ⟨rfl, rfl, by rw [hn]⟩
    · split
      · exact reach_here ⟨rfl, rfl, by rw [hn]⟩
      · next h1 h2 => simp_all

theorem run_div {H : CloMap} {s : Store} {m : Mem} {h : Nat} {L : GRegs} {o : Array String}
    {l r : Value} {t1 p1 t2 p2 rr : BitVec 64} (hop : Operands H m h L l r t1 p1 t2 p2)
    (hra : Has L ra rr) (hal : rr.toNat % 4 = 0) :
    Reaches code ⟨pcOf divPos, L, m, o⟩ (fun B => B.out = o ∧ B.mem = m ∧
      match binOpSem s .div l r with
      | some v => B.pc = rr ∧ InA H m h B.regs v ∧ Keep [ra, t0, a0, a1, a2, a3, s10] L B.regs
      | none => B.pc = pcOf errPos) := by
  obtain ⟨h10, h11, h12, h13, vl, vr⟩ := hop
  have k10 := has_mem h10 (by decide); have k11 := has_mem h11 (by decide)
  have k12 := has_mem h12 (by decide); have k13 := has_mem h13 (by decide)
  have k1 := has_mem hra (by decide)
  have e10 := srcVal_of_has h10; have e11 := srcVal_of_has h11; have e12 := srcVal_of_has h12
  have e13 := srcVal_of_has h13; have e1 := srcVal_of_has hra
  simp only [a0, a1, a2, a3, ra] at k10 k11 k12 k13 k1 e10 e11 e12 e13 e1
  apply run_seg hR.fits hR.div 0 divPos (by simp) (divCode divPos) (by simp)
    (KP := fun _ _ _ => False) (fun _ _ _ h => h.elim)
  by_cases hint : (∃ a, l = .int a) ∧ ∃ b, r = .int b
  · obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := hint
    obtain ⟨rfl, rfl, ha1, ha2⟩ := vl; obtain ⟨rfl, rfl, hb1, hb2⟩ := vr
    have hat : (BitVec.ofInt 64 a).toInt = a := toInt_ofInt_small a ha1 ha2
    have hbt : (BitVec.ofInt 64 b).toInt = b := toInt_ofInt_small b hb1 hb2
    by_cases hb0 : b = 0
    · subst hb0
      wp_simp [divCode, divPos, subPos, mulPos, divPos, modPos, addPos, ccPos, csPos, dpPos, nfPos,
        trPos, scPos, cpPos, itPos, psPos, k10, k11, k12, k13, k1, e10, e11, e12, e13, e1]
      exact reach_here ⟨rfl, rfl, by simp [binOpSem]⟩
    · have hbw : BitVec.ofInt 64 b ≠ 0 := fun e => hb0 (by rw [← hbt, e]; rfl)
      have hbt' : (BitVec.ofInt 64 b).toInt ≠ 0 := by rw [hbt]; exact hb0
      wp_simp [divCode, divPos, subPos, mulPos, divPos, modPos, addPos, ccPos, csPos, dpPos, nfPos,
        trPos, scPos, cpPos, itPos, psPos, k10, k11, k12, k13, k1, e10, e11, e12, e13, e1, hbw, hbt', hat, hbt]
      refine ⟨hal, reach_here ⟨rfl, rfl, ?_⟩⟩
      simp only [binOpSem, beq_iff_eq, hb0, if_false]
      refine ⟨by first | rfl | trivial, ⟨(2 : BitVec 64), BitVec.ofInt 64 (a.tdiv b), ?_, ?_,
        rfl, ?_, I64_wrap _⟩, ?_⟩
      · reg_simp
      · reg_simp
      · rw [ofInt_wrap]
      · reg_simp; exact Keep.refl _ _
  · have hn := binOpSem_int_none (s := s) (.inr (.inr (.inl rfl))) hint
    have ht : t1 ≠ 2#64 ∨ t2 ≠ 2#64 := Classical.byContradiction fun hc => by
      simp only [not_or] at hc
      exact hint ⟨vl.tag_int.mp (Classical.not_not.mp hc.1), vr.tag_int.mp (Classical.not_not.mp hc.2)⟩
    wp_simp [divCode, divPos, subPos, mulPos, divPos, modPos, addPos, ccPos, csPos, dpPos, nfPos, trPos,
      scPos, cpPos, itPos, psPos, k10, k11, k12, k13, k1, e10, e11, e12, e13, e1]
    split
    · exact reach_here ⟨rfl, rfl, by rw [hn]⟩
    · split
      · exact reach_here ⟨rfl, rfl, by rw [hn]⟩
      · next h1 h2 => simp_all

theorem run_mod {H : CloMap} {s : Store} {m : Mem} {h : Nat} {L : GRegs} {o : Array String}
    {l r : Value} {t1 p1 t2 p2 rr : BitVec 64} (hop : Operands H m h L l r t1 p1 t2 p2)
    (hra : Has L ra rr) (hal : rr.toNat % 4 = 0) :
    Reaches code ⟨pcOf modPos, L, m, o⟩ (fun B => B.out = o ∧ B.mem = m ∧
      match binOpSem s .mod l r with
      | some v => B.pc = rr ∧ InA H m h B.regs v ∧ Keep [ra, t0, a0, a1, a2, a3, s10] L B.regs
      | none => B.pc = pcOf errPos) := by
  obtain ⟨h10, h11, h12, h13, vl, vr⟩ := hop
  have k10 := has_mem h10 (by decide); have k11 := has_mem h11 (by decide)
  have k12 := has_mem h12 (by decide); have k13 := has_mem h13 (by decide)
  have k1 := has_mem hra (by decide)
  have e10 := srcVal_of_has h10; have e11 := srcVal_of_has h11; have e12 := srcVal_of_has h12
  have e13 := srcVal_of_has h13; have e1 := srcVal_of_has hra
  simp only [a0, a1, a2, a3, ra] at k10 k11 k12 k13 k1 e10 e11 e12 e13 e1
  apply run_seg hR.fits hR.mod 0 modPos (by simp) (modCode modPos) (by simp)
    (KP := fun _ _ _ => False) (fun _ _ _ h => h.elim)
  by_cases hint : (∃ a, l = .int a) ∧ ∃ b, r = .int b
  · obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := hint
    obtain ⟨rfl, rfl, ha1, ha2⟩ := vl; obtain ⟨rfl, rfl, hb1, hb2⟩ := vr
    have hat : (BitVec.ofInt 64 a).toInt = a := toInt_ofInt_small a ha1 ha2
    have hbt : (BitVec.ofInt 64 b).toInt = b := toInt_ofInt_small b hb1 hb2
    by_cases hb0 : b = 0
    · subst hb0
      wp_simp [modCode, modPos, subPos, mulPos, divPos, modPos, addPos, ccPos, csPos, dpPos, nfPos,
        trPos, scPos, cpPos, itPos, psPos, k10, k11, k12, k13, k1, e10, e11, e12, e13, e1]
      exact reach_here ⟨rfl, rfl, by simp [binOpSem]⟩
    · have hbw : BitVec.ofInt 64 b ≠ 0 := fun e => hb0 (by rw [← hbt, e]; rfl)
      have hbt' : (BitVec.ofInt 64 b).toInt ≠ 0 := by rw [hbt]; exact hb0
      wp_simp [modCode, modPos, subPos, mulPos, divPos, modPos, addPos, ccPos, csPos, dpPos, nfPos,
        trPos, scPos, cpPos, itPos, psPos, k10, k11, k12, k13, k1, e10, e11, e12, e13, e1, hbw, hbt', hat, hbt]
      refine ⟨hal, reach_here ⟨rfl, rfl, ?_⟩⟩
      simp only [binOpSem, beq_iff_eq, hb0, if_false]
      refine ⟨by first | rfl | trivial, ⟨(2 : BitVec 64), BitVec.ofInt 64 (a.tmod b), ?_, ?_,
        rfl, ?_, I64_wrap _⟩, ?_⟩
      · reg_simp
      · reg_simp
      · rw [ofInt_wrap]
      · reg_simp; exact Keep.refl _ _
  · have hn := binOpSem_int_none (s := s) (.inr (.inr (.inr rfl))) hint
    have ht : t1 ≠ 2#64 ∨ t2 ≠ 2#64 := Classical.byContradiction fun hc => by
      simp only [not_or] at hc
      exact hint ⟨vl.tag_int.mp (Classical.not_not.mp hc.1), vr.tag_int.mp (Classical.not_not.mp hc.2)⟩
    wp_simp [modCode, modPos, subPos, mulPos, divPos, modPos, addPos, ccPos, csPos, dpPos, nfPos, trPos,
      scPos, cpPos, itPos, psPos, k10, k11, k12, k13, k1, e10, e11, e12, e13, e1]
    split
    · exact reach_here ⟨rfl, rfl, by rw [hn]⟩
    · split
      · exact reach_here ⟨rfl, rfl, by rw [hn]⟩
      · next h1 h2 => simp_all

end

end Vsa.Compiler
