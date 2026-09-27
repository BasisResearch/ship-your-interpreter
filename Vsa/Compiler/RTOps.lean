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

theorem cmpL_range : ∀ (xs ys : List Char), cmpL xs ys = -1 ∨ cmpL xs ys = 0 ∨ cmpL xs ys = 1
  | [], [] => by simp [cmpL]
  | [], _ :: _ => by simp [cmpL]
  | _ :: _, [] => by simp [cmpL]
  | x :: xs, y :: ys => by
    simp only [cmpL]; split
    · exact .inl rfl
    · split
      · exact .inr (.inr rfl)
      · exact cmpL_range xs ys

/-- Selector of an ordering comparison in `a4`. -/
def selOf : BinOp → Nat
  | .lt => 0 | .le => 1 | .gt => 2 | .ge => 3 | _ => 0

/-- The truth value an ordering comparison selects from a three-way result. -/
def selRes (sel : Nat) (c : Int) : Bool :=
  if sel = 0 then decide (c < 0) else if sel = 1 then decide (c ≤ 0) else if sel = 2 then decide (0 < c)
  else decide (0 ≤ c)

/-- Three-way comparison of integers. -/
def sgnI (a b : Int) : Int := if a < b then -1 else if b < a then 1 else 0

/-- The ordering comparisons. -/
def IsOrd (op : BinOp) : Prop := op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge

theorem binOpSem_ord_int {s : Store} {op : BinOp} (hop : IsOrd op) (a b : Int) :
    binOpSem s op (.int a) (.int b) = some (.bool (selRes (selOf op) (sgnI a b))) := by
  rcases hop with rfl | rfl | rfl | rfl <;> simp only [binOpSem, selOf, selRes, sgnI] <;>
    by_cases h1 : a < b <;> by_cases h2 : b < a <;> simp [h1, h2] <;> omega

theorem binOpSem_ord_str {s : Store} {op : BinOp} (hop : IsOrd op) (a b : String) :
    binOpSem s op (.str a) (.str b) = some (.bool (selRes (selOf op) (cmpL a.toList b.toList))) := by
  obtain ⟨h1, h2, h3⟩ := cmpL_spec a.toList b.toList
  have e : a = b ↔ a.toList = b.toList := String.toList_inj.symm
  have l1 : a < b ↔ a.toList < b.toList := String.lt_iff
  have l2 : b < a ↔ b.toList < a.toList := String.lt_iff
  have hc := cmpL_range a.toList b.toList
  rcases hop with rfl | rfl | rfl | rfl <;> simp only [binOpSem, selOf, selRes] <;> congr 2 <;>
    rcases hc with hc | hc | hc <;> simp_all

theorem binOpSem_ord_none {s : Store} {op : BinOp} (hop : IsOrd op) {l r : Value}
    (hi : ¬ ((∃ a, l = .int a) ∧ ∃ b, r = .int b)) (hs : ¬ ((∃ a, l = .str a) ∧ ∃ b, r = .str b)) :
    binOpSem s op l r = none := by
  rcases hop with rfl | rfl | rfl | rfl <;> cases l <;> cases r <;> simp_all [binOpSem]

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

/-- Registers the ordering comparison may change. -/
def cmpClob : List Nat := [ra, t0, t1, t2, t3, t4, t5, a0, a1, s10]

/-- The selection tail of the ordering comparison, from the three-way result in `a0`. -/
theorem cmp_sel {L L0 : GRegs} {m : Mem} {o : Array String} {c : Int} {sel : Nat} {rr : BitVec 64}
    (hc : c = -1 ∨ c = 0 ∨ c = 1) (hsel : sel < 4) (h10 : Has L a0 (BitVec.ofInt 64 c))
    (h14 : Has L a4 (BitVec.ofNat 64 sel)) (h26 : Has L s10 rr) (hal : rr.toNat % 4 = 0)
    (hk : Keep cmpClob L0 L) :
    Reaches code ⟨pcOf (cmpPos + 16), L, m, o⟩ (fun B => B.pc = rr ∧ B.mem = m ∧ B.out = o ∧
      Has B.regs a0 1 ∧ Has B.regs a1 (if selRes sel c then 1 else 0) ∧ Keep cmpClob L0 B.regs) := by
  have k10 := has_mem h10 (by decide); have k14 := has_mem h14 (by decide)
  have k26 := has_mem h26 (by decide)
  have e10 := srcVal_of_has h10; have e14 := srcVal_of_has h14; have e26 := srcVal_of_has h26
  simp only [a0, a4, s10] at k10 k14 k26 e10 e14 e26
  -- the two endings
  have hend : ∀ (L' : GRegs) (b : Bool), Keep cmpClob L0 L' → Has L' s10 rr →
      (Has L' a1 (if b then 1 else 0) → b = selRes sel c) → Has L' a1 (if b then 1 else 0) →
      Reaches code ⟨pcOf (cmpPos + 32), L', m, o⟩ (fun B => B.pc = rr ∧ B.mem = m ∧ B.out = o ∧
        Has B.regs a0 1 ∧ Has B.regs a1 (if selRes sel c then 1 else 0) ∧ Keep cmpClob L0 B.regs) := by
    intro L' b hk' h26' hb h11'
    have k26' := has_mem h26' (by decide); have e26' := srcVal_of_has h26'
    simp only [s10] at k26' e26'
    apply run_seg hR.fits hR.cmp 32 (cmpPos + 32) rfl [mvi a0 1, mv ra s10, ret] (by decide)
      (KP := fun _ _ _ => False) (fun _ _ _ h => h.elim)
    wp_simp [k26', e26']
    refine ⟨hal, reach_here ⟨rfl, rfl, rfl, by reg_simp, ?_, by reg_simp; exact hk'⟩⟩
    rw [← hb h11']; reg_simp; exact h11'
  have htrue : ∀ (L' : GRegs), Keep cmpClob L0 L' → Has L' s10 rr → selRes sel c = true →
      Reaches code ⟨pcOf (cmpPos + 31), L', m, o⟩ (fun B => B.pc = rr ∧ B.mem = m ∧ B.out = o ∧
        Has B.regs a0 1 ∧ Has B.regs a1 (if selRes sel c then 1 else 0) ∧ Keep cmpClob L0 B.regs) := by
    intro L' hk' h26' hs
    apply run_seg hR.fits hR.cmp 31 (cmpPos + 31) rfl [mvi a1 1] (by decide)
      (KP := fun L'' m'' o'' => L'' = gset L' a1 1 ∧ m'' = m ∧ o'' = o)
      (fun L'' m'' o'' ⟨e1, e2, e3⟩ => by
        subst e1 e2 e3
        exact hend _ true (hk'.gset (by decide)) (by reg_simp; exact h26') (fun _ => hs.symm)
          (by reg_simp))
    wp_simp; rfl
  have hct : (BitVec.ofInt 64 c).toInt = c := toInt_ofInt_small c (by omega) (by omega)
  have hdone : ∀ (L' : GRegs), Keep cmpClob L0 L' → Has L' s10 rr → Has L' a1 0 →
      selRes sel c = false →
      Reaches code ⟨pcOf (cmpPos + 32), L', m, o⟩ (fun B => B.pc = rr ∧ B.mem = m ∧ B.out = o ∧
        Has B.regs a0 1 ∧ Has B.regs a1 (if selRes sel c then 1 else 0) ∧ Keep cmpClob L0 B.regs) :=
    fun L' hk' h26' h11' hs => hend L' false hk' h26' (fun _ => hs.symm) (by simpa using h11')
  -- the dispatch on the selector
  apply run_seg hR.fits hR.cmp 16 (cmpPos + 16) rfl [mvi a1 0, mvi t1 0,
    Br .eq a4 t1 (cmpPos + 18) (cmpPos + 24), mvi t1 1, Br .eq a4 t1 (cmpPos + 20) (cmpPos + 26),
    mvi t1 2, Br .eq a4 t1 (cmpPos + 22) (cmpPos + 28), J (cmpPos + 23) (cmpPos + 30)] (by decide)
    (KP := fun _ _ _ => False) (fun _ _ _ h => h.elim)
  wp_simp [cmpPos, eqPos, modPos, divPos, mulPos, subPos, addPos, ccPos, csPos, dpPos, nfPos, trPos,
    scPos, cpPos, itPos, psPos, k10, k14, k26, e10, e14, e26]
  have hk1 : ∀ L', Keep cmpClob L0 L' → ∀ (r : Nat) (v : BitVec 64), r ∈ cmpClob →
      Keep cmpClob L0 (gset L' r v) := fun L' h r v hr => h.gset hr
  -- one selection block: branch to done on `cond`, else to the true ending
  rcases (show sel = 0 ∨ sel = 1 ∨ sel = 2 ∨ sel = 3 by omega) with rfl | rfl | rfl | rfl
  · simp only [show BitVec.ofNat 64 0 = 0 from rfl, if_true]
    apply run_seg hR.fits hR.cmp 24 (cmpPos + 24) rfl
      [Br .ge a0 0 (cmpPos + 24) (cmpPos + 32), J (cmpPos + 25) (cmpPos + 31)] (by decide)
      (KP := fun _ _ _ => False) (fun _ _ _ h => h.elim)
    wp_simp [cmpPos, eqPos, modPos, divPos, mulPos, subPos, addPos, ccPos, csPos, dpPos, nfPos, trPos,
      scPos, cpPos, itPos, psPos, k10, e10, hct]
    split
    · next hc0 =>
      refine hdone _ ?_ ?_ ?_ ?_
      · reg_simp; exact hk
      · reg_simp; exact h26
      · reg_simp
      · simp at hc0; simp [selRes]; omega
    · next hc0 =>
      refine htrue _ ?_ ?_ ?_
      · reg_simp; exact hk
      · reg_simp; exact h26
      · simp at hc0; simp [selRes]; omega
  · simp only [show BitVec.ofNat 64 1 ≠ 0 from by decide, show BitVec.ofNat 64 1 = 1#64 from rfl,
      if_true, if_false]
    apply run_seg hR.fits hR.cmp 26 (cmpPos + 26) rfl
      [Br .lt 0 a0 (cmpPos + 26) (cmpPos + 32), J (cmpPos + 27) (cmpPos + 31)] (by decide)
      (KP := fun _ _ _ => False) (fun _ _ _ h => h.elim)
    wp_simp [cmpPos, eqPos, modPos, divPos, mulPos, subPos, addPos, ccPos, csPos, dpPos, nfPos, trPos,
      scPos, cpPos, itPos, psPos, k10, e10, hct]
    split
    · next hc0 =>
      refine hdone _ ?_ ?_ ?_ ?_
      · reg_simp; exact hk
      · reg_simp; exact h26
      · reg_simp
      · simp at hc0; simp [selRes]; omega
    · next hc0 =>
      refine htrue _ ?_ ?_ ?_
      · reg_simp; exact hk
      · reg_simp; exact h26
      · simp at hc0; simp [selRes]; omega
  · simp only [show BitVec.ofNat 64 2 ≠ 0 from by decide, show BitVec.ofNat 64 2 ≠ 1#64 from by decide,
      show BitVec.ofNat 64 2 = 2#64 from rfl, if_true, if_false]
    apply run_seg hR.fits hR.cmp 28 (cmpPos + 28) rfl
      [Br .ge 0 a0 (cmpPos + 28) (cmpPos + 32), J (cmpPos + 29) (cmpPos + 31)] (by decide)
      (KP := fun _ _ _ => False) (fun _ _ _ h => h.elim)
    wp_simp [cmpPos, eqPos, modPos, divPos, mulPos, subPos, addPos, ccPos, csPos, dpPos, nfPos, trPos,
      scPos, cpPos, itPos, psPos, k10, e10, hct]
    split
    · next hc0 =>
      refine hdone _ ?_ ?_ ?_ ?_
      · reg_simp; exact hk
      · reg_simp; exact h26
      · reg_simp
      · simp at hc0; simp [selRes]; omega
    · next hc0 =>
      refine htrue _ ?_ ?_ ?_
      · reg_simp; exact hk
      · reg_simp; exact h26
      · simp at hc0; simp [selRes]; omega
  · simp only [show BitVec.ofNat 64 3 ≠ 0 from by decide, show BitVec.ofNat 64 3 ≠ 1#64 from by decide,
      show BitVec.ofNat 64 3 ≠ 2#64 from by decide, if_false]
    apply run_seg hR.fits hR.cmp 30 (cmpPos + 30) rfl [Br .lt a0 0 (cmpPos + 30) (cmpPos + 32)]
      (by decide) (KP := fun L' m' o' => L' = gset (gset (gset (gset L 11 0) 6 0) 6 1#64) 6 2#64 ∧
        m' = m ∧ o' = o ∧ 0 ≤ c)
      (fun L' m' o' ⟨e1, e2, e3, hc0⟩ => by
        subst e1 e2 e3
        refine htrue _ ?_ ?_ ?_
        · reg_simp; exact hk
        · reg_simp; exact h26
        · simp [selRes]; omega)
    wp_simp [cmpPos, eqPos, modPos, divPos, mulPos, subPos, addPos, ccPos, csPos, dpPos, nfPos, trPos,
      scPos, cpPos, itPos, psPos, k10, e10, hct]
    split
    · next hc0 =>
      refine hdone _ ?_ ?_ ?_ ?_
      · reg_simp; exact hk
      · reg_simp; exact h26
      · reg_simp
      · simp at hc0; simp [selRes]; omega
    · next hc0 => simp at hc0; omega

theorem selOf_lt {op : BinOp} (hop : IsOrd op) : selOf op < 4 := by
  rcases hop with rfl | rfl | rfl | rfl <;> decide

/-- **Ordering comparisons.** -/
theorem run_cmp {H : CloMap} {s : Store} {m : Mem} {h : Nat} {L : GRegs} {o : Array String}
    {op : BinOp} (hop : IsOrd op) {l r : Value} {t1 p1 t2 p2 rr : BitVec 64}
    (hops : Operands H m h L l r t1 p1 t2 p2) (h14 : Has L a4 (BitVec.ofNat 64 (selOf op)))
    (hra : Has L ra rr) (hal : rr.toNat % 4 = 0) :
    Reaches code ⟨pcOf cmpPos, L, m, o⟩ (fun B => B.out = o ∧ B.mem = m ∧
      match binOpSem s op l r with
      | some v => B.pc = rr ∧ InA H m h B.regs v ∧ Keep cmpClob L B.regs
      | none => B.pc = pcOf errPos) := by
  obtain ⟨h10, h11, h12, h13, vl, vr⟩ := hops
  have k10 := has_mem h10 (by decide); have k11 := has_mem h11 (by decide)
  have k12 := has_mem h12 (by decide); have k13 := has_mem h13 (by decide)
  have k1 := has_mem hra (by decide)
  have e10 := srcVal_of_has h10; have e11 := srcVal_of_has h11; have e12 := srcVal_of_has h12
  have e13 := srcVal_of_has h13; have e1 := srcVal_of_has hra
  simp only [a0, a1, a2, a3, ra] at k10 k11 k12 k13 k1 e10 e11 e12 e13 e1
  have hsel := selOf_lt hR hop
  -- the finish from the three-way result
  have hfin : ∀ (c : Int) (v : Value) L', (c = -1 ∨ c = 0 ∨ c = 1) → Has L' a0 (BitVec.ofInt 64 c) →
      Has L' a4 (BitVec.ofNat 64 (selOf op)) → Has L' s10 rr → Keep cmpClob L L' →
      binOpSem s op l r = some v → v = .bool (selRes (selOf op) c) →
      Reaches code ⟨pcOf (cmpPos + 16), L', m, o⟩ (fun B => B.out = o ∧ B.mem = m ∧
        match binOpSem s op l r with
        | some v => B.pc = rr ∧ InA H m h B.regs v ∧ Keep cmpClob L B.regs
        | none => B.pc = pcOf errPos) := by
    intro c v L' hc g10 g14 g26 hk hb hv
    refine reaches_mono (cmp_sel hR hc hsel g10 g14 g26 hal hk) ?_
    rintro B ⟨g1, g2, g3, g4, g5, g6⟩
    refine ⟨g3, g2, ?_⟩
    rw [hb, hv]
    exact ⟨g1, ⟨1, _, g4, g5, rfl, rfl⟩, g6⟩
  have hnone : binOpSem s op l r = none → ∀ L', Reaches code ⟨pcOf errPos, L', m, o⟩ (fun B => B.out = o ∧
      B.mem = m ∧ match binOpSem s op l r with
        | some v => B.pc = rr ∧ InA H m h B.regs v ∧ Keep cmpClob L B.regs
        | none => B.pc = pcOf errPos) := fun hn L' => reach_here ⟨rfl, rfl, by rw [hn]⟩
  have hrest : ∀ L' : GRegs, Keep cmpClob L L' → Has L' a4 (BitVec.ofNat 64 (selOf op)) → True :=
    fun _ _ _ => trivial
  -- the entry block, for integers and the dispatch to strings
  apply run_seg hR.fits hR.cmp 0 cmpPos (by simp) [mv s10 ra,
    mvi t0 2, Br .ne a0 t0 (cmpPos + 2) (cmpPos + 12), Br .ne a2 t0 (cmpPos + 3) errPos,
    Br .lt a1 a3 (cmpPos + 4) (cmpPos + 8), Br .lt a3 a1 (cmpPos + 5) (cmpPos + 10),
    mvi a0 0, J (cmpPos + 7) (cmpPos + 16)] (by decide)
    (KP := fun _ _ _ => False) (fun _ _ _ h => h.elim)
  wp_simp [cmpPos, eqPos, modPos, divPos, mulPos, subPos, addPos, ccPos, csPos, dpPos, nfPos, trPos,
    scPos, cpPos, itPos, psPos, k10, k11, k12, k13, k1, e10, e11, e12, e13, e1]
  by_cases hint : (∃ a, l = .int a) ∧ ∃ b, r = .int b
  · obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := hint
    obtain ⟨rfl, rfl, ha1, ha2⟩ := vl; obtain ⟨rfl, rfl, hb1, hb2⟩ := vr
    have hat : (BitVec.ofInt 64 a).toInt = a := toInt_ofInt_small a ha1 ha2
    have hbt : (BitVec.ofInt 64 b).toInt = b := toInt_ofInt_small b hb1 hb2
    have hsem := binOpSem_ord_int (s := s) hop a b
    simp only [hat, hbt, BitVec.reduceEq, ne_eq, not_true_eq_false, if_false, ite_false]
    split
    · next hab =>
      apply run_seg hR.fits hR.cmp 8 (cmpPos + 8) rfl [mvi a0 (-1), J (cmpPos + 9) (cmpPos + 16)]
        (by decide) (KP := fun _ _ _ => False) (fun _ _ _ h => h.elim)
      wp_simp [cmpPos, eqPos, modPos, divPos, mulPos, subPos, addPos, ccPos, csPos, dpPos, nfPos, trPos,
        scPos, cpPos, itPos, psPos]
      exact hfin (-1) _ _ (.inl rfl) (by reg_simp) (by reg_simp; exact h14) (by reg_simp)
        (by reg_simp; exact Keep.refl _ _) hsem (by simp [sgnI, hab])
    · next hab =>
      split
      · next hba =>
        apply run_seg hR.fits hR.cmp 10 (cmpPos + 10) rfl [mvi a0 1, J (cmpPos + 11) (cmpPos + 16)]
          (by decide) (KP := fun _ _ _ => False) (fun _ _ _ h => h.elim)
        wp_simp [cmpPos, eqPos, modPos, divPos, mulPos, subPos, addPos, ccPos, csPos, dpPos, nfPos, trPos,
          scPos, cpPos, itPos, psPos]
        exact hfin 1 _ _ (.inr (.inr rfl)) (by reg_simp) (by reg_simp; exact h14) (by reg_simp)
          (by reg_simp; exact Keep.refl _ _) hsem (by simp [sgnI, hab, hba])
      · next hba =>
        exact hfin 0 _ _ (.inr (.inl rfl)) (by reg_simp) (by reg_simp; exact h14) (by reg_simp)
          (by reg_simp; exact Keep.refl _ _) hsem (by simp [sgnI, hab, hba])
  · have hstr : ∀ (L' : GRegs), Keep cmpClob L L' → Has L' a0 t1 → Has L' a1 p1 → Has L' a2 t2 →
        Has L' a3 p2 → Has L' a4 (BitVec.ofNat 64 (selOf op)) → Has L' s10 rr →
        Reaches code ⟨pcOf (cmpPos + 12), L', m, o⟩ (fun B => B.out = o ∧ B.mem = m ∧
          match binOpSem s op l r with
          | some v => B.pc = rr ∧ InA H m h B.regs v ∧ Keep cmpClob L B.regs
          | none => B.pc = pcOf errPos) := by
      intro L' hk g10 g11 g12 g13 g14 g26
      have k10 := has_mem g10 (by decide); have k12 := has_mem g12 (by decide)
      have e10 := srcVal_of_has g10; have e12 := srcVal_of_has g12
      simp only [a0, a2] at k10 k12 e10 e12
      apply run_seg hR.fits hR.cmp 12 (cmpPos + 12) rfl [mvi t0 3, Br .ne a0 t0 (cmpPos + 13) errPos,
        Br .ne a2 t0 (cmpPos + 14) errPos, Call (cmpPos + 15) scPos] (by decide)
        (KP := fun _ _ _ => False) (fun _ _ _ h => h.elim)
      wp_simp [cmpPos, eqPos, modPos, divPos, mulPos, subPos, addPos, ccPos, csPos, dpPos, nfPos, trPos,
        scPos, cpPos, itPos, psPos, k10, k12, e10, e12]
      by_cases hs2 : (∃ a, l = .str a) ∧ ∃ b, r = .str b
      · obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := hs2
        obtain ⟨rfl, ha⟩ := vl; obtain ⟨rfl, hb⟩ := vr
        simp only [BitVec.reduceEq, ne_eq, not_true_eq_false, if_false, ite_false]
        have hpa : p1 = BitVec.ofNat 64 p1.toNat := by simp
        have hpb : p2 = BitVec.ofNat 64 p2.toNat := by simp
        refine ex_bind (run_sc hR.fits hR.sc (p := p1.toNat) (q := p2.toNat)
          (by reg_simp; rw [← hpa]; exact g11) (by reg_simp; rw [← hpb]; exact g13)
          (Has.set_self _ _ (by decide) (by decide)) (pcOf_aligned (posOK_lt (by decide)))
          ha.str hb.str) ?_
        rintro B ⟨hpc, hm, ho, h10', hk'⟩
        obtain ⟨pc, L2, m2, o2⟩ := B
        simp only at hpc hm ho h10' hk'; subst hpc hm ho
        exact hfin _ _ _ (cmpL_range _ _) h10' (hk'.has (by decide) (by reg_simp; exact g14))
          (hk'.has (by decide) (by reg_simp; exact g26))
          (Keep.trans hk (Keep.trans (by reg_simp; exact Keep.refl _ _) (hk'.mono (by decide))))
          (binOpSem_ord_str hop a b) rfl
      · have hn := binOpSem_ord_none (s := s) hop hint hs2
        have ht : t1 ≠ 3#64 ∨ t2 ≠ 3#64 := Classical.byContradiction fun hc => by
          simp only [not_or] at hc
          exact hs2 ⟨vl.tag_str (Classical.not_not.mp hc.1), vr.tag_str (Classical.not_not.mp hc.2)⟩
        split
        · exact hnone hn _
        · split
          · exact hnone hn _
          · next h1 h2 => simp_all
    split
    · exact hstr _ (by reg_simp; exact Keep.refl _ _) (by reg_simp; exact h10) (by reg_simp; exact h11)
        (by reg_simp; exact h12) (by reg_simp; exact h13) (by reg_simp; exact h14) (by reg_simp)
    · next ht1 =>
      have ht1' : t1 = 2 := by simpa using ht1
      have ht2 : ¬ t2 = 2#64 := fun h2 => hint ⟨vl.tag_int.mp ht1', vr.tag_int.mp h2⟩
      have hs2 : ¬ ((∃ a, l = .str a) ∧ ∃ b, r = .str b) := by
        rintro ⟨⟨a, rfl⟩, -⟩; obtain ⟨rfl, -⟩ := vl; exact absurd ht1' (by decide)
      rw [if_pos ht2]
      exact hnone (binOpSem_ord_none hop hint hs2) _

end

end Vsa.Compiler
