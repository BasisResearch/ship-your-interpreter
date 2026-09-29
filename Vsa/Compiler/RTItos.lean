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

theorem foldl_push_toList (l : List Char) (s : String) :
    (l.foldl String.push s).toList = s.toList ++ l := by
  induction l generalizing s with
  | nil => simp
  | cons c l ih => simp [ih]

theorem intToString_toList (z : Int) : (intToString z).toList =
    (if z < 0 then ['-'] else []) ++ ((digitsLE z.natAbs).map Nat.digitChar).reverse := by
  rw [intToString_eq, natToString_eq, String.toList_append, foldl_push_toList]
  split <;> simp

/-- Character `q` of the rendering of an integer with digits `ds` (least
significant first) and sign flag `sg`, as a character code. -/
def itChar (sg : Nat) (ds : List Nat) (q : Nat) : Nat :=
  if q < sg then 45 else ds[ds.length - 1 - (q - sg)]! + 48

theorem digitChar_toNat {d : Nat} (h : d < 10) : (Nat.digitChar d).toNat = d + 48 := by
  have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 := by omega
  rcases this with h|h|h|h|h|h|h|h|h|h <;> subst h <;> rfl

theorem getElem_digits (pre : List Char) (hpre : ∀ c ∈ pre, c = '-') (ds : List Nat)
    (hds : ∀ d ∈ ds, d < 10) (q : Nat) (hq : q < (pre ++ (ds.map Nat.digitChar).reverse).length) :
    ((pre ++ (ds.map Nat.digitChar).reverse)[q]'hq).toNat = itChar pre.length ds q := by
  simp only [List.length_append, List.length_reverse, List.length_map] at hq
  unfold itChar
  by_cases h : q < pre.length
  · rw [if_pos h, List.getElem_append_left h, hpre _ (List.getElem_mem h)]; rfl
  · rw [if_neg h, List.getElem_append_right (by simpa using h)]
    simp only [List.getElem_reverse, List.getElem_map, List.length_map]
    have hi : ds.length - 1 - (q - pre.length) < ds.length := by omega
    rw [getElem!_pos ds _ hi, digitChar_toNat (hds _ (List.getElem_mem hi))]

theorem itChar_eq (z : Int) (q : Nat) (hq : q < (intToString z).toList.length) :
    ((intToString z).toList[q]'hq).toNat =
      itChar (if z < 0 then 1 else 0) (digitsLE z.natAbs) q := by
  have hl := intToString_toList z
  have e : (if z < 0 then 1 else 0) = (if z < 0 then ['-'] else []).length := by split <;> rfl
  rw [e, ← getElem_digits _ (by split <;> simp) _ (digitsLE_lt z.natAbs) q (by rw [← hl]; exact hq)]
  simp only [hl]

theorem intToString_length (z : Int) :
    (intToString z).toList.length = (if z < 0 then 1 else 0) + (digitsLE z.natAbs).length := by
  rw [intToString_toList]; split <;> simp <;> omega

theorem natAbs_le (x : BitVec 64) : x.toInt.natAbs ≤ 2 ^ 63 := by
  have hb1 := BitVec.le_toInt x
  have hb2 : x.toInt < 2 ^ (64 - 1) := BitVec.toInt_lt
  rw [show (2 : Int) ^ (64 - 1) = 9223372036854775808 by decide] at hb1 hb2
  omega

theorem digits_len (x : BitVec 64) : (digitsLE x.toInt.natAbs).length ≤ 19 :=
  digitsLE_length_le 18 _ (by have := natAbs_le x; simp only [Nat.reducePow, Nat.reduceAdd] at *; omega)

theorem intToString_len_le (x : BitVec 64) : (intToString x.toInt).toList.length ≤ 20 := by
  have hl := intToString_length x.toInt; have hK := digits_len x; split at hl <;> omega

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

/-- The digit loop: the digits of `|x|` (least significant first) are appended to the buffer. -/
theorem it_digits : ∀ (N : Nat) (x : BitVec 64) (j : Nat) (ds : List Nat) (L' : GRegs) (m' : Mem)
    (o : Array String), x.toInt.natAbs = N →
    Has L' s4 x → Has L' s5 (BitVec.ofNat 64 j) → Has L' s6 (BitVec.ofNat 64 (bufBase + 8 * j)) →
    ds.length = j → j + (digitsLE N).length ≤ 20 →
    Reaches code ⟨pcOf (itPos + 16), L', m', o⟩ (fun B => B.pc = pcOf (itPos + 34) ∧ B.out = o ∧
      Has B.regs s5 (BitVec.ofNat 64 (ds ++ digitsLE N).length) ∧
      Has B.regs s6 (BitVec.ofNat 64 (bufBase + 8 * (ds ++ digitsLE N).length)) ∧
      Keep itLoopClob L' B.regs ∧
      (∀ q, j ≤ q → q < (ds ++ digitsLE N).length →
        rdW B.mem (bufBase + 8 * q) = BitVec.ofNat 64 ((ds ++ digitsLE N)[q]! + 48)) ∧
      (∀ a, a % 8 = 0 → (a + 8 ≤ bufBase + 8 * j ∨ bufBase + 160 ≤ a) → rdW B.mem a = rdW m' a)) := by
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
  intro x j ds L' m' o hN h4 h5 h6 hj hlen
  have hb : bufBase = 0x80080000 := rfl
  have hpos : 1 ≤ (digitsLE N).length := by unfold digitsLE; split <;> simp
  refine ex_bind (it_step hfit hseg h4 h5 h6 (by omega)) ?_
  rintro B1 ⟨ho1, hm1, h4', h5', h6', hk1, hpc1⟩
  obtain ⟨pc1, L1, mm1, oo1⟩ := B1
  simp only at ho1 hm1 h4' h5' h6' hk1 hpc1
  subst ho1
  have hw := rdW_write mm1 (bufBase + 8 * j) (BitVec.ofNat 64 (N % 10 + 48))
  by_cases hsmall : N < 10
  · rw [if_pos ((tdiv_word_zero x).mpr (by omega))] at hpc1
    have hdl : digitsLE N = [N] := digitsLE_small hsmall
    rw [hdl]
    refine reach_here ⟨hpc1, rfl, by simpa [hj] using h5', by simpa [hj] using h6', hk1, ?_, ?_⟩
    · intro q hq1 hq2
      simp [hj] at hq2
      have : q = j := by omega
      subst this
      rw [hm1, hN, rdW_write]
      simp [hj, Nat.mod_eq_of_lt hsmall]
    · intro a ha hout
      rw [hm1]
      exact rdW_write_other _ _ _ _ (by omega)
  · rw [if_neg (fun h => hsmall (hN ▸ (tdiv_word_zero x).mp h))] at hpc1
    have hdl : digitsLE N = N % 10 :: digitsLE (N / 10) := digitsLE_big hsmall
    obtain ⟨hx1, hx'⟩ := tdiv_word x
    subst hpc1
    refine ex_bind (ih (N / 10) (by omega) _ (j + 1) (ds ++ [N % 10]) L1 mm1 oo1
      (by rw [hx1, hx', hN]) h4' h5' h6' (by simp [hj]) (by rw [hdl] at hlen; simp at hlen ⊢; omega)) ?_
    rintro B ⟨hpc, hof, h5f, h6f, hkf, hcells, hframe⟩
    have heq : ds ++ [N % 10] ++ digitsLE (N / 10) = ds ++ digitsLE N := by rw [hdl]; simp
    rw [heq] at h5f h6f hcells
    refine reach_here ⟨hpc, hof, h5f, h6f, hk1.trans hkf, ?_, ?_⟩
    · intro q hq1 hq2
      by_cases hqj : q = j
      · subst hqj
        rw [hframe _ (by omega) (by omega), hm1, hN, rdW_write]
        congr 2
        rw [hdl]; simp [hj]
      · exact hcells q (by omega) hq2
    · intro a ha hout
      rw [hframe a ha (by omega), hm1]
      exact rdW_write_other _ _ _ _ (by omega)

/-- The copy loop head of `itos` with `i` buffered digits left. -/
def ItCopy (L0 : GRegs) (m : Mem) (o : Array String) (d : Nat) (r : BitVec 64) (sg : Nat)
    (ds : List Nat) (i : Nat) (A : AM) : Prop :=
  A.pc = pcOf (itPos + 42) ∧ A.out = o ∧ i ≤ ds.length ∧
    Has A.regs s5 (BitVec.ofNat 64 i) ∧ Has A.regs s6 (BitVec.ofNat 64 (bufBase + 8 * i)) ∧
    Has A.regs t1 (BitVec.ofNat 64 (d + 8 + 8 * (sg + ds.length - i))) ∧ Has A.regs s9 r ∧
    Keep itClob L0 A.regs ∧
    (∀ q, q < i → rdW A.mem (bufBase + 8 * q) = BitVec.ofNat 64 (ds[q]! + 48)) ∧
    rdW A.mem d = BitVec.ofNat 64 (sg + ds.length) ∧
    (∀ q, q < sg + ds.length - i → rdW A.mem (d + 8 + 8 * q) = BitVec.ofNat 64 (itChar sg ds q)) ∧
    (∀ a, a % 8 = 0 → (a + 8 ≤ d ∨ d + 8 + 8 * (sg + ds.length) ≤ a) →
      (a + 8 ≤ bufBase ∨ bufBase + 160 ≤ a) → rdW A.mem a = rdW m a)

/-- The destination of `itos`: writable, aligned, and apart from the digit buffer. -/
structure ItDest (d : Nat) : Prop where
  lo : tohostAddr + 16 ≤ d
  hi : d + 168 ≤ 2 ^ 32
  al : d % 8 = 0
  buf : d + 168 ≤ bufBase ∨ bufBase + 160 ≤ d

theorem it_copy {L0 : GRegs} {m : Mem} {o : Array String} {d : Nat} {r : BitVec 64} {sg : Nat}
    {ds : List Nat} (hd : ItDest d) (hsg : sg ≤ 1) (hK : sg + ds.length ≤ 20)
    (hds : ∀ q ∈ ds, q < 10) (hal : r.toNat % 4 = 0) :
    ∀ i A, ItCopy L0 m o d r sg ds i A → Reaches code A (fun B => B.pc = r ∧ B.out = o ∧
      Has B.regs a3 (BitVec.ofNat 64 (d + 8 + 8 * (sg + ds.length))) ∧ Keep itClob L0 B.regs ∧
      rdW B.mem d = BitVec.ofNat 64 (sg + ds.length) ∧
      (∀ q, q < sg + ds.length → rdW B.mem (d + 8 + 8 * q) = BitVec.ofNat 64 (itChar sg ds q)) ∧
      (∀ a, a % 8 = 0 → (a + 8 ≤ d ∨ d + 8 + 8 * (sg + ds.length) ≤ a) →
        (a + 8 ≤ bufBase ∨ bufBase + 160 ≤ a) → rdW B.mem a = rdW m a)) := by
  have hb : bufBase = 0x80080000 := rfl
  have ht : tohostAddr = 0x8001ad00 := rfl
  have := hd.lo; have := hd.hi; have := hd.al; have := hd.buf
  refine loop_run (fun i A hA => ?_) (fun A hA => ?_)
  · obtain ⟨hpc, ho, hi, h21, h22, h6, h25, hk, hbuf, hlen, hstr, hfr⟩ := hA
    obtain ⟨pc, L', m', o'⟩ := A
    simp only at hpc ho h21 h22 h6 h25 hk hbuf hlen hstr hfr; subst hpc ho
    have k21 := has_mem h21 (by decide); have k22 := has_mem h22 (by decide)
    have k6 := has_mem h6 (by decide)
    have e21 := srcVal_of_has h21; have e22 := srcVal_of_has h22; have e6 := srcVal_of_has h6
    simp only [s5, s6, t1] at k21 k22 k6 e21 e22 e6
    have hj0 : BitVec.ofNat 64 (i + 1) ≠ 0 := ofNat_ne_zero (by omega) (by omega)
    have hbn : (BitVec.ofNat 64 (bufBase + 8 * (i + 1) - 8)).toNat = bufBase + 8 * i := by
      rw [toNat_ofNat_lt (by omega)]; omega
    have htn : (BitVec.ofNat 64 (d + 8 + 8 * (sg + ds.length - (i + 1)))).toNat =
        d + 8 + 8 * (sg + ds.length - (i + 1)) := toNat_ofNat_lt (by omega)
    have hc := hbuf i (by omega)
    have hne : d + 8 + 8 * (sg + ds.length - (i + 1)) ≠ tohostAddr := by omega
    apply run_at' hfit hseg 42 (itPos + 42) rfl
    wp_simp [itCode, itPos, psPos, k21, k22, k6, e21, e22, e6, hj0, hbn, htn, hc, hne]
    refine ⟨⟨by omega, by omega, .inr (by omega)⟩, ⟨by omega, by omega, by omega, by omega⟩,
      reach_here ⟨rfl, rfl, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · reg_simp; try bv_eq
    · reg_simp; try bv_eq
    · reg_simp; try bv_eq
    · reg_simp; exact h25
    · reg_simp; exact hk
    · intro q hq
      rw [rdW_upd (by omega) (by omega), if_neg (by omega)]
      exact hbuf q (by omega)
    · rw [rdW_upd (by omega) (by omega), if_neg (by omega)]; exact hlen
    · intro q hq
      rw [rdW_upd (by omega) (by omega)]
      split
      · next he =>
        have hq' : q = sg + ds.length - (i + 1) := by omega
        subst hq'
        have e1 : ds.length - 1 - (sg + ds.length - (i + 1) - sg) = i := by omega
        simp only [itChar, if_neg (show ¬(sg + ds.length - (i + 1) < sg) by omega), e1]
      · exact hstr q (by omega)
    · intro a ha h1 h2
      rw [rdW_upd (by omega) ha, if_neg (by omega)]
      exact hfr a ha h1 h2
  · obtain ⟨hpc, ho, hi, h21, h22, h6, h25, hk, hbuf, hlen, hstr, hfr⟩ := hA
    obtain ⟨pc, L', m', o'⟩ := A
    simp only at hpc ho h21 h22 h6 h25 hk hbuf hlen hstr hfr; subst hpc ho
    have k21 := has_mem h21 (by decide); have k6 := has_mem h6 (by decide)
    have k25 := has_mem h25 (by decide)
    have e21 := srcVal_of_has h21; have e6 := srcVal_of_has h6; have e25 := srcVal_of_has h25
    simp only [s5, t1, s9] at k21 k6 k25 e21 e6 e25
    apply run_at' hfit hseg 42 (itPos + 42) rfl
    wp_simp [itCode, itPos, psPos, k21, e21]
    apply run_at' hfit hseg 49 (itPos + 49) rfl
    wp_simp [itCode, itPos, psPos, k6, e6, k25, e25]
    refine ⟨hal, reach_here ⟨rfl, rfl, ?_, ?_, hlen, fun q hq => hstr q (by omega), hfr⟩⟩
    · reg_simp; bv_eq
    · reg_simp; exact hk

/-- **`itos`.** -/
theorem run_it {L : GRegs} {m : Mem} {o : Array String} {x r : BitVec 64} {d : Nat}
    (h11 : Has L a1 x) (h12 : Has L a2 (BitVec.ofNat 64 d)) (hr : Has L ra r)
    (hal : r.toNat % 4 = 0) (hd : ItDest d) :
    Reaches code ⟨pcOf itPos, L, m, o⟩ (fun B => B.pc = r ∧ B.out = o ∧
      StrW B.mem d (intToString x.toInt).toList ∧
      Has B.regs a3 (BitVec.ofNat 64 (d + 8 + 8 * (intToString x.toInt).toList.length)) ∧
      Keep itClob L B.regs ∧
      (∀ a, a % 8 = 0 → (a + 8 ≤ d ∨ d + 8 + 8 * (intToString x.toInt).toList.length ≤ a) →
        (a + 8 ≤ bufBase ∨ bufBase + 160 ≤ a) →
        rdW B.mem a = rdW m a)) := by
  have hb : bufBase = 0x80080000 := rfl
  have ht : tohostAddr = 0x8001ad00 := rfl
  have := hd.lo; have := hd.hi; have := hd.al; have := hd.buf
  have hK := digits_len x
  have hds := digitsLE_lt x.toInt.natAbs
  have hlen := intToString_length x.toInt
  -- the final state from the copy loop
  have hfin : ∀ (sg : Nat), sg = (if x.toInt < 0 then 1 else 0) → ∀ A,
      ItCopy L m o d r sg (digitsLE x.toInt.natAbs) (digitsLE x.toInt.natAbs).length A →
      Reaches code A (fun B => B.pc = r ∧ B.out = o ∧
        StrW B.mem d (intToString x.toInt).toList ∧
        Has B.regs a3 (BitVec.ofNat 64 (d + 8 + 8 * (intToString x.toInt).toList.length)) ∧
        Keep itClob L B.regs ∧
        (∀ a, a % 8 = 0 → (a + 8 ≤ d ∨ d + 8 + 8 * (intToString x.toInt).toList.length ≤ a) →
        (a + 8 ≤ bufBase ∨ bufBase + 160 ≤ a) →
          rdW B.mem a = rdW m a)) := by
    intro sg hsg A hA
    have hsg1 : sg ≤ 1 := by rw [hsg]; split <;> omega
    refine reaches_mono (it_copy hfit hseg hd hsg1 (by omega) hds hal _ _ hA) ?_
    rintro B ⟨hpc, ho, h13, hk, hl, hc, hfr⟩
    rw [← hsg] at hlen
    refine ⟨hpc, ho, ⟨by omega, by omega, hd.al, by rw [hl, hlen], fun q hq => ?_, ?_⟩, by rw [hlen]; exact h13, hk,
      fun a ha h1 h2 => hfr a ha (by rw [hlen] at h1; exact h1) h2⟩
    · rw [hc q (by omega), itChar_eq, ← hsg]
    · intro c hc'
      obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hc'
      rw [itChar_eq, ← hsg]
      unfold itChar; split
      · omega
      · have := hds (digitsLE x.toInt.natAbs)[(digitsLE x.toInt.natAbs).length - 1 - (q - sg)]!
          (by rw [getElem!_pos _ _ (by omega)]; exact List.getElem_mem (by omega))
        omega
  -- the header, from 34
  have hhead : ∀ L2 m2, Has L2 s5 (BitVec.ofNat 64 (digitsLE x.toInt.natAbs).length) →
      Has L2 s6 (BitVec.ofNat 64 (bufBase + 8 * (digitsLE x.toInt.natAbs).length)) →
      Has L2 a6 x → Has L2 a7 (BitVec.ofNat 64 d) → Has L2 s9 r → Keep itClob L L2 →
      (∀ q, q < (digitsLE x.toInt.natAbs).length →
        rdW m2 (bufBase + 8 * q) = BitVec.ofNat 64 ((digitsLE x.toInt.natAbs)[q]! + 48)) →
      (∀ a, a % 8 = 0 → (a + 8 ≤ bufBase ∨ bufBase + 160 ≤ a) → rdW m2 a = rdW m a) →
      Reaches code ⟨pcOf (itPos + 34), L2, m2, o⟩ (fun B => B.pc = r ∧ B.out = o ∧
        StrW B.mem d (intToString x.toInt).toList ∧
        Has B.regs a3 (BitVec.ofNat 64 (d + 8 + 8 * (intToString x.toInt).toList.length)) ∧
        Keep itClob L B.regs ∧
        (∀ a, a % 8 = 0 → (a + 8 ≤ d ∨ d + 8 + 8 * (intToString x.toInt).toList.length ≤ a) →
        (a + 8 ≤ bufBase ∨ bufBase + 160 ≤ a) →
          rdW B.mem a = rdW m a)) := by
    intro L2 m2 h21 h22 h16 h17 h25 hk hcells hfr
    have k21 := has_mem h21 (by decide); have k16 := has_mem h16 (by decide)
    have k17 := has_mem h17 (by decide)
    have e21 := srcVal_of_has h21; have e16 := srcVal_of_has h16; have e17 := srcVal_of_has h17
    simp only [s5, a6, a7] at k21 k16 k17 e21 e16 e17
    have hdn : (BitVec.ofNat 64 d).toNat = d := toNat_ofNat_lt (by omega)
    have hdn8 : (BitVec.ofNat 64 (d + 8)).toNat = d + 8 := toNat_ofNat_lt (by omega)
    have hne : d ≠ tohostAddr := by omega
    have hne8 : d + 8 ≠ tohostAddr := by omega
    apply run_block hfit hseg 34 8 (itPos + 34) rfl
      (KP := fun L3 m3 o3 => ItCopy L m o d r (if x.toInt < 0 then 1 else 0)
        (digitsLE x.toInt.natAbs) (digitsLE x.toInt.natAbs).length ⟨pcOf (itPos + 42), L3, m3, o3⟩)
      (fun L3 m3 o3 h => hfin _ rfl _ h) (by len_ok [itCode])
    wp_simp [itCode, itPos, psPos, k21, k16, k17, e21, e16, e17, hdn, hdn8, hne, hne8]
    split
    · next hx =>
      have hx' : ¬ x.toInt < 0 := by simpa using hx
      apply run_block hfit hseg 41 1 (itPos + 41) rfl
        (KP := fun L3 m3 o3 => ItCopy L m o d r (if x.toInt < 0 then 1 else 0)
          (digitsLE x.toInt.natAbs) (digitsLE x.toInt.natAbs).length ⟨pcOf (itPos + 42), L3, m3, o3⟩)
        (fun L3 m3 o3 h => hfin _ rfl _ h) (by len_ok [itCode])
      wp_simp [itCode, itPos, psPos, k21, k16, k17, e21, e16, e17, hdn, hdn8, hne, hne8]
      simp only [if_neg hx']
      refine ⟨⟨by omega, by omega, by omega, by omega⟩, rfl, rfl, Nat.le_refl _, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_⟩
      · reg_simp; exact h21
      · reg_simp; exact h22
      · reg_simp; bv_eq
      · reg_simp; exact h25
      · reg_simp; exact hk
      · intro q hq
        rw [rdW_upd (by omega) (by omega), if_neg (by omega)]; exact hcells q hq
      · rw [rdW_upd (by omega) (by omega), if_pos rfl]; simp
      · intro q hq; omega
      · intro a ha h1 h2
        rw [rdW_upd (by omega) ha, if_neg (by omega)]; exact hfr a ha h2
    · next hx =>
      have hx' : x.toInt < 0 := by simpa using hx
      simp only [if_pos hx']
      refine ⟨⟨by omega, by omega, by omega, by omega⟩, ⟨by omega, by omega, by omega, by omega⟩,
        rfl, rfl, Nat.le_refl _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · reg_simp; exact h21
      · reg_simp; exact h22
      · reg_simp; bv_eq
      · reg_simp; exact h25
      · reg_simp; exact hk
      · intro q hq
        rw [rdW_upd (by omega) (by omega), if_neg (by omega), rdW_upd (by omega) (by omega),
          if_neg (by omega)]
        exact hcells q hq
      · rw [rdW_upd (by omega) (by omega), if_pos rfl]; bv_eq
      · intro q hq
        have hq0 : q = 0 := by omega
        subst hq0
        rw [rdW_upd (by omega) (by omega), if_neg (by omega), rdW_upd (by omega) (by omega),
          if_pos (by omega)]
        rfl
      · intro a ha h1 h2
        rw [rdW_upd (by omega) ha, if_neg (by omega), rdW_upd (by omega) ha, if_neg (by omega)]
        exact hfr a ha h2
  -- prologue and digits
  have k11 := has_mem h11 (by decide); have k12 := has_mem h12 (by decide)
  have k1 := has_mem hr (by decide)
  have e11 := srcVal_of_has h11; have e12 := srcVal_of_has h12; have e1 := srcVal_of_has hr
  simp only [a1, a2, ra] at k11 k12 k1 e11 e12 e1
  apply run_block hfit hseg 0 16 itPos rfl
    (KP := fun L1 m1 o1 => m = m1 ∧ o = o1 ∧ Has L1 s4 x ∧ Has L1 s5 (BitVec.ofNat 64 0) ∧
      Has L1 s6 (BitVec.ofNat 64 (bufBase + 8 * 0)) ∧ Has L1 a6 x ∧ Has L1 a7 (BitVec.ofNat 64 d) ∧
      Has L1 s9 r ∧ Keep itClob L L1)
    (fun L1 m1 o1 ⟨g1, g2, g4, g5, g6, g16, g17, g25, gk⟩ => by
      subst g1 g2
      refine ex_bind (it_digits hfit hseg _ x 0 [] L1 m o rfl g4 g5 g6 rfl (by omega)) ?_
      rintro B ⟨hpc, ho, h5, h6, hk2, hcells, hfr⟩
      obtain ⟨pc, L2, m2, o2⟩ := B
      simp only at hpc ho h5 h6 hk2 hcells hfr; subst hpc ho
      exact hhead L2 m2 (by simpa using h5) (by simpa using h6) (hk2.has (by decide) g16)
        (hk2.has (by decide) g17) (hk2.has (by decide) g25)
        (gk.trans (hk2.mono (by decide))) (fun q hq => by simpa using hcells q (by omega) (by simpa using hq))
        (fun a ha hout => hfr a ha (by omega)))
    (by len_ok [itCode])
  wp_simp [itCode, itPos, psPos, k11, k12, k1, e11, e12, e1]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals reg_simp
  all_goals first | exact Keep.refl _ _ | bv_eq | rfl

end

end Vsa.Compiler
