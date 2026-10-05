import Vsa.Compiler.PrintInt
import Vsa.Compiler.CTOps

namespace Vsa.Compiler

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa.Sim

def nezW (x : BitVec 64) : BitVec 64 := if x = 0 then 0 else 1

theorem sltW_nez (x : BitVec 64) : sltW 0 x + sltW x 0 = nezW x := by
  unfold sltW nezW
  by_cases h : x = 0
  · subst h; decide
  · have hx : x.toInt ≠ 0 := fun e => h (BitVec.eq_of_toInt_eq (by simpa using e))
    rw [if_neg h]
    rcases Int.lt_or_gt_of_ne hx with h1 | h1
    · rw [if_neg (by simp; omega), if_pos (by simpa using h1)]; decide
    · rw [if_pos (by simpa using h1), if_neg (by simp; omega)]; decide

theorem flip_val (c : Bool) :
    (0 : BitVec 64) - (if c then 1 else 0) + (sign_extend (1 : BitVec 12) : BitVec 64)
      = if c then 0 else 1 := by
  cases c <;> decide

theorem mask_and (v x : BitVec 64) :
    (0 - sltW v 0) &&& x = if 2 ^ 64 ≤ 2 * v.toNat then x else 0 := by
  unfold sltW
  by_cases h : 2 ^ 64 ≤ 2 * v.toNat
  · rw [if_pos (by simpa using BitVec.toInt_neg_iff.mpr h), if_pos h,
      show (0 : BitVec 64) - 1 = BitVec.allOnes 64 by decide, BitVec.allOnes_and]
  · rw [if_neg (fun h' => h (by simpa using BitVec.toInt_neg_iff.mp (by simpa using h'))), if_neg h]
    simp

def mulIt (x : BitVec 64) : Nat → BitVec 64 → BitVec 64 → BitVec 64
  | 0, acc, _ => acc
  | n + 1, acc, yy => mulIt x n (acc + acc + ((0 - sltW yy 0) &&& x)) (yy + yy)

theorem mul_bit (Y j : Nat) (hj : j < 64) (hY : Y < 2 ^ 64) :
    (2 ^ 64 ≤ 2 * (Y * 2 ^ (63 - j) % 2 ^ 64)) ↔ Y / 2 ^ j % 2 = 1 := by
  have hcd : 2 ^ (63 - j) * 2 ^ j = 2 ^ 63 := by
    rw [← Nat.pow_add]; congr 1; omega
  have hY' := Nat.div_add_mod Y (2 ^ j)
  have hr := Nat.mod_lt Y (Nat.two_pow_pos j)
  generalize Y / 2 ^ j = q at hY'
  generalize Y % 2 ^ j = r at hY' hr
  have hs : 2 ^ (63 - j) * r < 2 ^ 63 := by
    rw [← hcd]; exact Nat.mul_lt_mul_of_pos_left hr (Nat.two_pow_pos _)
  have e : Y * 2 ^ (63 - j) = 2 ^ 63 * q + 2 ^ (63 - j) * r := by
    rw [← hY', Nat.add_mul, Nat.mul_comm (2 ^ j * q), ← Nat.mul_assoc, hcd, Nat.mul_comm r]
  rw [e]
  generalize 2 ^ (63 - j) * r = s at hs
  omega

theorem mulIt_inv (x y : BitVec 64) : ∀ j, j ≤ 64 →
    mulIt x j (x * (y >>> j)) (y <<< (64 - j)) = x * y := by
  intro j
  induction j with
  | zero => intro _; simp [mulIt]
  | succ j ih =>
    intro hj
    rw [mulIt]
    have hY := y.isLt
    have hsh : y <<< (64 - (j + 1)) + y <<< (64 - (j + 1)) = y <<< (64 - j) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
      have e2 : 2 ^ (64 - j) = 2 ^ (64 - (j + 1)) * 2 := by
        rw [← Nat.pow_succ]; congr 1; omega
      rw [e2, ← Nat.mul_assoc]
      generalize y.toNat * 2 ^ (64 - (j + 1)) = T
      omega
    have hacc : x * (y >>> (j + 1)) + x * (y >>> (j + 1)) +
        ((0 - sltW (y <<< (64 - (j + 1))) 0) &&& x) = x * (y >>> j) := by
      rw [mask_and]
      have hb := mul_bit y.toNat j (by omega) hY
      rw [show 63 - j = 64 - (j + 1) by omega] at hb
      simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq] at hb ⊢
      apply BitVec.eq_of_toNat_eq
      have hq : y.toNat / 2 ^ (j + 1) = y.toNat / 2 ^ j / 2 := by
        rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
      have hq2 := Nat.div_add_mod (y.toNat / 2 ^ j) 2
      split
      · rename_i hc
        have h1 := hb.mp hc
        simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
          hq]
        generalize y.toNat / 2 ^ j = q at hq2 h1
        have e : x.toNat * q = 2 * (x.toNat * (q / 2)) + x.toNat := by
          conv => lhs; rw [← hq2, h1]
          rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]
        rw [e]
        generalize x.toNat * (q / 2) = P
        omega
      · rename_i hc
        have h1 : y.toNat / 2 ^ j % 2 = 0 := by
          have := Nat.mod_two_eq_zero_or_one (y.toNat / 2 ^ j)
          rcases this with h | h
          · exact h
          · exact absurd (hb.mpr h) hc
        have hz : (0 : BitVec 64).toNat = 0 := rfl
        simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
          hq, hz, Nat.add_zero]
        generalize y.toNat / 2 ^ j = q at hq2 h1
        have e : x.toNat * q = 2 * (x.toNat * (q / 2)) := by
          conv => lhs; rw [← hq2, h1]
          rw [Nat.add_zero, Nat.mul_left_comm]
        rw [e]
        generalize x.toNat * (q / 2) = P
        omega
    rw [hacc, hsh]
    exact ih (by omega)

theorem mulIt_spec (x y : BitVec 64) : mulIt x 64 0 y = x * y := by
  have h := mulIt_inv x y 64 (by omega)
  have h0 : y >>> 64 = 0 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
    exact Nat.div_eq_of_lt y.isLt
  have hx0 : x * (0 : BitVec 64) = 0 := by simp
  rw [h0, hx0, show 64 - 64 = 0 from rfl, BitVec.shiftLeft_zero] at h
  exact h

section
variable {code : List Ins}

theorem reach_shape {A : AM} {pc : BitVec 64} {P : GRegs → Prop}
    (h : Reaches code A (fun B => B.pc = pc ∧ B.mem = A.mem ∧ B.out = A.out ∧ P B.regs)) :
    ∃ L, Star code A ⟨pc, L, A.mem, A.out⟩ ∧ P L := by
  obtain ⟨⟨pc', L, m, o⟩, s, h1, h2, h3, h4⟩ := h
  simp only at h1 h2 h3 h4
  subst h1 h2 h3
  exact ⟨L, s, h4⟩

theorem run_nez (hfit : Fits code) {p : Nat} {A : AM} {x : BitVec 64}
    (hseg : Seg code p nez) (hA : A.pc = pcOf p) (h0 : Has A.regs a0 x) :
    ∃ L, Star code A ⟨pcOf (p + 3), L, A.mem, A.out⟩ ∧ Has L a0 (nezW x) := by
  apply reach_shape
  refine ex_step (step_slt hfit (k := p) (rd := s3) (hseg 0 (by decide)) hA (by decide) h0 (Has.zero _)) ?_
  refine ex_step (step_slt hfit (k := p + 1) (rd := a0) (hseg 1 (by decide)) rfl (by decide) (Has.zero _)
    (h0.set_other (by decide))) ?_
  refine ex_step (step_add hfit (k := p + 2) (rd := a0) (hseg 2 (by decide)) rfl (by decide)
    (Has.set_self _ _ (by decide) (by decide))
    ((Has.set_self _ _ (by decide) (by decide)).set_other (by decide))) ?_
  refine ⟨_, Star.refl _ _, rfl, rfl, rfl, ?_⟩
  show Has (gset _ a0 (sltW 0 x + sltW x 0)) a0 (nezW x)
  rw [sltW_nez]
  exact Has.set_self _ _ (by decide) (by decide)

theorem run_flip (hfit : Fits code) {p : Nat} {A : AM} {c : Bool}
    (hseg : Seg code p flip) (hA : A.pc = pcOf p) (h0 : Has A.regs a0 (if c then 1 else 0)) :
    ∃ L, Star code A ⟨pcOf (p + 2), L, A.mem, A.out⟩ ∧ Has L a0 (if c then 0 else 1) := by
  apply reach_shape
  refine ex_step (step_sub hfit (k := p) (rd := a0) (hseg 0 (by decide)) hA (by decide) (Has.zero _) h0) ?_
  refine ex_step (step_addi hfit (k := p + 1) (rd := a0) (hseg 1 (by decide)) rfl (by decide)
    (Has.set_self _ _ (by decide) (by decide))) ?_
  refine ⟨_, Star.refl _ _, rfl, rfl, rfl, ?_⟩
  show Has (gset _ a0 ((0 : BitVec 64) - (if c then 1 else 0) + (sign_extend (1 : BitVec 12) : BitVec 64)))
    a0 (if c then 0 else 1)
  rw [flip_val]
  exact Has.set_self _ _ (by decide) (by decide)

theorem sext_m1 : (sign_extend (-1 : BitVec 12) : BitVec 64) = -1 := by decide

theorem ofNat_pred (n : Nat) (h1 : 1 ≤ n) (h2 : n ≤ 64) :
    BitVec.ofNat 64 n + (sign_extend (-1 : BitVec 12) : BitVec 64) = BitVec.ofNat 64 (n - 1) := by
  rw [sext_m1]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  apply BitVec.eq_of_toNat_eq
  have : (-1 : BitVec 64).toNat = 2 ^ 64 - 1 := by simp
  rw [BitVec.toNat_add, this]
  simp only [BitVec.toNat_ofNat, Nat.add_sub_cancel]
  omega

theorem ofNat_beq_zero (n : Nat) (h : n < 2 ^ 64) : (BitVec.ofNat 64 n == 0) = decide (n = 0) := by
  by_cases hn : n = 0
  · subst hn; decide
  · have : BitVec.ofNat 64 n ≠ 0 := by
      intro e
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_ofNat] at this
      have hz : (0 : BitVec 64).toNat = 0 := rfl
      omega
    rw [beq_eq_false_iff_ne.mpr this]; simp [hn]

theorem run_mulIter (hfit : Fits code) {p : Nat} (hseg : Seg code p ctMul) (hpos : PosOK (p + 11))
    (n : Nat) (A : AM) (acc yy x : BitVec 64) (h1 : 1 ≤ n) (h2 : n ≤ 64) (hA : A.pc = pcOf (p + 2))
    (ha0 : Has A.regs a0 x) (ha1 : Has A.regs a1 yy) (hs3 : Has A.regs s3 acc)
    (hs4 : Has A.regs s4 (BitVec.ofNat 64 n)) :
    ∃ L, Star code A ⟨if n - 1 = 0 then pcOf (p + 10) else pcOf (p + 2), L, A.mem, A.out⟩ ∧
      Has L a0 x ∧ Has L a1 (yy + yy) ∧ Has L s3 (acc + acc + ((0 - sltW yy 0) &&& x)) ∧
      Has L s4 (BitVec.ofNat 64 (n - 1)) := by
  apply reach_shape (P := fun L => Has L a0 x ∧ Has L a1 (yy + yy) ∧
    Has L s3 (acc + acc + ((0 - sltW yy 0) &&& x)) ∧ Has L s4 (BitVec.ofNat 64 (n - 1)))
  refine ex_step (step_add hfit (k := p + 2) (rd := s3) (hseg 2 (by decide)) hA (by decide) hs3 hs3) ?_
  refine ex_step (step_slt hfit (k := p + 3) (rd := s5) (hseg 3 (by decide)) rfl (by decide)
    (ha1.set_other (by decide)) (Has.zero _)) ?_
  refine ex_step (step_sub hfit (k := p + 4) (rd := s5) (hseg 4 (by decide)) rfl (by decide) (Has.zero _)
    (Has.set_self _ _ (by decide) (by decide))) ?_
  refine ex_step (step_and hfit (k := p + 5) (rd := s5) (hseg 5 (by decide)) rfl (by decide)
    (Has.set_self _ _ (by decide) (by decide))
    (((ha0.set_other (by decide)).set_other (by decide)).set_other (by decide))) ?_
  refine ex_step (step_add hfit (k := p + 6) (rd := s3) (hseg 6 (by decide)) rfl (by decide)
    ((((Has.set_self _ _ (by decide) (by decide)).set_other (by decide)).set_other
      (by decide)).set_other (by decide))
    (Has.set_self _ _ (by decide) (by decide))) ?_
  refine ex_step (step_add hfit (k := p + 7) (rd := a1) (hseg 7 (by decide)) rfl (by decide)
    (((((ha1.set_other (by decide)).set_other (by decide)).set_other (by decide)).set_other
      (by decide)).set_other (by decide))
    (((((ha1.set_other (by decide)).set_other (by decide)).set_other (by decide)).set_other
      (by decide)).set_other (by decide))) ?_
  refine ex_step (step_addi hfit (k := p + 8) (rd := s4) (hseg 8 (by decide)) rfl (by decide)
    ((((((hs4.set_other (by decide)).set_other (by decide)).set_other (by decide)).set_other
      (by decide)).set_other (by decide)).set_other (by decide))) ?_
  rw [ofNat_pred n h1 h2]
  refine ex_step (step_br_back hfit (op := .ne) (n := 7) (k := p + 9) (hseg 9 (by decide)) rfl
    (Has.set_self _ _ (by decide) (by decide)) (Has.zero _)
    (by unfold PosOK at *; omega) (by omega) (by decide)) ?_
  rw [guard_ne_zero, ofNat_beq_zero _ (by omega), show p + 9 - 7 = p + 2 by omega]
  refine ⟨_, Star.refl _ _, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · by_cases h : n - 1 = 0 <;> simp [h]
  · exact (((((((ha0.set_other (by decide)).set_other (by decide)).set_other (by decide)).set_other
      (by decide)).set_other (by decide)).set_other (by decide)).set_other (by decide))
  · exact (Has.set_self _ _ (by decide) (by decide)).set_other (by decide)
  · exact ((Has.set_self _ _ (by decide) (by decide)).set_other (by decide)).set_other (by decide)
  · exact Has.set_self _ _ (by decide) (by decide)

theorem run_mulLoop (hfit : Fits code) {p : Nat} (hseg : Seg code p ctMul) (hpos : PosOK (p + 11)) :
    ∀ (n : Nat) (A : AM) (acc yy x : BitVec 64), 1 ≤ n → n ≤ 64 → A.pc = pcOf (p + 2) →
      Has A.regs a0 x → Has A.regs a1 yy → Has A.regs s3 acc → Has A.regs s4 (BitVec.ofNat 64 n) →
      ∃ L, Star code A ⟨pcOf (p + 10), L, A.mem, A.out⟩ ∧ Has L s3 (mulIt x n acc yy) ∧
        Has L a0 x := by
  intro n
  induction n with
  | zero => intro _ _ _ _ h; omega
  | succ n ih =>
    intro A acc yy x h1 h2 hA ha0 ha1 hs3 hs4
    obtain ⟨L, r, h0', h1', h3', h4'⟩ := run_mulIter hfit hseg hpos (n + 1) A acc yy x h1 h2 hA ha0 ha1
      hs3 hs4
    simp only [Nat.add_sub_cancel] at r h4'
    by_cases hn : n = 0
    · subst hn
      simp only [ite_true] at r
      exact ⟨L, r, by simpa [mulIt] using h3', h0'⟩
    · rw [if_neg hn] at r
      obtain ⟨L', r', h3'', h0''⟩ := ih ⟨pcOf (p + 2), L, A.mem, A.out⟩ _ _ x (by omega) (by omega) rfl
        h0' h1' h3' h4'
      exact ⟨L', r.trans r', by rw [mulIt]; exact h3'', h0''⟩

theorem run_ctMul (hfit : Fits code) {p : Nat} {A : AM} {x y : BitVec 64}
    (hseg : Seg code p ctMul) (hA : A.pc = pcOf p) (hpos : PosOK (p + 11))
    (h0 : Has A.regs a0 x) (h1 : Has A.regs a1 y) :
    ∃ L, Star code A ⟨pcOf (p + 11), L, A.mem, A.out⟩ ∧ Has L a0 (x * y) := by
  have z0 : (0 : BitVec 64) + (sign_extend (0 : BitVec 12) : BitVec 64) = 0 := by decide
  have z64 : (0 : BitVec 64) + (sign_extend (64 : BitVec 12) : BitVec 64) = BitVec.ofNat 64 64 := by
    decide
  apply reach_shape
  refine ex_step (step_addi hfit (k := p) (rd := s3) (hseg 0 (by decide)) hA (by decide) (Has.zero _)) ?_
  refine ex_step (step_addi hfit (k := p + 1) (rd := s4) (hseg 1 (by decide)) rfl (by decide)
    (Has.zero _)) ?_
  rw [z0, z64]
  obtain ⟨L, r, h3, h0'⟩ := run_mulLoop hfit hseg hpos 64
    ⟨pcOf (p + 1 + 1), gset (gset A.regs s3 0) s4 (BitVec.ofNat 64 64), A.mem, A.out⟩ 0 y x
    (by decide) (by decide) rfl ((h0.set_other (by decide)).set_other (by decide))
    ((h1.set_other (by decide)).set_other (by decide))
    ((Has.set_self _ _ (by decide) (by decide)).set_other (by decide))
    (Has.set_self _ _ (by decide) (by decide))
  rw [mulIt_spec] at h3
  refine ex_trans r ?_
  refine ex_step (step_addi hfit (k := p + 10) (rd := a0) (hseg 10 (by decide)) rfl (by decide) h3) ?_
  rw [show x * y + (sign_extend (0 : BitVec 12) : BitVec 64) = x * y by
    rw [show (sign_extend (0 : BitVec 12) : BitVec 64) = 0 by decide]; simp]
  exact ⟨_, Star.refl _ _, rfl, rfl, rfl, Has.set_self (rd := a0) _ _ (by decide) (by decide)⟩

end

end Vsa.Compiler
