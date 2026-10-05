import Vsa.CT.TRun

namespace Vsa.Compiler

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa.Sim

section
variable {code : List Ins}

theorem reachT_shape {A : AM} {τ : List Obs} {pc : BitVec 64} {P : GRegs → Prop}
    (h : ReachesT code A τ (fun B => B.pc = pc ∧ B.mem = A.mem ∧ B.out = A.out ∧ P B.regs)) :
    ∃ L, StarT code τ A ⟨pc, L, A.mem, A.out⟩ ∧ P L := by
  obtain ⟨⟨pc', L, m, o⟩, s, h1, h2, h3, h4⟩ := h
  simp only at h1 h2 h3 h4
  subst h1 h2 h3
  exact ⟨L, s, h4⟩

theorem run_nezT (hfit : Fits code) {p : Nat} {A : AM} {x : BitVec 64}
    (hseg : Seg code p nez) (hA : A.pc = pcOf p) (h0 : Has A.regs a0 x) :
    ∃ L, StarT code (lin p 3) A ⟨pcOf (p + 3), L, A.mem, A.out⟩ ∧ Has L a0 (nezW x) := by
  apply reachT_shape
  refine exT_step hfit (hseg 0 (by decide)) trivial hA
    (step_slt hfit (k := p) (rd := s3) (hseg 0 (by decide)) hA (by decide) h0 (Has.zero _)) ?_
  refine exT_step hfit (hseg 1 (by decide)) trivial rfl
    (step_slt hfit (k := p + 1) (rd := a0) (hseg 1 (by decide)) rfl (by decide) (Has.zero _)
    (h0.set_other (by decide))) ?_
  refine exT_step hfit (hseg 2 (by decide)) trivial rfl
    (step_add hfit (k := p + 2) (rd := a0) (hseg 2 (by decide)) rfl (by decide)
    (Has.set_self _ _ (by decide) (by decide))
    ((Has.set_self _ _ (by decide) (by decide)).set_other (by decide))) ?_
  refine ⟨_, StarT.refl _, rfl, rfl, rfl, ?_⟩
  show Has (gset _ a0 (sltW 0 x + sltW x 0)) a0 (nezW x)
  rw [sltW_nez]
  exact Has.set_self _ _ (by decide) (by decide)

theorem run_flipT (hfit : Fits code) {p : Nat} {A : AM} {c : Bool}
    (hseg : Seg code p flip) (hA : A.pc = pcOf p) (h0 : Has A.regs a0 (if c then 1 else 0)) :
    ∃ L, StarT code (lin p 2) A ⟨pcOf (p + 2), L, A.mem, A.out⟩ ∧ Has L a0 (if c then 0 else 1) := by
  apply reachT_shape
  refine exT_step hfit (hseg 0 (by decide)) trivial hA
    (step_sub hfit (k := p) (rd := a0) (hseg 0 (by decide)) hA (by decide) (Has.zero _) h0) ?_
  refine exT_step hfit (hseg 1 (by decide)) trivial rfl
    (step_addi hfit (k := p + 1) (rd := a0) (hseg 1 (by decide)) rfl (by decide)
    (Has.set_self _ _ (by decide) (by decide))) ?_
  refine ⟨_, StarT.refl _, rfl, rfl, rfl, ?_⟩
  show Has (gset _ a0 ((0 : BitVec 64) - (if c then 1 else 0) + (sign_extend (1 : BitVec 12) : BitVec 64)))
    a0 (if c then 0 else 1)
  rw [flip_val]
  exact Has.set_self _ _ (by decide) (by decide)

def iterTr (p : Nat) : List Obs := lin (p + 2) 8

def loopTr (p : Nat) : Nat → List Obs
  | 0 => []
  | n + 1 => iterTr p ++ loopTr p n

def mulTr (p : Nat) : List Obs := lin p 2 ++ loopTr p 64 ++ [pobs (p + 10)]

theorem run_mulIterT (hfit : Fits code) {p : Nat} (hseg : Seg code p ctMul) (hpos : PosOK (p + 11))
    (n : Nat) (A : AM) (acc yy x : BitVec 64) (h1 : 1 ≤ n) (h2 : n ≤ 64) (hA : A.pc = pcOf (p + 2))
    (ha0 : Has A.regs a0 x) (ha1 : Has A.regs a1 yy) (hs3 : Has A.regs s3 acc)
    (hs4 : Has A.regs s4 (BitVec.ofNat 64 n)) :
    ∃ L, StarT code (iterTr p) A ⟨if n - 1 = 0 then pcOf (p + 10) else pcOf (p + 2), L, A.mem, A.out⟩ ∧
      Has L a0 x ∧ Has L a1 (yy + yy) ∧ Has L s3 (acc + acc + ((0 - sltW yy 0) &&& x)) ∧
      Has L s4 (BitVec.ofNat 64 (n - 1)) := by
  apply reachT_shape (P := fun L => Has L a0 x ∧ Has L a1 (yy + yy) ∧
    Has L s3 (acc + acc + ((0 - sltW yy 0) &&& x)) ∧ Has L s4 (BitVec.ofNat 64 (n - 1)))
  have ht : iterTr p = [pobs (p + 2), pobs (p + 3), pobs (p + 4), pobs (p + 5), pobs (p + 6),
      pobs (p + 7), pobs (p + 8), pobs (p + 9)] := by
    simp [iterTr, lin, Nat.add_assoc]
  rw [ht]
  refine exT_step hfit (hseg 2 (by decide)) trivial hA
    (step_add hfit (k := p + 2) (rd := s3) (hseg 2 (by decide)) hA (by decide) hs3 hs3) ?_
  refine exT_step hfit (hseg 3 (by decide)) trivial rfl
    (step_slt hfit (k := p + 3) (rd := s5) (hseg 3 (by decide)) rfl (by decide)
    (ha1.set_other (by decide)) (Has.zero _)) ?_
  refine exT_step hfit (hseg 4 (by decide)) trivial rfl
    (step_sub hfit (k := p + 4) (rd := s5) (hseg 4 (by decide)) rfl (by decide) (Has.zero _)
    (Has.set_self _ _ (by decide) (by decide))) ?_
  refine exT_step hfit (hseg 5 (by decide)) trivial rfl
    (step_and hfit (k := p + 5) (rd := s5) (hseg 5 (by decide)) rfl (by decide)
    (Has.set_self _ _ (by decide) (by decide))
    (((ha0.set_other (by decide)).set_other (by decide)).set_other (by decide))) ?_
  refine exT_step hfit (hseg 6 (by decide)) trivial rfl
    (step_add hfit (k := p + 6) (rd := s3) (hseg 6 (by decide)) rfl (by decide)
    ((((Has.set_self _ _ (by decide) (by decide)).set_other (by decide)).set_other
      (by decide)).set_other (by decide))
    (Has.set_self _ _ (by decide) (by decide))) ?_
  refine exT_step hfit (hseg 7 (by decide)) trivial rfl
    (step_add hfit (k := p + 7) (rd := a1) (hseg 7 (by decide)) rfl (by decide)
    (((((ha1.set_other (by decide)).set_other (by decide)).set_other (by decide)).set_other
      (by decide)).set_other (by decide))
    (((((ha1.set_other (by decide)).set_other (by decide)).set_other (by decide)).set_other
      (by decide)).set_other (by decide))) ?_
  refine exT_step hfit (hseg 8 (by decide)) trivial rfl
    (step_addi hfit (k := p + 8) (rd := s4) (hseg 8 (by decide)) rfl (by decide)
    ((((((hs4.set_other (by decide)).set_other (by decide)).set_other (by decide)).set_other
      (by decide)).set_other (by decide)).set_other (by decide))) ?_
  rw [ofNat_pred n h1 h2]
  refine exT_step hfit (hseg 9 (by decide)) trivial rfl
    (step_br_back hfit (op := .ne) (n := 7) (k := p + 9) (hseg 9 (by decide)) rfl
    (Has.set_self _ _ (by decide) (by decide)) (Has.zero _)
    (by unfold PosOK at *; omega) (by omega) (by decide)) ?_
  rw [guard_ne_zero, ofNat_beq_zero _ (by omega), show p + 9 - 7 = p + 2 by omega]
  refine ⟨_, StarT.refl _, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · by_cases h : n - 1 = 0 <;> simp [h]
  · exact (((((((ha0.set_other (by decide)).set_other (by decide)).set_other (by decide)).set_other
      (by decide)).set_other (by decide)).set_other (by decide)).set_other (by decide))
  · exact (Has.set_self _ _ (by decide) (by decide)).set_other (by decide)
  · exact ((Has.set_self _ _ (by decide) (by decide)).set_other (by decide)).set_other (by decide)
  · exact Has.set_self _ _ (by decide) (by decide)

theorem run_mulLoopT (hfit : Fits code) {p : Nat} (hseg : Seg code p ctMul) (hpos : PosOK (p + 11)) :
    ∀ (n : Nat) (A : AM) (acc yy x : BitVec 64), 1 ≤ n → n ≤ 64 → A.pc = pcOf (p + 2) →
      Has A.regs a0 x → Has A.regs a1 yy → Has A.regs s3 acc → Has A.regs s4 (BitVec.ofNat 64 n) →
      ∃ L, StarT code (loopTr p n) A ⟨pcOf (p + 10), L, A.mem, A.out⟩ ∧ Has L s3 (mulIt x n acc yy) ∧
        Has L a0 x := by
  intro n
  induction n with
  | zero => intro _ _ _ _ h; omega
  | succ n ih =>
    intro A acc yy x h1 h2 hA ha0 ha1 hs3 hs4
    obtain ⟨L, r, h0', h1', h3', h4'⟩ := run_mulIterT hfit hseg hpos (n + 1) A acc yy x h1 h2 hA ha0 ha1
      hs3 hs4
    simp only [Nat.add_sub_cancel] at r h4'
    by_cases hn : n = 0
    · subst hn
      simp only [ite_true] at r
      refine ⟨L, by simpa [loopTr] using r, by simpa [mulIt] using h3', h0'⟩
    · rw [if_neg hn] at r
      obtain ⟨L', r', h3'', h0''⟩ := ih ⟨pcOf (p + 2), L, A.mem, A.out⟩ _ _ x (by omega) (by omega) rfl
        h0' h1' h3' h4'
      exact ⟨L', r.trans r', by rw [mulIt]; exact h3'', h0''⟩

theorem run_ctMulT (hfit : Fits code) {p : Nat} {A : AM} {x y : BitVec 64}
    (hseg : Seg code p ctMul) (hA : A.pc = pcOf p) (hpos : PosOK (p + 11))
    (h0 : Has A.regs a0 x) (h1 : Has A.regs a1 y) :
    ∃ L, StarT code (mulTr p) A ⟨pcOf (p + 11), L, A.mem, A.out⟩ ∧ Has L a0 (x * y) := by
  have z0 : (0 : BitVec 64) + (sign_extend (0 : BitVec 12) : BitVec 64) = 0 := by decide
  have z64 : (0 : BitVec 64) + (sign_extend (64 : BitVec 12) : BitVec 64) = BitVec.ofNat 64 64 := by
    decide
  apply reachT_shape
  have hm : mulTr p = [pobs p, pobs (p + 1)] ++ (loopTr p 64 ++ [pobs (p + 10)]) := by
    simp [mulTr, lin]
  rw [hm]
  refine exT_step hfit (hseg 0 (by decide)) trivial hA
    (step_addi hfit (k := p) (rd := s3) (hseg 0 (by decide)) hA (by decide) (Has.zero _)) ?_
  refine exT_step hfit (hseg 1 (by decide)) trivial rfl
    (step_addi hfit (k := p + 1) (rd := s4) (hseg 1 (by decide)) rfl (by decide)
    (Has.zero _)) ?_
  rw [z0, z64]
  obtain ⟨L, r, h3, h0'⟩ := run_mulLoopT hfit hseg hpos 64
    ⟨pcOf (p + 1 + 1), gset (gset A.regs s3 0) s4 (BitVec.ofNat 64 64), A.mem, A.out⟩ 0 y x
    (by decide) (by decide) rfl ((h0.set_other (by decide)).set_other (by decide))
    ((h1.set_other (by decide)).set_other (by decide))
    ((Has.set_self _ _ (by decide) (by decide)).set_other (by decide))
    (Has.set_self _ _ (by decide) (by decide))
  rw [mulIt_spec] at h3
  show ReachesT code _ (loopTr p 64 ++ [pobs (p + 10)]) _
  refine exT_trans r ?_
  refine exT_step hfit (hseg 10 (by decide)) trivial rfl
    (step_addi hfit (k := p + 10) (rd := a0) (hseg 10 (by decide)) rfl (by decide) h3) ?_
  rw [show x * y + (sign_extend (0 : BitVec 12) : BitVec 64) = x * y by
    rw [show (sign_extend (0 : BitVec 12) : BitVec 64) = 0 by decide]; simp]
  exact ⟨_, StarT.refl _, rfl, rfl, rfl, Has.set_self (rd := a0) _ _ (by decide) (by decide)⟩

end

end Vsa.Compiler
