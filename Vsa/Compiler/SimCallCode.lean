import Vsa.Compiler.SimNative

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

def ccAssert (k m pos : Nat) : List Ins :=
  if m = 1 ∨ m = 2 then
    loadTmp (k + 1) ++ [Call (pos + 15 + 4) trPos] ++ jmpIfZero (pos + 15 + 5) errPos ++ [mvi a0 0, mvi a1 0]
  else [J (pos + 15) errPos]

def ccPR (k m pos : Nat) : Nat := pos + 15 + (ccAssert k m pos).length + 1
def ccPrC (k m pos : Nat) : List Ins := printLoopG (ccPR k m pos) (k + 1) m ++ [mvi a0 0, mvi a1 0]
def ccPL (k m pos : Nat) : Nat := ccPR k m pos + (ccPrC k m pos).length + 1
def ccPlC (k m pos : Nat) : List Ins := printLoopG (ccPL k m pos) (k + 1) m ++ putc '\n' ++ [mvi a0 0, mvi a1 0]
def ccCL (k m pos : Nat) : Nat := ccPL k m pos + (ccPlC k m pos).length + 1
def ccFin (k m pos : Nat) : Nat := ccCL k m pos + 8

def ccHead (k m pos : Nat) : List Ins :=
  [addiN t6 spR (16 + 16 * k), .ld t0 t6, addi t6 t6 8, .ld t1 t6,
   mvi t2 4, Br .ne t0 t2 (pos + 5) (pos + 7), J (pos + 6) (ccCL k m pos),
   mvi t2 5] ++ errUnlessEq t0 t2 (pos + 8) ++
  [Br .ne t1 0 (pos + 10) (pos + 12), J (pos + 11) (ccPR k m pos),
   mvi t2 1, Br .ne t1 t2 (pos + 13) (pos + 15), J (pos + 14) (ccPL k m pos)]

def ccClo (k m pos : Nat) : List Ins :=
  [mv a2 t1, addiN a3 spR (16 + 16 * (k + 1)), mvi a4 m, addi t3 a2 8, .ld t3 t3,
   Call (ccCL k m pos + 5) (ccCL k m pos + 7), J (ccCL k m pos + 6) (ccFin k m pos), .jalr t3]

theorem callCode_eq (k m pos : Nat) : callCode k m pos =
    ccHead k m pos ++ ccAssert k m pos ++ [J (ccPR k m pos - 1) (ccFin k m pos)] ++ ccPrC k m pos ++
      [J (ccPL k m pos - 1) (ccFin k m pos)] ++ ccPlC k m pos ++ [J (ccCL k m pos - 1) (ccFin k m pos)] ++
      ccClo k m pos := rfl

theorem ccHead_length (k m pos : Nat) : (ccHead k m pos).length = 15 := rfl

theorem ccPR_eq (k m pos : Nat) : ccPR k m pos = pos + 15 + (ccAssert k m pos).length + 1 := rfl
theorem ccPL_eq (k m pos : Nat) : ccPL k m pos = ccPR k m pos + (ccPrC k m pos).length + 1 := rfl
theorem ccCL_eq (k m pos : Nat) : ccCL k m pos = ccPL k m pos + (ccPlC k m pos).length + 1 := rfl

theorem callCode_length (k m pos : Nat) : (callCode k m pos).length = ccFin k m pos - pos := by
  simp only [callCode_eq, List.length_append, ccHead_length, List.length_singleton, ccFin, ccCL_eq, ccPL_eq,
    ccPR_eq, ccClo, List.length_cons, List.length_nil]
  omega

structure CCSegs (code : List Ins) (k m pos : Nat) : Prop where
  head : Seg code pos (ccHead k m pos)
  asrt : Seg code (pos + 15) (ccAssert k m pos)
  asrtJ : Seg code (ccPR k m pos - 1) [J (ccPR k m pos - 1) (ccFin k m pos)]
  pr : Seg code (ccPR k m pos) (ccPrC k m pos)
  prJ : Seg code (ccPL k m pos - 1) [J (ccPL k m pos - 1) (ccFin k m pos)]
  pl : Seg code (ccPL k m pos) (ccPlC k m pos)
  plJ : Seg code (ccCL k m pos - 1) [J (ccCL k m pos - 1) (ccFin k m pos)]
  clo : Seg code (ccCL k m pos) (ccClo k m pos)

theorem CCSegs.of {code : List Ins} {k m pos : Nat} (h : Seg code pos (callCode k m pos)) : CCSegs code k m pos := by
  rw [callCode_eq] at h
  obtain ⟨h, h8⟩ := h.append
  obtain ⟨h, h7⟩ := h.append
  obtain ⟨h, h6⟩ := h.append
  obtain ⟨h, h5⟩ := h.append
  obtain ⟨h, h4⟩ := h.append
  obtain ⟨h, h3⟩ := h.append
  obtain ⟨h1, h2⟩ := h.append
  simp only [List.length_append, ccHead_length, List.length_singleton] at h2 h3 h4 h5 h6 h7 h8
  refine ⟨h1, h2, h3.cast ?_, h4.cast ?_, h5.cast ?_, h6.cast ?_, h7.cast ?_, h8.cast ?_⟩ <;>
    simp only [ccCL_eq, ccPL_eq, ccPR_eq] <;> omega

def dispTgt (k m pos : Nat) (t p : BitVec 64) : Nat :=
  if t = 4 then ccCL k m pos
  else if t = 5 then (if p = 0 then ccPR k m pos else if p = 1 then ccPL k m pos else pos + 15)
  else errPos

section
variable {code : List Ins} (hR : RTLoaded code)
include hR

theorem run_dispatch {k m pos sp d fs : Nat} (hs : CCSegs code k m pos)
    (hP : PosOK (pos + (callCode k m pos).length)) {L : GRegs} {mm : Mem} {o : Array String}
    (hsp : Has L spR (BitVec.ofNat 64 sp)) (hst : StackOK d sp fs) (hk : 16 + 16 * (k + 1) ≤ fs) :
    Reaches code ⟨pcOf pos, L, mm, o⟩ (fun B => B.mem = mm ∧ B.out = o ∧ Keep [t0, t1, t2, t6] L B.regs ∧
      Has B.regs t1 (rdW mm (sp + 16 + 16 * k + 8)) ∧
      B.pc = pcOf (dispTgt k m pos (rdW mm (sp + 16 + 16 * k)) (rdW mm (sp + 16 + 16 * k + 8)))) := by
  have hl := callCode_length k m pos
  have hfin : ccCL k m pos + 8 ≤ pos + (callCode k m pos).length := by
    rw [hl]; simp only [ccFin]; have : pos ≤ ccCL k m pos := by simp only [ccCL_eq, ccPL_eq, ccPR_eq]; omega
    omega
  have hcl : PosOK (ccCL k m pos) := posOK_le hP (by omega)
  have hpl : PosOK (ccPL k m pos) := posOK_le hP (by simp only [ccCL_eq] at hfin; omega)
  have hpr : PosOK (ccPR k m pos) := posOK_le hP (by simp only [ccCL_eq, ccPL_eq] at hfin; omega)
  have hpp : PosOK (pos + 15) := posOK_le hP (by simp only [ccCL_eq, ccPL_eq, ccPR_eq] at hfin; omega)
  have hb := hst.bounds
  have hfs := hst.fsz
  have hL : stackLo = 0xE0000000 := rfl
  have hH : stackHi = 0x100000000 := rfl
  have ht : tohostAddr = 0x8001ad00 := rfl
  have hM : maxFS = 2048 := rfl
  have k2 := has_mem hsp (by decide); have e2 := srcVal_of_has hsp
  simp only [spR] at k2 e2
  have hn1 : (BitVec.ofNat 64 (sp + 16 + 16 * k)).toNat = sp + 16 + 16 * k := toNat_ofNat_lt (by omega)
  have hn2 : (BitVec.ofNat 64 (sp + 16 + 16 * k + 8)).toNat = sp + 16 + 16 * k + 8 :=
    toNat_ofNat_lt (by omega)
  have e1 : sp + (16 + 16 * k) = sp + 16 + 16 * k := by omega
  generalize ht0 : rdW mm (sp + 16 + 16 * k) = tw
  generalize ht1 : rdW mm (sp + 16 + 16 * k + 8) = pw
  have hseg := hs.head
  simp only [ccHead, errUnlessEq, List.cons_append, List.nil_append] at hseg
  apply run_jumps hR.fits hseg
  wp_simp [k2, e2, hn1, hn2, e1, ht0, ht1]
  refine ⟨by unfold LdOK; omega, by unfold LdOK; omega, ?_⟩
  have g6 : ∀ L', Keep [5, 6, 7, 31] (gset (gset (gset (gset (gset L 31 (BitVec.ofNat 64 (sp + 16 + 16 * k))) 5 tw)
      31 (BitVec.ofNat 64 (sp + 16 + 16 * k + 8))) 6 pw) 7 4#64) L' → Keep [5, 6, 7, 31] L L' := fun L' h =>
    Keep.trans (by reg_simp []; exact Keep.refl _ _) h
  split
  · next h4 =>
    have h4' : tw ≠ 4 := by simpa using h4
    apply run_jumps hR.fits (hseg.drop 7)
    wp_simp []
    split
    · next h5 =>
      have h5' : tw = 5 := by simpa using h5
      apply run_jumps hR.fits ((hseg.drop 10).cast (by rfl))
      wp_simp []
      split
      · next h0 =>
        have h0' : pw ≠ 0 := by simpa using h0
        apply run_jumps hR.fits ((hseg.drop 12).cast (by rfl))
        wp_simp []
        split
        · next h1 =>
          have h1' : pw ≠ 1 := by simpa using h1
          refine reach_here ⟨rfl, rfl, by reg_simp []; exact Keep.refl _ _, by reg_simp [], ?_⟩
          simp only [dispTgt]; simp_all
        · next h1 =>
          have h1' : pw = 1 := by simpa using h1
          refine reach_here ⟨rfl, rfl, by reg_simp []; exact Keep.refl _ _, by reg_simp [], ?_⟩
          simp only [dispTgt]; simp_all
      · next h0 =>
        have h0' : pw = 0 := by simpa using h0
        refine reach_here ⟨rfl, rfl, by reg_simp []; exact Keep.refl _ _, by reg_simp [], ?_⟩
        simp only [dispTgt]; simp_all
    · next h5 =>
      have h5' : tw ≠ 5 := by simpa using h5
      refine reach_here ⟨rfl, rfl, by reg_simp []; exact Keep.refl _ _, by reg_simp [], ?_⟩
      simp only [dispTgt]; simp_all
  · next h4 =>
    have h4' : tw = 4 := by simpa using h4
    refine reach_here ⟨rfl, rfl, g6 _ (Keep.refl _ _), by reg_simp [], ?_⟩
    simp only [dispTgt]; simp_all

end

end Vsa.Compiler
