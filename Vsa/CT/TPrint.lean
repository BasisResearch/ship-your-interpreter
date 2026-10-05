import Vsa.CT.TRun
import Vsa.Compiler.PrintInt

namespace Vsa.Compiler

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa.Sim Vsa.While

section
variable {code : List Ins}

theorem exT_mem (hfit : Fits code) {k : Nat} {i : Ins} (hk : code[k]? = some i) {A S : AM}
    {τ : List Obs} {Q : AM → Prop} {a : Nat} (hA : A.pc = pcOf k) (hobs : insObs i A = mobs k a)
    (e : astep code A = some (.run S)) (h : ReachesT code S τ Q) : ReachesT code A (mobs k a :: τ) Q := by
  obtain ⟨B, hs, hq⟩ := h
  refine ⟨B, ?_, hq⟩
  have := stepM hfit hk hA e hs
  rwa [hobs] at this

theorem doneT {A : AM} {Q : AM → Prop} (h : Q A) : ReachesT code A [] Q := ⟨A, .refl A, h⟩

end

def absTr (v : BitVec 64) : List Obs := if v.toInt ≥ 0 then [pobs 57] else [pobs 57, pobs 58]

section
variable {code : List Ins} (hfit : Fits code) (hseg : Seg code 14 printCode)
include hfit hseg

theorem run_absT {A : AM} {v : BitVec 64} (hA : A.pc = pcOf 57) (h10 : Has A.regs a0 v)
    (hv : -10 < v.toInt ∧ v.toInt < 10) :
    ReachesT code A (absTr v) fun B => B.pc = pcOf 59 ∧ B.mem = A.mem ∧ B.out = A.out ∧
      Has B.regs a0 (BitVec.ofNat 64 v.toInt.natAbs) ∧
      ∀ n w, n ≠ a0 → Has A.regs n w → Has B.regs n w := by
  have P := fun k (hk : k ≤ 100) => print_posOK hfit hseg hk
  have hk := pI hseg (j := 43) (k := 57) (i := .br .ge a0 0 (bSkip 1)) rfl rfl
  have e := step_br hfit hk hA h10 (Has.zero _)
    (by rw [pcOf_skip _ _ (P _ (by decide)) (by decide), pcOf_toNat (by decide)]; decide)
  rw [pcOf_skip _ _ (P _ (by decide)) (by decide), zopz_ge] at e
  by_cases hs : v.toInt ≥ 0
  · rw [if_pos (by simpa using hs)] at e
    rw [absTr, if_pos hs]
    refine exT_step hfit hk trivial hA e (doneT ⟨rfl, rfl, rfl, ?_, fun n w _ h => h⟩)
    have : v = BitVec.ofNat 64 v.toInt.natAbs := by
      rw [← BitVec.ofInt_natCast, Int.natAbs_of_nonneg hs, BitVec.ofInt_toInt]
    rw [← this]; exact h10
  · rw [if_neg (by simpa using hs)] at e
    rw [absTr, if_neg hs]
    refine exT_step hfit hk trivial hA e ?_
    have hk2 := pI hseg (j := 44) (k := 57 + 1) (i := .sub a0 0 a0) rfl rfl
    have e2 := step_sub hfit hk2 rfl (A := ⟨_, A.regs, A.mem, A.out⟩)
      (by decide) (Has.zero _) h10
    refine exT_step hfit hk2 trivial rfl e2 (doneT ⟨rfl, rfl, rfl, ?_, fun n w hn h => h.gs hn⟩)
    have : 0 - v = BitVec.ofNat 64 v.toInt.natAbs := by
      rw [← BitVec.ofInt_natCast, Int.ofNat_natAbs_of_nonpos (by omega)]
      rw [BitVec.ofInt_neg, BitVec.ofInt_toInt]; simp
    rw [← this]; exact Has.gs_self _ _ _ (by decide)

end

def digitTr (j : Nat) (x : BitVec 64) : List Obs :=
  pobs 52 :: pobs 53 :: (libcTr 54 x 10 ++ (absTr (BitVec.ofInt 64 (x.toInt.tmod 10)) ++
    (pobs 59 :: mobs 60 (bufBase + 8 * j) :: pobs 61 :: pobs 62 :: pobs 63 :: pobs 64 ::
      (libcTr 65 x 10 ++ [pobs 68, pobs 69]))))

section
variable {code : List Ins} (hfit : Fits code) (hseg : Seg code 14 printCode)
include hfit hseg

theorem run_digitT {A : AM} {x r : BitVec 64} {j : Nat}
    (hA : A.pc = pcOf 52) (h4 : Has A.regs s4 x) (h5 : Has A.regs s5 (BitVec.ofNat 64 j))
    (h6 : Has A.regs s6 (BitVec.ofNat 64 (bufBase + 8 * j))) (h11 : Has A.regs s11 r)
    (hj : j < 20) :
    ReachesT code A (digitTr j x) fun B =>
      B.pc = (if BitVec.ofInt 64 (x.toInt.tdiv 10) = 0 then pcOf 70 else pcOf 52) ∧
      Has B.regs s4 (BitVec.ofInt 64 (x.toInt.tdiv 10)) ∧
      Has B.regs s5 (BitVec.ofNat 64 (j + 1)) ∧
      Has B.regs s6 (BitVec.ofNat 64 (bufBase + 8 * (j + 1))) ∧ Has B.regs s11 r ∧
      B.mem = applyW A.mem (bufBase + 8 * j, 8, BitVec.ofNat 64 (x.toInt.natAbs % 10 + 48)) ∧
      B.out = A.out := by
  have P := fun k (hk : k ≤ 100) => print_posOK hfit hseg hk
  have hb : bufBase = 0x80080000 := rfl
  have ht : tohostAddr = 0x8001ad00 := rfl
  have k52 := pI hseg (j := 38) (k := 52) (i := mv a0 s4) rfl rfl
  refine exT_step hfit k52 trivial hA (step_addi_eq hfit k52 hA (by decide) h4 (add_sext_zero x)) ?_
  have k53 := pI hseg (j := 39) (k := 52 + 1) (i := .addi a1 0 10) rfl rfl
  refine exT_step hfit k53 trivial rfl (step_addi_eq hfit k53 rfl (by decide)
    (Has.zero _) (w := 10) (by decide)) ?_
  refine exT_trans (run_libcT hfit (pS hseg (j := 40) (len := 3) (k := 52 + 1 + 1) rfl rfl) rfl
    (P _ (by decide)) (.inr (.inr rfl)) (by has_tac) (by has_tac) (libRes_mod x)) ?_
  obtain ⟨B1, s1, hpc1, hm1, ho1, h10', hpres⟩ := run_absT hfit hseg
    (A := ⟨pcOf (52 + 1 + 1 + 3), _, _, _⟩) rfl (Has.lib_self _ _)
    (by rw [abs_digit x.toInt]; have := Int.natAbs_tmod x.toInt 10
        have h2 : (x.toInt.tmod 10).natAbs < 10 := by rw [this]; simp; omega
        rcases Int.natAbs_eq (x.toInt.tmod 10) with h | h <;> omega)
  refine exT_trans s1 ?_
  simp only at hm1 ho1
  have hd : (BitVec.ofInt 64 (x.toInt.tmod 10)).toInt.natAbs = x.toInt.natAbs % 10 := by
    rw [abs_digit x.toInt, Int.natAbs_tmod]; rfl
  rw [hd] at h10'
  have g4 := hpres s4 x (by decide) (by has_tac)
  have g5 := hpres s5 _ (by decide) (by has_tac)
  have g6 := hpres s6 _ (by decide) (by has_tac)
  have g11 := hpres s11 r (by decide) (by has_tac)
  have hdl : x.toInt.natAbs % 10 < 10 := Nat.mod_lt _ (by decide)
  have k59 := pI hseg (j := 45) (k := 59) (i := .addi a0 a0 48) rfl rfl
  refine exT_step hfit k59 trivial hpc1 (step_addi_eq hfit k59 hpc1 (by decide) h10'
    (ofNat_add_sext _ 48 (by decide) (by omega))) ?_
  have k60 := pI hseg (j := 46) (k := 59 + 1) (i := .sd a0 s6) rfl rfl
  have h6' : Has (gset B1.regs a0 (BitVec.ofNat 64 (x.toInt.natAbs % 10 + 48))) s6
      (BitVec.ofNat 64 (bufBase + 8 * j)) := by has_tac
  refine exT_mem hfit k60 rfl (by simp [insObs, mobs, h6'.src.2]; omega)
    (step_sd hfit k60 rfl (a := BitVec.ofNat 64 (bufBase + 8 * j)) h6' (by has_tac)
      (by rw [BitVec.toNat_ofNat]; unfold StOK; omega)) ?_
  have k61 := pI hseg (j := 47) (k := 59 + 1 + 1) (i := .addi s6 s6 8) rfl rfl
  refine exT_step hfit k61 trivial rfl (step_addi_eq hfit k61 rfl (by decide)
    (by has_tac) (ofNat_add_sext _ 8 (by decide) (by omega))) ?_
  have k62 := pI hseg (j := 48) (k := 59 + 1 + 1 + 1) (i := .addi s5 s5 1) rfl rfl
  refine exT_step hfit k62 trivial rfl (step_addi_eq hfit k62 rfl (by decide)
    (by has_tac) (ofNat_add_sext _ 1 (by decide) (by omega))) ?_
  have k63 := pI hseg (j := 49) (k := 59 + 1 + 1 + 1 + 1) (i := mv a0 s4) rfl rfl
  refine exT_step hfit k63 trivial rfl (step_addi_eq hfit k63 rfl
    (by decide) (by has_tac) (add_sext_zero x)) ?_
  have k64 := pI hseg (j := 50) (k := 59 + 1 + 1 + 1 + 1 + 1) (i := .addi a1 0 10) rfl rfl
  refine exT_step hfit k64 trivial rfl (step_addi_eq hfit k64 rfl
    (by decide) (Has.zero _) (w := 10) (by decide)) ?_
  refine exT_trans (run_libcT hfit (pS hseg (j := 51) (len := 3) (k := 59 + 1 + 1 + 1 + 1 + 1 + 1)
    rfl rfl) rfl (P _ (by decide)) (.inr (.inl rfl)) (by has_tac) (by has_tac) (libRes_div x)) ?_
  have k68 := pI hseg (j := 54) (k := 59 + 1 + 1 + 1 + 1 + 1 + 1 + 3) (i := mv s4 a0) rfl rfl
  refine exT_step hfit k68 trivial rfl (step_addi_eq hfit k68
    rfl (by decide) (Has.lib_self _ _) (add_sext_zero _)) ?_
  have k69 := pI hseg (j := 55) (k := 69)
    (i := .br .ne s4 0 (BitVec.ofInt 13 (-4 * ((17 : Nat) : Int)))) rfl rfl
  refine exT_step hfit k69 trivial rfl (step_br_back hfit k69 rfl
    (Has.gs_self _ s4 (BitVec.ofInt 64 (x.toInt.tdiv 10)) (by decide)) (Has.zero _)
    (P _ (by decide)) (by decide) (by decide)) ?_
  rw [guard_ne_zero]
  refine doneT ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases h0 : BitVec.ofInt 64 (x.toInt.tdiv 10) = 0
    · simp [h0]
    · simp [h0]
  · has_tac
  · has_tac
  · rw [show bufBase + 8 * (j + 1) = bufBase + 8 * j + 8 by omega]; has_tac
  · has_tac
  · simp only [hm1, BitVec.toNat_ofNat]
    congr 2
    omega
  · simp only [ho1]

end

theorem run_digitsT : ∀ (N : Nat) (x : BitVec 64) (j : Nat) (ds : List Nat),
    x.toInt.natAbs = N → ds.length = j → (ds ++ digitsLE N).length ≤ 19 →
    ∃ τ : List Obs, ∀ {code : List Ins} {A : AM} {r : BitVec 64}, Fits code → Seg code 14 printCode →
    A.pc = pcOf 52 → Has A.regs s4 x → Has A.regs s5 (BitVec.ofNat 64 j) →
    Has A.regs s6 (BitVec.ofNat 64 (bufBase + 8 * j)) → Has A.regs s11 r →
    ReachesT code A τ fun B => B.pc = pcOf 70 ∧
      Has B.regs s5 (BitVec.ofNat 64 (ds ++ digitsLE N).length) ∧
      Has B.regs s6 (BitVec.ofNat 64 (bufBase + 8 * (ds ++ digitsLE N).length)) ∧
      Has B.regs s11 r ∧ B.out = A.out ∧
      (∀ q, j ≤ q → q < (ds ++ digitsLE N).length →
        rdW B.mem (bufBase + 8 * q) = BitVec.ofNat 64 ((ds ++ digitsLE N)[q]! + 48)) ∧
      (∀ a, (a + 8 ≤ bufBase + 8 * j ∨ bufBase + 8 * 20 ≤ a) → rdW B.mem a = rdW A.mem a) := by
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
  intro x j ds hN hj hlen
  have hb : bufBase = 0x80080000 := rfl
  have hjl : j + (digitsLE N).length ≤ 19 := by simpa [hj] using hlen
  have hpos : 1 ≤ (digitsLE N).length := by
    unfold digitsLE; split <;> simp
  by_cases hsmall : N < 10
  · refine ⟨digitTr j x, fun {code A r} hfit hseg hA h4 h5 h6 h11 => ?_⟩
    obtain ⟨B1, s1, hpc1, h4', h5', h6', h11', hm1, ho1⟩ :=
      run_digitT hfit hseg hA h4 h5 h6 h11 (by omega)
    have hw := rdW_write A.mem (bufBase + 8 * j) (BitVec.ofNat 64 (N % 10 + 48))
    rw [if_pos ((tdiv_word_zero x).mpr (by omega))] at hpc1
    have hdl : digitsLE N = [N] := digitsLE_small hsmall
    rw [hdl] at hlen ⊢
    refine ⟨B1, s1, hpc1, ?_, ?_, h11', ho1, ?_, ?_⟩
    · simpa [hj] using h5'
    · simpa [hj] using h6'
    · intro q hq1 hq2
      simp [hj] at hq2
      have : q = j := by omega
      subst this
      rw [hm1, hN]
      simp [hj, Nat.mod_eq_of_lt hsmall] at hw ⊢
      rw [hw]
    · intro a ha
      rw [hm1]
      exact rdW_write_other _ _ _ _ (by omega)
  · have hdl : digitsLE N = N % 10 :: digitsLE (N / 10) := digitsLE_big hsmall
    obtain ⟨hx1, hx'⟩ := tdiv_word x
    obtain ⟨τ', hτ'⟩ := ih (N / 10) (by omega) (BitVec.ofInt 64 (x.toInt.tdiv 10)) (j + 1)
      (ds ++ [N % 10]) (by rw [hx1, hx', hN]) (by simp [hj]) (by rw [hdl] at hlen; simpa using hlen)
    refine ⟨digitTr j x ++ τ', fun {code A r} hfit hseg hA h4 h5 h6 h11 => ?_⟩
    obtain ⟨B1, s1, hpc1, h4', h5', h6', h11', hm1, ho1⟩ :=
      run_digitT hfit hseg hA h4 h5 h6 h11 (by omega)
    have hw := rdW_write A.mem (bufBase + 8 * j) (BitVec.ofNat 64 (N % 10 + 48))
    rw [if_neg (fun h => hsmall (hN ▸ (tdiv_word_zero x).mp h))] at hpc1
    obtain ⟨B, s2, hpc, h5f, h6f, h11f, hof, hcells, hframe⟩ := hτ' hfit hseg hpc1 h4' h5' h6' h11'
    have heq : ds ++ [N % 10] ++ digitsLE (N / 10) = ds ++ digitsLE N := by rw [hdl]; simp
    rw [heq] at h5f h6f hcells
    refine ⟨B, s1.trans s2, hpc, h5f, h6f, h11f, hof.trans ho1, ?_, ?_⟩
    · intro q hq1 hq2
      by_cases hqj : q = j
      · subst hqj
        rw [hframe _ (by omega), hm1, hN, hw]
        congr 2
        rw [hdl]; simp [hj]
      · exact hcells q (by omega) hq2
    · intro a ha
      rw [hframe a (by omega), hm1]
      exact rdW_write_other _ _ _ _ (by omega)

def out1Tr (i : Nat) : List Obs :=
  pobs 70 :: mobs (70 + 1) (bufBase + 8 * i) :: (lin (70 + 1 + 1) (li s3 (putcWord 0)).length ++
    (pobs (70 + 1 + 1 + (li s3 (putcWord 0)).length) ::
      (lin (70 + 1 + 1 + (li s3 (putcWord 0)).length + 1) (li s2 tohostW).length ++
        (mobs (70 + 1 + 1 + (li s3 (putcWord 0)).length + 1 + (li s2 tohostW).length) tohostAddr ::
          [pobs 96, pobs 97]))))

def outsTr : Nat → List Obs
  | 0 => out1Tr 0
  | i + 1 => out1Tr (i + 1) ++ outsTr i

def proTr (n : BitVec 64) : List Obs :=
  pobs 14 :: pobs (14 + 1) ::
    (if n.toInt ≥ 0 then [pobs 16] else pobs 16 :: putcTr (16 + 1) (BitVec.ofNat 8 45))

section
variable {code : List Ins} (hfit : Fits code) (hseg : Seg code 14 printCode)
include hfit hseg

theorem run_out1T {A : AM} {i d : Nat} {r : BitVec 64}
    (hA : A.pc = pcOf 70) (h5 : Has A.regs s5 (BitVec.ofNat 64 (i + 1)))
    (h6 : Has A.regs s6 (BitVec.ofNat 64 (bufBase + 8 * (i + 1)))) (h11 : Has A.regs s11 r)
    (hi : i < 20) (hd : d < 10) (hcell : rdW A.mem (bufBase + 8 * i) = BitVec.ofNat 64 (d + 48)) :
    ReachesT code A (out1Tr i) fun B => B.pc = (if i = 0 then pcOf 98 else pcOf 70) ∧
      Has B.regs s5 (BitVec.ofNat 64 i) ∧ Has B.regs s6 (BitVec.ofNat 64 (bufBase + 8 * i)) ∧
      Has B.regs s11 r ∧ B.mem = A.mem ∧ outStr B = outStr A ++ toString (Nat.digitChar d) := by
  have P := fun k (hk : k ≤ 100) => print_posOK hfit hseg hk
  have hb : bufBase = 0x80080000 := rfl
  have ht : tohostAddr = 0x8001ad00 := rfl
  have k70 := pI hseg (j := 56) (k := 70) (i := .addi s6 s6 (-8)) rfl rfl
  refine exT_step hfit k70 trivial hA (step_addi_eq hfit k70 hA (by decide) h6
    (w := BitVec.ofNat 64 (bufBase + 8 * i))
    (by rw [show (sign_extend (-8 : BitVec 12) : BitVec 64) = BitVec.ofInt 64 (-((8 : Nat) : Int))
          by decide, ofNat_sub_neg _ 8 (by omega) (by omega) (by decide),
          show bufBase + 8 * (i + 1) - 8 = bufBase + 8 * i by omega])) ?_
  have k71 := pI hseg (j := 57) (k := 70 + 1) (i := .ld a0 s6) rfl rfl
  have h6' : Has (gset A.regs s6 (BitVec.ofNat 64 (bufBase + 8 * i))) s6
      (BitVec.ofNat 64 (bufBase + 8 * i)) := by has_tac
  refine exT_mem hfit k71 rfl (by simp [insObs, mobs, h6'.src.2]; omega)
    (step_ld hfit k71 rfl (by decide) h6' (by rw [BitVec.toNat_ofNat]; unfold LdOK; omega)) ?_
  refine exT_trans (run_liT hfit (pS hseg (j := 58) (len := 11) (k := 70 + 1 + 1)
    (s := li s3 (putcWord 0)) rfl rfl) rfl (by decide)) ?_
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show bufBase + 8 * i < 2 ^ 64 by omega), hcell]
  have k83 := pI hseg (j := 69) (k := 70 + 1 + 1 + (li s3 (putcWord 0)).length) (i := .add s3 s3 a0)
    rfl rfl
  refine exT_step hfit k83 trivial rfl (step_add hfit k83 rfl (by decide) (by has_tac) (by has_tac)) ?_
  rw [putcWord_add _ (by omega)]
  refine exT_trans (run_liT hfit (pS hseg (j := 70) (len := 11)
    (k := 70 + 1 + 1 + (li s3 (putcWord 0)).length + 1) (s := li s2 tohostW) rfl rfl) rfl (by decide)) ?_
  have k95 := pI hseg (j := 81) (k := 70 + 1 + 1 + (li s3 (putcWord 0)).length + 1
    + (li s2 tohostW).length) (i := .sd s3 s2) rfl rfl
  refine exT_mem hfit k95 rfl (by
      simp only [insObs, mobs,
        (Has.set_self (rd := s2) _ tohostW (by decide) (by decide)).src.2, tohostW_toNat])
    ((step_htif hfit k95 rfl (by has_tac) (by has_tac) tohostW_toNat).trans (htifOut_putc _ _)) ?_
  have k96 := pI hseg (j := 82) (k := 96) (i := .addi s5 s5 (-1)) rfl rfl
  refine exT_step hfit k96 trivial (pcOf_succ _) (step_addi_eq hfit k96 (pcOf_succ _) (by decide)
    (by has_tac) (w := BitVec.ofNat 64 i)
    (by rw [show (sign_extend (-1 : BitVec 12) : BitVec 64) = BitVec.ofInt 64 (-((1 : Nat) : Int))
          by decide, ofNat_sub_neg _ 1 (by omega) (by omega) (by decide)]; rfl)) ?_
  have k97 := pI hseg (j := 83) (k := 97)
    (i := .br .ne s5 0 (BitVec.ofInt 13 (-4 * ((27 : Nat) : Int)))) rfl rfl
  refine exT_step hfit k97 trivial rfl (step_br_back hfit k97 rfl
    (Has.gs_self _ s5 (BitVec.ofNat 64 i) (by decide)) (Has.zero _)
    (P _ (by decide)) (by decide) (by decide)) ?_
  rw [guard_ne_zero]
  refine doneT ⟨?_, ?_, ?_, ?_, rfl, ?_⟩
  · by_cases h0 : i = 0
    · subst h0; simp
    · have : BitVec.ofNat 64 i ≠ 0 := by
        intro h; apply h0
        have := congrArg BitVec.toNat h
        simp at this; omega
      simp [h0]
      intro h; exact absurd h this
  · has_tac
  · has_tac
  · has_tac
  · simp only [outStr_push]
    congr 2
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.add_comm, char_digit d hd]

theorem run_outsT : ∀ (i : Nat) (A : AM) (ds : List Nat) (r : BitVec 64),
    A.pc = pcOf 70 → Has A.regs s5 (BitVec.ofNat 64 (i + 1)) →
    Has A.regs s6 (BitVec.ofNat 64 (bufBase + 8 * (i + 1))) → Has A.regs s11 r →
    i < 20 → i < ds.length →
    (∀ q, q ≤ i → ds[q]! < 10 ∧ rdW A.mem (bufBase + 8 * q) = BitVec.ofNat 64 (ds[q]! + 48)) →
    ReachesT code A (outsTr i) fun B => B.pc = pcOf 98 ∧ Has B.regs s11 r ∧ B.mem = A.mem ∧
      outStr B = outStr A ++ ((ds.take (i + 1)).map Nat.digitChar).reverse.foldl String.push "" := by
  intro i
  induction i with
  | zero =>
    intro A ds r hA h5 h6 h11 _ hl hc
    obtain ⟨hd, hcell⟩ := hc 0 (by omega)
    obtain ⟨B, s, hpc, _, _, h11', hm, ho⟩ := run_out1T hfit hseg hA h5 h6 h11 (by omega) hd hcell
    refine ⟨B, s, by simpa using hpc, h11', hm, ?_⟩
    rw [ho, take_succ_rev ds 0 hl]
    simp only [List.take_zero, List.map_nil, List.reverse_nil, List.foldl_cons, List.foldl_nil]
    rw [toString_eq_push]
  | succ i ih =>
    intro A ds r hA h5 h6 h11 hi hl hc
    obtain ⟨hd, hcell⟩ := hc (i + 1) (by omega)
    obtain ⟨B1, s1, hpc, h5', h6', h11', hm, ho⟩ :=
      run_out1T hfit hseg hA h5 h6 h11 (by omega) hd hcell
    rw [if_neg (by omega)] at hpc
    obtain ⟨B, s2, hpc2, h11f, hm2, ho2⟩ := ih B1 ds r hpc h5' h6' h11' (by omega) (by omega)
      (fun q hq => by rw [hm]; exact hc q (by omega))
    refine ⟨B, s1.trans s2, hpc2, h11f, hm2.trans hm, ?_⟩
    rw [ho2, ho, take_succ_rev ds (i + 1) hl, List.foldl_cons, foldl_push _ ("".push _),
      String.append_assoc, toString_eq_push]

theorem run_prologueT {A : AM} {n r : BitVec 64} (hA : A.pc = pcOf 14)
    (ha0 : Has A.regs a0 n) (hra : Has A.regs ra r) :
    ReachesT code A (proTr n) fun B => B.pc = pcOf 40 ∧ Has B.regs s4 n ∧ Has B.regs s11 r ∧
      B.mem = A.mem ∧ outStr B = outStr A ++ (if n.toInt < 0 then "-" else "") := by
  have P := fun k (hk : k ≤ 100) => print_posOK hfit hseg hk
  have k14 := pI hseg (j := 0) (k := 14) (i := mv s11 ra) rfl rfl
  refine exT_step hfit k14 trivial hA (step_addi_eq hfit k14 hA (by decide) hra
    (add_sext_zero r)) ?_
  have k15 := pI hseg (j := 1) (k := 14 + 1) (i := mv s4 a0) rfl rfl
  refine exT_step hfit k15 trivial rfl (step_addi_eq hfit k15 rfl (by decide)
    (by has_tac) (add_sext_zero n)) ?_
  have k16 := pI hseg (j := 2) (k := 16) (i := .br .ge s4 0 (bSkip 23)) rfl rfl
  have e := step_br hfit k16
    (A := ⟨pcOf (14 + 1 + 1), gset (gset A.regs s11 r) s4 n, A.mem, A.out⟩) rfl
    (Has.gs_self _ s4 n (by decide)) (Has.zero _)
    (by rw [pcOf_skip _ _ (P _ (by decide)) (by decide), pcOf_toNat (by decide)]; decide)
  rw [pcOf_skip _ _ (P _ (by decide)) (by decide), zopz_ge] at e
  by_cases hs : n.toInt ≥ 0
  · rw [if_pos (by simpa using hs)] at e
    rw [if_pos hs]
    refine exT_step hfit k16 trivial rfl e (doneT ⟨rfl, by has_tac, by has_tac, rfl, ?_⟩)
    rw [if_neg (by omega)]; simp [outStr]
  · rw [if_neg (by simpa using hs)] at e
    rw [if_neg hs]
    have r1 := run_putcWT hfit (c := BitVec.ofNat 8 45)
      (pS hseg (j := 3) (len := 23) (k := 16 + 1)
        (s := li s3 (putcWord (BitVec.ofNat 8 45)) ++ li s2 tohostW ++ [.sd s3 s2]) rfl rfl)
      (A := ⟨pcOf (16 + 1), gset (gset A.regs s11 r) s4 n, A.mem, A.out⟩) rfl
    refine exT_step hfit k16 trivial rfl e ⟨_, r1, rfl, by has_tac, by has_tac, rfl, ?_⟩
    rw [if_pos (by omega), outStr_push]
    rfl

end

theorem run_printT (n : BitVec 64) : ∃ τ : List Obs, ∀ {code : List Ins} {k : Nat} {A : AM}
    {r : BitVec 64}, Fits code → Seg code printPos printCode → A.pc = pcOf printPos →
    Has A.regs a0 n → Has A.regs ra r → r = pcOf k → PosOK k →
    ReachesT code A τ fun B => B.pc = r ∧ outStr B = outStr A ++ intToString n.toInt ∧
      ∀ a, (a + 8 ≤ bufBase ∨ bufBase + 8 * 20 ≤ a) → rdW B.mem a = rdW A.mem a := by
  have hb : bufBase = 0x80080000 := rfl
  have hN : n.toInt.natAbs ≤ 2 ^ 63 := by
    have hb1 := BitVec.le_toInt n
    have hb2 : n.toInt < 2 ^ (64 - 1) := BitVec.toInt_lt
    rw [show (2 : Int) ^ (64 - 1) = 9223372036854775808 by decide] at hb1 hb2
    omega
  have hlen : (digitsLE n.toInt.natAbs).length ≤ 19 :=
    digitsLE_length_le 18 _ (by omega)
  obtain ⟨τd, hτd⟩ := run_digitsT n.toInt.natAbs n 0 [] rfl rfl (by simpa using hlen)
  have hpos : 1 ≤ (digitsLE n.toInt.natAbs).length := by
    unfold digitsLE; split <;> simp
  obtain ⟨J, hJ⟩ : ∃ J, (digitsLE n.toInt.natAbs).length = J + 1 := ⟨_, (Nat.sub_add_cancel hpos).symm⟩
  refine ⟨proTr n ++ (lin 40 (li s6 (BitVec.ofNat 64 bufBase)).length ++
    (pobs (40 + (li s6 (BitVec.ofNat 64 bufBase)).length) ::
      (τd ++ (outsTr J ++ [pobs 98, pobs (98 + 1)])))),
    fun {code k A r} hfit hseg hA ha0 hra hr hk => ?_⟩
  have P := fun k (hk : k ≤ 100) => print_posOK hfit hseg hk
  obtain ⟨B1, s1, hpc1, h4, h11, hm1, ho1⟩ := run_prologueT hfit hseg hA ha0 hra
  refine exT_trans s1 ?_
  refine exT_trans (run_liT hfit (pS hseg (j := 26) (len := 11) (k := 40)
    (s := li s6 (BitVec.ofNat 64 bufBase)) rfl rfl) hpc1 (by decide)) ?_
  have k51 := pI hseg (j := 37) (k := 40 + (li s6 (BitVec.ofNat 64 bufBase)).length)
    (i := .addi s5 0 0) rfl rfl
  refine exT_step hfit k51 trivial rfl (step_addi_eq hfit k51 rfl (by decide) (Has.zero _)
    (w := BitVec.ofNat 64 0) (by decide)) ?_
  obtain ⟨B2, s2, hpc2, h5, h6, h11', ho2, hcells, hframe⟩ := hτd (A := ⟨pcOf (40 +
      (li s6 (BitVec.ofNat 64 bufBase)).length + 1), gset (gset B1.regs s6 (BitVec.ofNat 64 bufBase))
      s5 (BitVec.ofNat 64 0), B1.mem, B1.out⟩) hfit hseg rfl (by has_tac)
    (by has_tac) (by simp only [Nat.mul_zero, Nat.add_zero]; has_tac) (by has_tac)
  refine exT_trans s2 ?_
  simp only [List.nil_append] at h5 h6 hcells
  rw [hJ] at h5 h6 hcells
  obtain ⟨B3, s3', hpc3, h11'', hm3, ho3⟩ := run_outsT hfit hseg J B2 (digitsLE n.toInt.natAbs) r hpc2
    h5 h6 h11' (by omega) (by omega) (fun q hq => ⟨digitsLE_lt _ _ (by
          rw [getElem!_pos _ q (by omega)]; exact List.getElem_mem (by omega)),
        hcells q (by omega) (by omega)⟩)
  refine exT_trans s3' ?_
  have k98 := pI hseg (j := 84) (k := 98) (i := mv ra s11) rfl rfl
  refine exT_step hfit k98 trivial hpc3 (step_addi_eq hfit k98 hpc3 (by decide) h11''
    (add_sext_zero r)) ?_
  have hb' : codeBase = 0x80004800 := rfl
  have ht' : tohostAddr = 0x8001ad00 := rfl
  have k99 := pI hseg (j := 85) (k := 98 + 1) (i := .jalr ra) rfl rfl
  refine exT_step hfit k99 trivial rfl (step_jalr hfit k99 rfl
    (Has.gs_self _ ra r (by decide)) (by rw [hr, pcOf_toNat (by unfold PosOK at hk; omega)]; omega)) ?_
  refine doneT ⟨rfl, ?_, ?_⟩
  · show outStr B3 = _
    rw [ho3]
    have hB2 : outStr B2 = outStr B1 := by simp [outStr, ho2]
    rw [hB2, ho1, intToString_eq, natToString_eq, String.append_assoc, ← hJ, List.take_length]
  · intro a ha
    show rdW B3.mem a = rdW A.mem a
    rw [hm3, hframe a (by omega), ← hm1]

end Vsa.Compiler
