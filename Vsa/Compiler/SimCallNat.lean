import Vsa.Compiler.SimCallCode

/-!
# Forward simulation: calls of natives

`print`/`println` display their arguments; `assert` checks the truthiness of its
first argument.
-/

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

theorem StackOK.frames {d sp fs : Nat} (h : StackOK d sp fs) : frameBase ≤ sp := by
  have := h.bounds.1
  have hl : stackLo = 0xE0000000 := rfl
  have hf : frameBase = 0x80100000 := rfl
  omega

/-- A native's return: display output, `null` in `(a0, a1)`. -/
theorem epost_native {code : List Ins} {T : List String} {V : View} {st : St} {d : Nat} {env : Addr}
    {Γ : List (List String)} {sp fs k : Nat} {A B : AM} (hm : MS code T V st d env Γ sp fs A)
    {S : List Nat} (hS : Scratch S) (hk : Keep S A.regs B.regs) (hd : DpFrame A.mem B.mem) {out' : String}
    (hout : String.join B.out.toList = out') (h10 : Has B.regs a0 0) (h11 : Has B.regs a1 0) :
    EPost code T V st d env Γ sp fs k A 0 ⟨st.store, out'⟩ .null V B where
  ms := by
    have h := hm.transport (B := ⟨B.pc, B.regs, B.mem, A.out⟩) hS hk (hd.above (Nat.le_refl _)) (hd.obj _) rfl
    exact ⟨h.rel, h.img, h.clo, h.chn, hout, h.ho, h.hf, h.henv, h.hsp, h.hdep, h.stk, h.hfal⟩
  val := ⟨0, 0, h10, h11, rfl, rfl⟩
  grow := VGrow.refl _ _
  within := Within.refl _ _
  stack := ⟨hd.above hm.stk.frames, hd.above (Nat.le_trans hm.stk.frames (Nat.le_add_right _ _))⟩
  obj := hd.obj _

theorem ccFin_eq (k m pos : Nat) : pos + (callCode k m pos).length = ccFin k m pos := by
  rw [callCode_length]
  have : pos ≤ ccFin k m pos := by simp only [ccFin, ccCL_eq, ccPL_eq, ccPR_eq]; omega
  omega

theorem ccPrC_length (k m pos : Nat) : (ccPrC k m pos).length = plLen (k + 1) m + 2 := by
  simp [ccPrC, printLoopG_len]

theorem ccPlC_length (k m pos : Nat) : (ccPlC k m pos).length = plLen (k + 1) m + 25 := by
  simp only [ccPlC, List.length_append, printLoopG_len, List.length_cons, List.length_nil]
  have : (putc '\n').length = 23 := by decide
  omega

section
variable {code : List Ins} {T : List String} (hR : RTLoaded code)
include hR

theorem cPrint (st : St) (d : Nat) (vs : List Value) :
    CSpec code T st d (.native .print) vs ⟨st.store, st.out ++ printArgs st.store vs⟩ .null 0 := by
  intro V env Γ sp fs k pos A hm hA hf hvs hmax hseg hP htmp
  have hs := CCSegs.of hseg
  have hfin := ccFin_eq k vs.length pos
  obtain ⟨pc, L, m, o⟩ := A
  simp only at hA; subst hA
  obtain ⟨ht5, hp0⟩ : rdW m (sp + 16 + 16 * k) = 5 ∧ rdW m (sp + 16 + 16 * k + 8) = 0 := hf
  refine ex_bind (run_dispatch hR hs hP hm.hsp hm.stk (by omega)) ?_
  rintro ⟨pc1, L1, m1, o1⟩ ⟨hm1, ho1, hk1, -, hpc1⟩
  simp only at hm1 ho1 hk1 hpc1; subst hm1 ho1 hpc1
  rw [ht5, hp0] at *
  simp only [dispTgt, show (5 : BitVec 64) ≠ 4 by decide, if_false, if_true] at *
  have hpr := hs.pr
  simp only [ccPrC] at hpr
  obtain ⟨sl, sz⟩ := hpr.append
  have hpos : ccPR k vs.length pos + (printLoopG (ccPR k vs.length pos) (k + 1) vs.length).length + 2 + 1 ≤
      ccFin k vs.length pos := by
    simp only [ccFin, ccCL_eq, ccPL_eq, ccPrC_length, printLoopG_len]; omega
  refine ex_bind (run_printLoop hR (s := st.store) hm.stk hm.rel.clo hm.img.ptr.hi vs (k + 1) _ L1 _ _ sl
    (posOK_le hP (by omega)) (hk1.has (by decide) hm.hsp) (by omega) hvs (ObjAgree.refl _ _) hm.img.fixed) ?_
  rintro ⟨pc2, L2, m2, o2⟩ ⟨hpc2, ho2, hd2, hk2⟩
  simp only at hpc2 ho2 hd2 hk2; subst hpc2
  apply run_whole hR.fits sz
  wp_simp []
  have hj := hs.prJ.cast (pos' := ccPR k vs.length pos + (printLoopG (ccPR k vs.length pos) (k + 1)
    vs.length).length + 2) (by simp only [ccPL_eq, ccPrC_length, printLoopG_len]; omega)
  have hPL : ccPL k vs.length pos = ccPR k vs.length pos + (printLoopG (ccPR k vs.length pos) (k + 1)
      vs.length).length + 2 + 1 := by simp only [ccPL_eq, ccPrC_length, printLoopG_len]; omega
  have hF : PosOK (ccFin k vs.length pos) := posOK_le hP (by omega)
  apply run_jumps hR.fits hj
  wp_simp [hF]
  refine reach_here (.inr ⟨by rw [hfin], V, ?_⟩)
  have hk : Keep (a0 :: a1 :: t0 :: t1 :: t2 :: prClob) L (gset (gset L2 10 0) 11 0) := by
    reg_simp []; exact (hk1.mono (by decide)).trans (hk2.mono (by decide))
  have hout : String.join o2.toList = st.out ++ printArgs st.store vs := by
    show ostr _ = _; rw [ho2]; rw [show ostr o1 = st.out from hm.out]
  have hS : Scratch (a0 :: a1 :: t0 :: t1 :: t2 :: prClob) := by decide
  have g10 : Has (gset (gset L2 10 0) 11 0) a0 0 := by reg_simp []
  have g11 : Has (gset (gset L2 10 0) 11 0) a1 0 := by reg_simp []
  exact epost_native (B := ⟨pcOf (ccFin k vs.length pos), gset (gset L2 10 0) 11 0, m2, o2⟩) hm hS hk hd2 hout g10 g11

theorem cPrintln (st : St) (d : Nat) (vs : List Value) :
    CSpec code T st d (.native .println) vs ⟨st.store, st.out ++ printArgs st.store vs ++ "\n"⟩ .null 0 := by
  intro V env Γ sp fs k pos A hm hA hf hvs hmax hseg hP htmp
  have hs := CCSegs.of hseg
  have hfin := ccFin_eq k vs.length pos
  obtain ⟨pc, L, m, o⟩ := A
  simp only at hA; subst hA
  obtain ⟨ht5, hp1⟩ : rdW m (sp + 16 + 16 * k) = 5 ∧ rdW m (sp + 16 + 16 * k + 8) = 1 := hf
  refine ex_bind (run_dispatch hR hs hP hm.hsp hm.stk (by omega)) ?_
  rintro ⟨pc1, L1, m1, o1⟩ ⟨hm1, ho1, hk1, -, hpc1⟩
  simp only at hm1 ho1 hk1 hpc1; subst hm1 ho1 hpc1
  rw [ht5, hp1] at *
  simp only [dispTgt, show (5 : BitVec 64) ≠ 4 by decide, show (1 : BitVec 64) ≠ 0 by decide, if_false,
    if_true] at *
  have hpl := hs.pl
  simp only [ccPlC] at hpl
  obtain ⟨sl, sz⟩ := hpl.append
  obtain ⟨sl, sn⟩ := sl.append
  have hlp : (putc '\n').length = 23 := by decide
  simp only [List.length_append, hlp] at sz
  have hpos : ccPL k vs.length pos + (printLoopG (ccPL k vs.length pos) (k + 1) vs.length).length + 25 + 1 ≤
      ccFin k vs.length pos := by
    simp only [ccFin, ccCL_eq, ccPlC_length, printLoopG_len]; omega
  refine ex_bind (run_printLoop hR (s := st.store) hm.stk hm.rel.clo hm.img.ptr.hi vs (k + 1) _ L1 _ _ sl
    (posOK_le hP (by omega)) (hk1.has (by decide) hm.hsp) (by omega) hvs (ObjAgree.refl _ _) hm.img.fixed) ?_
  rintro ⟨pc2, L2, m2, o2⟩ ⟨hpc2, ho2, hd2, hk2⟩
  simp only at hpc2 ho2 hd2 hk2; subst hpc2
  apply run_whole hR.fits sn
  wp_simp [putc]
  apply run_whole hR.fits (sz.cast (pos' := ccPL k vs.length pos + (printLoopG (ccPL k vs.length pos) (k + 1)
    vs.length).length + 23) (by omega))
  wp_simp []
  have hj := hs.plJ.cast (pos' := ccPL k vs.length pos + (printLoopG (ccPL k vs.length pos) (k + 1)
    vs.length).length + 23 + 2) (by simp only [ccCL_eq, ccPlC_length, printLoopG_len]; omega)
  have hCL : ccCL k vs.length pos = ccPL k vs.length pos + (printLoopG (ccPL k vs.length pos) (k + 1)
      vs.length).length + 23 + 2 + 1 := by simp only [ccCL_eq, ccPlC_length, printLoopG_len]; omega
  have hF : PosOK (ccFin k vs.length pos) := posOK_le hP (by omega)
  apply run_jumps hR.fits hj
  wp_simp [hF]
  refine reach_here (.inr ⟨by rw [hfin], V, ?_⟩)
  have hk : Keep (a0 :: a1 :: t0 :: t1 :: t2 :: prClob) L (gset (gset (gset (gset L2 19 (putcWord
      (BitVec.ofNat 8 '\n'.toNat))) 18 tohostW) 10 0) 11 0) := by
    reg_simp []; exact (hk1.mono (by decide)).trans (hk2.mono (by decide))
  have hout : String.join (o2.push (toString (Char.ofNat (BitVec.ofNat 8 '\n'.toNat).toNat))).toList =
      st.out ++ printArgs st.store vs ++ "\n" := by
    show ostr _ = _; rw [ostr_push, ho2, show ostr o1 = st.out from hm.out]; rfl
  have hS : Scratch (a0 :: a1 :: t0 :: t1 :: t2 :: prClob) := by decide
  have g10 : Has (gset (gset (gset (gset L2 19 (putcWord (BitVec.ofNat 8 '\n'.toNat))) 18 tohostW) 10 0) 11 0)
    a0 0 := by reg_simp []
  have g11 : Has (gset (gset (gset (gset L2 19 (putcWord (BitVec.ofNat 8 '\n'.toNat))) 18 tohostW) 10 0) 11 0)
    a1 0 := by reg_simp []
  exact epost_native (B := ⟨pcOf (ccFin k vs.length pos), gset (gset (gset (gset L2 19 (putcWord
      (BitVec.ofNat 8 '\n'.toNat))) 18 tohostW) 10 0) 11 0, m2,
    o2.push (toString (Char.ofNat (BitVec.ofNat 8 '\n'.toNat).toNat))⟩) hm hS hk hd2 hout g10 g11

theorem cAssert (st : St) (d : Nat) (vs : List Value) (v w : Value) (hvs : vs = [v] ∨ vs = [v, w])
    (ht : v.truthy = true) : CSpec code T st d (.native .assert) vs st .null 0 := by
  intro V env Γ sp fs k pos A hm hA hf hvs' hmax hseg hP htmp
  have hs := CCSegs.of hseg
  have hfin := ccFin_eq k vs.length pos
  have hm12 : vs.length = 1 ∨ vs.length = 2 := by rcases hvs with rfl | rfl <;> simp
  have hv0 : InTmp V.H A.mem V.h sp (k + 1) v := by
    have := hvs' 0 (by rcases hvs with rfl | rfl <;> simp)
    rcases hvs with rfl | rfl <;> simpa using this
  obtain ⟨pc, L, m, o⟩ := A
  simp only at hA; subst hA
  obtain ⟨ht5, hp2⟩ : rdW m (sp + 16 + 16 * k) = 5 ∧ rdW m (sp + 16 + 16 * k + 8) = 2 := hf
  refine ex_bind (run_dispatch hR hs hP hm.hsp hm.stk (by omega)) ?_
  rintro ⟨pc1, L1, m1, o1⟩ ⟨hm1, ho1, hk1, -, hpc1⟩
  simp only at hm1 ho1 hk1 hpc1; subst hm1 ho1 hpc1
  rw [ht5, hp2] at *
  simp only [dispTgt, show (5 : BitVec 64) ≠ 4 by decide, show (2 : BitVec 64) ≠ 0 by decide,
    show (2 : BitVec 64) ≠ 1 by decide, if_false, if_true] at *
  have ha := hs.asrt
  have ea : ccAssert k vs.length pos = loadTmp (k + 1) ++ [Call (pos + 15 + 4) trPos] ++
      jmpIfZero (pos + 15 + 5) errPos ++ [mvi a0 0, mvi a1 0] := by simp [ccAssert, hm12]
  rw [ea] at ha
  obtain ⟨s1, s4⟩ := ha.append
  obtain ⟨s1, s3⟩ := s1.append
  obtain ⟨s1, s2⟩ := s1.append
  have e4 : (loadTmp (k + 1)).length = 4 := by simp [loadTmp]
  simp only [List.length_append, e4, List.length_singleton, jmpIfZero, List.length_cons, List.length_nil] at s2 s3 s4
  have hPR : ccPR k vs.length pos = pos + 15 + 9 + 1 := by simp only [ccPR_eq, ea]; simp [loadTmp, jmpIfZero]
  have hpos : ccPR k vs.length pos ≤ ccFin k vs.length pos := by
    simp only [ccFin, ccCL_eq, ccPL_eq]; omega
  have hq : PosOK (pos + 15 + 4 + 1) := posOK_le hP (by omega)
  refine run_loadTmp hR.fits s1 (hk1.has (by decide) hm.hsp) hm.stk (by omega) fun L2 hk2 g10 g11 => ?_
  apply run_whole hR.fits (s2.cast (pos' := pos + 15 + 4) (by omega))
  wp_simp [hq]
  refine ex_bind (run_tr hR.fits hR.tr (L := gset L2 1 (pcOf (pos + 15 + 4 + 1))) (m := m1) (o := o1)
    (by reg_simp []; exact g10) (by reg_simp []; exact g11) (by reg_simp []) (pcOf_aligned hq)) ?_
  rintro ⟨pc3, L3, m3, o3⟩ ⟨hpc3, hm3, ho3, g10', hk3⟩
  simp only at hpc3 hm3 ho3 g10' hk3; subst hpc3 hm3 ho3
  have hv0' : VRepr V.H m3 V.h v (rdW m3 (sp + 16 + 16 * (k + 1))) (rdW m3 (sp + 16 + 16 * (k + 1) + 8)) := hv0
  rw [trW_repr hv0', ht] at g10'
  have k10 := has_mem g10' (by decide); have e10 := srcVal_of_has g10'
  simp only [a0] at k10 e10
  apply run_jumps hR.fits (s3.cast (pos' := pos + 15 + 5) (by omega))
  wp_simp [k10, e10]
  apply run_whole hR.fits (s4.cast (pos' := pos + 15 + 5 + 2) (by omega))
  wp_simp []
  have hj := hs.asrtJ.cast (pos' := pos + 15 + 5 + 2 + 2) (by omega)
  have hF : PosOK (ccFin k vs.length pos) := posOK_le hP (by omega)
  apply run_jumps hR.fits hj
  wp_simp [hF]
  refine reach_here (.inr ⟨by rw [hfin], V, ?_⟩)
  have hS : Scratch [a0, a1, t0, t1, t2, t6, ra] := by decide
  have hk : Keep [a0, a1, t0, t1, t2, t6, ra] L (gset (gset L3 10 0) 11 0) := by
    reg_simp []
    exact (hk1.mono (by decide)).trans ((hk2.mono (by decide)).trans
      ((Keep.gset (Keep.refl _ L2) (by decide)).trans (hk3.mono (by decide))))
  have g10 : Has (gset (gset L3 10 0) 11 0) a0 0 := by reg_simp []
  have g11 : Has (gset (gset L3 10 0) 11 0) a1 0 := by reg_simp []
  have hst : st = ⟨st.store, st.out⟩ := rfl
  rw [hst]
  exact epost_native (B := ⟨pcOf (ccFin k vs.length pos), gset (gset L3 10 0) 11 0, m3, o3⟩) hm hS hk
    (DpFrame.refl _) hm.out g10 g11

end

end Vsa.Compiler
