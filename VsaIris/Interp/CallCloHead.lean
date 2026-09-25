import VsaIris.Interp.CallClosure

/-!
# The closure call's head (lane E4)

`callCloHead` (either WP): from the kind dispatch `0x80003254` on a closure
value, runs K1a-K1d (`CallClosure.lean`) with the call node's, the closure
object's and the `EX_FN` node's data views and the depth word joined into the
run's bytes (`cloS`): `fn_expr`, the arity test, `++in->call_depth`, the depth
test, `cl->env`. Three exits (`CloHeadK`): the `jal env_new` (`CloHd`), the
arity error (`CloAr`), the depth error (`CloDp`).
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Newlib
open Vsa.MemRepr Vsa.Sim Vsa.While
open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.RuntimeRepr

#ix_piece callCloHead_p1 {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {st : Store} {fe : Expr} {args : List Expr} {ca : Nat} {cd : ClosureData} {q e : Nat}
    {img : Nat → BitVec 8} {P : Nat → Prop} {m : Mem} {dimg : Nat → BitVec 8}
    {s aX sret inp ret w0 w1 w2 : BitVec 64} {rv R : Nat → BitVec 64} {Mt : Mem} {argc dep : Nat}
    (hcall : CallAt R Mt s aX sret inp ret rv w0 w1 w2 argc) (hargc : argc ≤ 32)
    (hk4 : w0.toNat % 2 ^ 32 = 4) (hcf : CloFactsE st ca w1.toNat cd q e img P m)
    (hinpG : RtErr.InpGeom inp) (hinpA : inp.toNat % 8 = 0)
    (hdep : imgLE dimg (inp.toNat + 8) 4 = dep) (hdle : dep ≤ maxCallDepth) (hfg : EvalFrameG s) :
    codeRes ∗ □ astEG aX.toNat (.call fe args) ∗ roImg (InExt (w1.toNat, 16)) img ∗ roOn P m ∗
      ms 0x80003254#64 R (InExt (s.toNat - 1088, 1088)) Mt ∗
      ownImg (InExt (inp.toNat + 8, 4)) dimg ∗
      CloHeadK live Wp Φ cd Mt s aX sret inp ret (BitVec.ofNat 64 e) (BitVec.ofNat 64 q) rv argc dep
    ⊢ Wp.W Φ by
  have hsf := hfg.sf; have hs' := hfg.lo; have hs2 := hfg.hi; have hs3 := hfg.al
  have hoff := evalSP_off (s := s) hsf (by omega)
  iintro ⟨#Hcode, #Hast, #Himg, #Hro, Hms, Hdep, Hk⟩
  unfold astEG
  icases Hast with ⟨%Pc, %mc, %⟨hrepr, hgeo⟩, #Hroc⟩
  obtain ⟨aF, hnd, -, -⟩ := callNode_of_repr hrepr hgeo
  -- run K1a: the kind tests
  ihave #Hdv := roOwn_data hnd.view $$ [Hcode Hroc]
  · iframe Hcode Hroc
  iapply wp_swpF Wp (F := iprop(codeRes ∗ roImg (InExt (w1.toNat, 16)) img ∗ roOn P m ∗
      ownImg (InExt (inp.toNat + 8, 4)) dimg ∗
      CloHeadK live Wp Φ cd Mt s aX sret inp ret (BitVec.ofNat 64 e) (BitVec.ofNat 64 q) rv argc dep))
  rotate_left
  · iframe Hdv Hms Hcode Himg Hro Hdep; iexact Hk
  intro F'
  refine CallK_runA (w0 := w0) (w1 := w1) (w2 := w2) hlive hsf hs' hs2 hs3 hnd.lo hnd.hi hnd.off
    hcall.s0 hcall.sp ?_ ?_ ?_ ?_ ?_
  · rw [hoff 96 (by decide)]; exact hcall.w0
  · rw [hoff 104 (by decide)]; exact hcall.w1
  · rw [hoff 112 (by decide)]; exact hcall.w2
  · rw [hoff 96 (by decide)]; exact ldv_lw_of_ld hcall.w0 hk4 (by decide)
  intro vl _ _
  apply swp_closeRM
  intro R1 Mt1 hR1 hMt1
  unfold F'
  iintro ⟨⟨#Hcode, #Himg, #Hro, Hdep, Hk⟩, Hms⟩
  -- run K1b: `fn_expr` from the closure object
  have hc1 := hcf.objOK w1.toNat (by simp [InExt]); have hc16 := hcf.objOK (w1.toNat + 15) (by simp [InExt])
  ihave ⟨%Dt, #Hdc, %hDt⟩ := roOwn_roImg (p := w1.toNat) (n := 16) $$ [Hcode Himg]
  · iframe Hcode Himg
  have hq : ldv .ld Dt w1.toNat = BitVec.ofNat 64 q := by
    rw [ldv_ld_imgW]; unfold imgW
    rw [imgLE_congr (img' := img) (fun i hi => hDt _ (by omega) (by omega)), hcf.fn]
  iapply wp_swpF Wp (F := iprop(codeRes ∗ roImg (InExt (w1.toNat, 16)) img ∗ roOn P m ∗
      ownImg (InExt (inp.toNat + 8, 4)) dimg ∗
      CloHeadK live Wp Φ cd Mt s aX sret inp ret (BitVec.ofNat 64 e) (BitVec.ofNat 64 q) rv argc dep))
  rotate_left
  · iframe Hdc Hms Hcode Himg Hro Hdep; iexact Hk
  intro F'
  refine CallK_runB (cp := w1) hlive hsf hs' hs2 hs3 hc1.lo (by have := hc16.hi; omega)
    (by have := hc1.off; have := hc16.off; omega)
    (by subst hR1; ix_reg) (by subst hR1; ix_reg; exact hcall.sp) hq ?_
  apply swp_closeRM
  intro R2 Mt2 hR2 hMt2
  unfold F'
  iintro ⟨⟨#Hcode, #Himg, #Hro, Hdep, Hk⟩, Hms⟩

#ix_piece callCloHead_p2 from callCloHead_p1 by
  -- the depth word into the run's bytes
  ihave ⟨%Md, Hdep, %hMd⟩ := ownSet_trackedAt _ dimg $$ Hdep
  ihave ⟨%M3, Hms, %⟨hM3f, hM3d, hdisj⟩⟩ := ms_join $$ [Hms Hdep]
  · iframe Hms Hdep
  have hi3 : inp.toNat + 8 + 4 ≤ s.toNat - 1088 ∨ s.toNat ≤ inp.toNat + 8 := by
    refine Classical.byContradiction fun hc => ?_
    exact hdisj (max (s.toNat - 1088) (inp.toNat + 8)) (by simp only [InExt]; omega)
      (by simp only [InExt]; omega)
  have hdep3 : imgLE (imgM M3) (inp.toNat + 8) 4 = dep := by
    rw [imgLE_congr (img' := dimg) (fun i hi => (hM3d _ (by simp [InExt]; omega)).trans
      (hMd _ (by simp [InExt]; omega))), hdep]
  -- the `EX_FN` node
  have hqlt : q < 2 ^ 64 := by rw [← hcf.fn]; have := imgLE_lt img w1.toNat 8; omega
  have hqt : (BitVec.ofNat 64 q).toNat = q := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hqlt]
  have hrepq : ExprReprWithin m P (BitVec.ofNat 64 q).toNat (.fn cd.name cd.params cd.body) := by
    rw [hqt]; exact hcf.repr
  obtain ⟨prm, bod, nam, hfn, -, -, -, hps, hbody, hname⟩ := fnNode_of hrepq hcf.geo
  ihave #Hdf := roOwn_data (DA := accAddrs ((BitVec.ofNat 64 q).toNat + 24) 4)
    (fun a ha => hfn.view a (by simp only [List.mem_append, mem_accAddrs_iff] at ha ⊢; omega))
    $$ [Hcode Hro]
  · iframe Hcode Hro
  -- run K1c: the arity test, the depth bump, the depth test
  have hdl : ldv .lw M3 (inp + 8#64).toNat = BitVec.ofNat 64 dep := by
    rw [show (inp + 8#64).toNat = inp.toNat + 8 by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; have := hinpG.hi; omega]
    exact ldvf_lw_imgLE hdep3 (by unfold maxCallDepth at hdle; omega)
  have h14 : R2 14 = BitVec.ofNat 64 q := by subst hR2; ix_reg
  have h18 : R2 18 = inp := by subst hR2; subst hR1; ix_reg; exact hcall.s2
  have h2' : R2 2 = s + 18446744073709550528#64 := by subst hR2; subst hR1; ix_reg; exact hcall.sp
  iapply wp_swpF Wp (F := iprop(codeRes ∗ roImg (InExt (w1.toNat, 16)) img ∗ roOn P m ∗
      CloHeadK live Wp Φ cd Mt s aX sret inp ret (BitVec.ofNat 64 e) (BitVec.ofNat 64 q) rv argc dep))
  rotate_left
  · iframe Hdf Hms Hcode Himg Hro; iexact Hk
  intro F'
  refine CallK_runC hlive hsf hs' hs2 hs3 hfn.lo (by have := hfn.hi; omega)
    (by have := hfn.off; omega) hinpG.lo hinpG.hi hi3 hinpA h14 h18 h2' rfl hdl ?_ ?_ ?_
  intro hne
  apply swp_closeRM
  intro R3 Mt3 hR3 hMt3
  unfold F'
  iintro ⟨⟨#Hcode, #Himg, #Hro, Hk⟩, Hms⟩
  rotate_left
  intro heq hlt
  apply swp_closeRM
  intro R3 Mt3 hR3 hMt3
  unfold F'
  iintro ⟨⟨#Hcode, #Himg, #Hro, Hk⟩, Hms⟩
  rotate_left
  intro heq hnlt
  apply swp_closeRM
  intro R3 Mt3 hR3 hMt3
  unfold F'
  iintro ⟨⟨#Hcode, #Himg, #Hro, Hk⟩, Hms⟩
  rotate_left
  rotate_right

#ix_piece callCloHead_p3 from callCloHead_p2 by
  -- run K1d: `cl->env`, `argc` spilled
  ihave ⟨%Dt', #Hdc, %hDt'⟩ := roOwn_roImg (p := w1.toNat) (n := 16) $$ [Hcode Himg]
  · iframe Hcode Himg
  have he : ldv .ld Dt' (w1 + 8#64).toNat = BitVec.ofNat 64 e := by
    rw [show (w1 + 8#64).toNat = w1.toNat + 8 by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; have := hc16.hi; omega]
    rw [ldv_ld_imgW]; unfold imgW
    rw [imgLE_congr (img' := img) (fun i hi => hDt' _ (by omega) (by omega)), hcf.env]
  have h13 : R3 13 = w1 := by subst hR3; subst hR2; subst hR1; ix_reg
  have h2'' : R3 2 = s + 18446744073709550528#64 := by subst hR3; ix_reg; exact h2'
  iapply wp_swpF Wp (F := iprop(CloHeadK live Wp Φ cd Mt s aX sret inp ret (BitVec.ofNat 64 e)
      (BitVec.ofNat 64 q) rv argc dep))
  rotate_left
  · iframe Hdc Hms; iexact Hk
  intro F'
  refine CallK_runD (inp := inp) hlive hsf hs' hs2 hs3 hc1.lo (by have := hc16.hi; omega)
    (by have := hc1.off; have := hc16.off; omega) h13 h2'' he ?_
  apply swp_closeRM
  intro R4 Mt4 hR4 hMt4
  unfold F'
  iintro ⟨Hk, Hms⟩
  unfold CloHeadK
  ihave Hk := and_elim_l $$ Hk
  -- the count is `paramc`, the depth fits
  have h15 : R2 15 = BitVec.ofNat 64 argc := by subst hR2; subst hR1; ix_reg; exact hcall.a5
  have hpeq : cd.params.length = argc := by
    have h := heq; simp only [upd_apply, Nat.reduceEqDiff, ite_false, ne_eq, Decidable.not_not] at h
    rw [h15] at h
    exact ldvf_lw_eq_small hfn.pcr (by omega) h.symm
  have hdok : dep + 1 ≤ maxCallDepth := by
    have h := hnlt
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at h
    rw [idx_succ, sext32_ofNat_toInt (by unfold maxCallDepth at hdle; omega)] at h
    have : ((1000#64 : BitVec 64).toInt : Int) = 1000 := by decide
    unfold maxCallDepth; omega
  -- the memory: the spills and the depth word written, the rest as at the dispatch
  have hi8 : (inp + 8#64).toNat = inp.toNat + 8 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; have := hinpG.hi; omega
  have hun : ∀ a, InExt (s.toNat - 1088, 1088) a → ¬ InExt (s.toNat - 1088, 8) a →
      ¬ InExt (s.toNat - 1088 + 120, 24) a → ¬ InExt (s.toNat - 1088 + 1032, 8) a →
      ¬ InExt (s.toNat - 1088 + 1048, 8) a → imgM Mt4 a = imgM Mt a := by
    intro a hf h0 h1 h2 h3
    simp only [InExt] at hf h0 h1 h2 h3
    rw [hMt4, imgM_store_miss _ _ (by omega), hMt3, imgM_store_miss _ _ (by rw [hoff 1048 (by decide)]; omega),
      imgM_store_miss _ _ (by rw [hi8]; omega), hM3f a (by simp only [InExt]; omega), hMt2,
      imgM_store_miss _ _ (by rw [hoff 1032 (by decide)]; omega), hMt1,
      imgM_store_miss _ _ (by rw [hoff 136 (by decide)]; omega),
      imgM_store_miss _ _ (by rw [hoff 128 (by decide)]; omega),
      imgM_store_miss _ _ (by rw [hoff 120 (by decide)]; omega)]
  have hkeepM : ∀ o, 1056 ≤ o → o + 8 ≤ 1088 →
      ldv .ld Mt4 (s.toNat - 1088 + o) = ldv .ld Mt (s.toNat - 1088 + o) := fun o h1 h2 =>
    ldv_eqOn .ld (fun j hj => by
      simp only [widthOfM] at hj
      exact hun _ (by simp only [InExt]; omega) (by simp only [InExt]; omega)
        (by simp only [InExt]; omega) (by simp only [InExt]; omega) (by simp only [InExt]; omega))
  have h1016 : ldv .ld Mt4 (s.toNat - 1088 + 1016) = rv 23 := by
    rw [ldv_eqOn .ld (Mt' := Mt) (fun j hj => by
      simp only [widthOfM] at hj
      exact hun _ (by simp only [InExt]; omega) (by simp only [InExt]; omega)
        (by simp only [InExt]; omega) (by simp only [InExt]; omega) (by simp only [InExt]; omega))]
    exact hcall.sv23
  have h1048 : ldv .ld Mt4 (s.toNat - 1088 + 1048) = rv 19 := by
    rw [← hoff 1048 (by decide), hMt4, hMt3]
    ix_fwd
    subst hR2; subst hR1; ix_reg; exact hcall.keep 19 (by decide)
  have h1032 : ldv .ld Mt4 (s.toNat - 1088 + 1032) = rv 21 := by
    have e1 : ldv .ld Mt4 (s.toNat - 1088 + 1032) = ldv .ld M3 (s.toNat - 1088 + 1032) := by
      rw [← hoff 1032 (by decide), hMt4, hMt3]; ix_fwd
    rw [e1, ldv_eqOn .ld (Mt' := Mt2) (fun j hj => by
        simp only [widthOfM] at hj; exact hM3f _ (by simp only [InExt]; omega)),
      ← hoff 1032 (by decide), hMt2]
    ix_fwd
    subst hR1; ix_reg; exact hcall.keep 21 (by decide)
  have hsp0 : ldv .ld Mt4 (s.toNat - 1088) = BitVec.ofNat 64 argc := by
    rw [hMt4]; ix_fwd
    subst hR3; ix_reg; exact h15
  have hdepth : imgLE (imgM Mt4) (inp.toNat + 8) 4 = dep + 1 := by
    have hv : (BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 dep + 1#64))).toNat % 2 ^ 32
        = dep + 1 := by
      rw [idx_succ, sext32_toNat_small (by unfold maxCallDepth at hdle; omega)]
      exact Nat.mod_eq_of_lt (by unfold maxCallDepth at hdle; omega)
    rw [imgLE_congr (n := 4) (img' := imgM (writeLog M3 [((inp + 8#64).toNat,
        4, BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 dep + 1#64)))]))
      (fun i hi => by
        rw [hMt4, imgM_store_miss _ _ (by omega), hMt3,
          imgM_store_miss _ _ (by rw [hoff 1048 (by decide)]; omega)]),
      hi8, imgLE_store4_hit, hv]
  have hhd : CloHd R4 Mt4 Mt s aX sret inp ret (BitVec.ofNat 64 e) (BitVec.ofNat 64 q) vl rv argc dep := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩, h1048, h1032, h1016, hsp0, hdepth, ?_⟩
    all_goals first
      | (subst hR4; subst hR3; subst hR2; subst hR1; ix_reg; done)
      | (subst hR4; subst hR3; subst hR2; subst hR1; ix_reg; first
          | exact hcall.sp | exact hcall.s0 | exact hcall.s1 | exact hcall.s2)
      | skip
    · intro x hx
      have hx' : x = 19 ∨ x = 20 ∨ x = 22 ∨ x = 24 ∨ x = 25 ∨ x = 26 ∨ x = 27 := by simpa using hx
      subst hR4; subst hR3; subst hR2; subst hR1
      rcases hx' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (ix_reg; exact hcall.keep _ (by decide))
    · rw [hkeepM 1080 (by omega) (by omega)]; exact hcall.ra
    · rw [hkeepM 1072 (by omega) (by omega)]; exact hcall.sv8
    · rw [hkeepM 1064 (by omega) (by omega)]; exact hcall.sv9
    · rw [hkeepM 1056 (by omega) (by omega)]; exact hcall.sv18
    · intro a ha
      exact hun a (by simp only [InExt, argsBase] at ha ⊢; omega) (by simp only [InExt, argsBase] at ha ⊢; omega)
        (by simp only [InExt, argsBase] at ha ⊢; omega) (by simp only [InExt, argsBase] at ha ⊢; omega)
        (by simp only [InExt, argsBase] at ha ⊢; omega)
  iapply Hk $$ %R4 %Mt4 %vl %⟨hpeq, hdok, hhd⟩ Hms


#ix_piece callCloHead_p2b from callCloHead_p2 at 2 by
  -- the arity error: the count is not `paramc`
  unfold CloHeadK
  ihave Hk := and_elim_r $$ Hk
  ihave Hk := and_elim_l $$ Hk
  have h15 : R2 15 = BitVec.ofNat 64 argc := by subst hR2; subst hR1; ix_reg; exact hcall.a5
  have hpne : cd.params.length ≠ argc := by
    intro hpeq
    apply hne
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    rw [h15]
    exact ((ldvf_lw_imgLE hfn.pcr (by rw [hpeq]; omega)).trans (by rw [hpeq])).symm
  have hun : ∀ a, InExt (s.toNat - 1088, 1088) a → ¬ InExt (s.toNat - 1088 + 120, 24) a →
      ¬ InExt (s.toNat - 1088 + 1032, 8) a → imgM Mt3 a = imgM Mt a := by
    intro a hf h1 h2
    simp only [InExt] at hf h1 h2
    rw [hMt3, hM3f a (by simp only [InExt]; omega), hMt2,
      imgM_store_miss _ _ (by rw [hoff 1032 (by decide)]; omega), hMt1,
      imgM_store_miss _ _ (by rw [hoff 136 (by decide)]; omega),
      imgM_store_miss _ _ (by rw [hoff 128 (by decide)]; omega),
      imgM_store_miss _ _ (by rw [hoff 120 (by decide)]; omega)]
  have hkeepM : ∀ o, 1008 ≤ o → o + 8 ≤ 1088 → (o + 8 ≤ 1032 ∨ 1040 ≤ o) →
      ldv .ld Mt3 (s.toNat - 1088 + o) = ldv .ld Mt (s.toNat - 1088 + o) := fun o h1 h2 h3 =>
    ldv_eqOn .ld (fun j hj => by
      simp only [widthOfM] at hj
      exact hun _ (by simp only [InExt]; omega) (by simp only [InExt]; omega)
        (by simp only [InExt]; omega))
  have h1032 : ldv .ld Mt3 (s.toNat - 1088 + 1032) = rv 21 := by
    rw [hMt3, ldv_eqOn .ld (Mt' := Mt2) (fun j hj => by
        simp only [widthOfM] at hj; exact hM3f _ (by simp only [InExt]; omega)),
      ← hoff 1032 (by decide), hMt2]
    ix_fwd
    subst hR1; ix_reg; exact hcall.keep 21 (by decide)
  have har : CloAr R3 Mt3 Mt s aX sret inp ret (BitVec.ofNat 64 q) vl rv argc dep := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩, h1032, ?_, ?_, ?_⟩
    all_goals first
      | (subst hR3; subst hR2; subst hR1; ix_reg; done)
      | (subst hR3; subst hR2; subst hR1; ix_reg; first
          | exact hcall.sp | exact hcall.s0 | exact hcall.s1 | exact hcall.s2 | exact hcall.a5)
      | skip
    · intro x hx
      have hx' : x = 19 ∨ x = 20 ∨ x = 22 ∨ x = 24 ∨ x = 25 ∨ x = 26 ∨ x = 27 := by simpa using hx
      subst hR3; subst hR2; subst hR1
      rcases hx' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (ix_reg; exact hcall.keep _ (by decide))
    · rw [hkeepM 1080 (by omega) (by omega) (by omega)]; exact hcall.ra
    · rw [hkeepM 1072 (by omega) (by omega) (by omega)]; exact hcall.sv8
    · rw [hkeepM 1064 (by omega) (by omega) (by omega)]; exact hcall.sv9
    · rw [hkeepM 1056 (by omega) (by omega) (by omega)]; exact hcall.sv18
    · rw [hkeepM 1016 (by omega) (by omega) (by omega)]; exact hcall.sv23
    · rw [hMt3]; exact hdep3
    · intro a ha
      exact hun a (by simp only [InExt, argsBase] at ha ⊢; omega)
        (by simp only [InExt, argsBase] at ha ⊢; omega) (by simp only [InExt, argsBase] at ha ⊢; omega)
  iapply Hk $$ %R3 %Mt3 %vl %⟨hpne, har⟩ Hms


#ix_piece callCloHead_p2c from callCloHead_p2 at 3 by
  -- the depth error: the bumped depth exceeds the maximum
  unfold CloHeadK
  ihave Hk := and_elim_r $$ Hk
  ihave Hk := and_elim_r $$ Hk
  have hgt : maxCallDepth < dep + 1 := by
    have h := hlt
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at h
    rw [idx_succ, sext32_ofNat_toInt (by unfold maxCallDepth at hdle; omega)] at h
    have : ((1000#64 : BitVec 64).toInt : Int) = 1000 := by decide
    unfold maxCallDepth; omega
  have hi8 : (inp + 8#64).toNat = inp.toNat + 8 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; have := hinpG.hi; omega
  have hun : ∀ a, InExt (s.toNat - 1088, 1088) a → ¬ InExt (s.toNat - 1088 + 120, 24) a →
      ¬ InExt (s.toNat - 1088 + 1032, 8) a → ¬ InExt (s.toNat - 1088 + 1048, 8) a →
      imgM Mt3 a = imgM Mt a := by
    intro a hf h1 h2 h3
    simp only [InExt] at hf h1 h2 h3
    rw [hMt3, imgM_store_miss _ _ (by rw [hoff 1048 (by decide)]; omega),
      imgM_store_miss _ _ (by rw [hi8]; omega), hM3f a (by simp only [InExt]; omega), hMt2,
      imgM_store_miss _ _ (by rw [hoff 1032 (by decide)]; omega), hMt1,
      imgM_store_miss _ _ (by rw [hoff 136 (by decide)]; omega),
      imgM_store_miss _ _ (by rw [hoff 128 (by decide)]; omega),
      imgM_store_miss _ _ (by rw [hoff 120 (by decide)]; omega)]
  have hkeepM : ∀ o, 1008 ≤ o → o + 8 ≤ 1088 → (o + 8 ≤ 1032 ∨ 1056 ≤ o) →
      ldv .ld Mt3 (s.toNat - 1088 + o) = ldv .ld Mt (s.toNat - 1088 + o) := fun o h1 h2 h3 =>
    ldv_eqOn .ld (fun j hj => by
      simp only [widthOfM] at hj
      exact hun _ (by simp only [InExt]; omega) (by simp only [InExt]; omega)
        (by simp only [InExt]; omega) (by simp only [InExt]; omega))
  have h1048 : ldv .ld Mt3 (s.toNat - 1088 + 1048) = rv 19 := by
    rw [← hoff 1048 (by decide), hMt3]
    ix_fwd
    subst hR2; subst hR1; ix_reg; exact hcall.keep 19 (by decide)
  have h1032 : ldv .ld Mt3 (s.toNat - 1088 + 1032) = rv 21 := by
    have e1 : ldv .ld Mt3 (s.toNat - 1088 + 1032) = ldv .ld M3 (s.toNat - 1088 + 1032) := by
      rw [← hoff 1032 (by decide), hMt3]; ix_fwd
    rw [e1, ldv_eqOn .ld (Mt' := Mt2) (fun j hj => by
        simp only [widthOfM] at hj; exact hM3f _ (by simp only [InExt]; omega)),
      ← hoff 1032 (by decide), hMt2]
    ix_fwd
    subst hR1; ix_reg; exact hcall.keep 21 (by decide)
  have hdepth : imgLE (imgM Mt3) (inp.toNat + 8) 4 = dep + 1 := by
    have hv : (BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 dep + 1#64))).toNat % 2 ^ 32
        = dep + 1 := by
      rw [idx_succ, sext32_toNat_small (by unfold maxCallDepth at hdle; omega)]
      exact Nat.mod_eq_of_lt (by unfold maxCallDepth at hdle; omega)
    rw [imgLE_congr (n := 4) (img' := imgM (writeLog M3 [((inp + 8#64).toNat,
        4, BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 dep + 1#64)))]))
      (fun i hi => by
        rw [hMt3, imgM_store_miss _ _ (by rw [hoff 1048 (by decide)]; omega)]),
      hi8, imgLE_store4_hit, hv]
  have hdp : CloDp R3 Mt3 s aX sret inp ret vl rv dep := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩, h1048, h1032, ?_, hdepth⟩
    all_goals first
      | (subst hR3; subst hR2; subst hR1; ix_reg; done)
      | (subst hR3; subst hR2; subst hR1; ix_reg; first
          | exact hcall.sp | exact hcall.s0 | exact hcall.s1 | exact hcall.s2)
      | skip
    · intro x hx
      have hx' : x = 20 ∨ x = 22 ∨ x = 24 ∨ x = 25 ∨ x = 26 ∨ x = 27 := by simpa using hx
      subst hR3; subst hR2; subst hR1
      rcases hx' with rfl | rfl | rfl | rfl | rfl | rfl <;>
        (ix_reg; exact hcall.keep _ (by decide))
    · rw [hkeepM 1080 (by omega) (by omega) (by omega)]; exact hcall.ra
    · rw [hkeepM 1072 (by omega) (by omega) (by omega)]; exact hcall.sv8
    · rw [hkeepM 1064 (by omega) (by omega) (by omega)]; exact hcall.sv9
    · rw [hkeepM 1056 (by omega) (by omega) (by omega)]; exact hcall.sv18
    · rw [hkeepM 1016 (by omega) (by omega) (by omega)]; exact hcall.sv23
  iapply Hk $$ %R3 %Mt3 %vl %⟨hgt, hdp⟩ Hms

#ix_chain callCloHead_c := [callCloHead_p1, callCloHead_p2, callCloHead_p3]


/-- **The closure call's head**, for either WP: from the kind dispatch on a
closure, with its resources (`CloFactsE`) and the depth word, the runs read
`fn_expr`, `paramc` and `cl->env`, bump the depth, and leave at the
`jal env_new` (count = `paramc`, depth within the maximum), the arity error
or the depth error (`CloHeadK`). -/
theorem callCloHead {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {st : Store} {fe : Expr} {args : List Expr} {ca : Nat} {cd : ClosureData} {q e : Nat}
    {img : Nat → BitVec 8} {P : Nat → Prop} {m : Mem} {dimg : Nat → BitVec 8}
    {s aX sret inp ret w0 w1 w2 : BitVec 64} {rv R : Nat → BitVec 64} {Mt : Mem} {argc dep : Nat}
    (hcall : CallAt R Mt s aX sret inp ret rv w0 w1 w2 argc) (hargc : argc ≤ 32)
    (hk4 : w0.toNat % 2 ^ 32 = 4) (hcf : CloFactsE st ca w1.toNat cd q e img P m)
    (hinpG : RtErr.InpGeom inp) (hinpA : inp.toNat % 8 = 0)
    (hdep : imgLE dimg (inp.toNat + 8) 4 = dep) (hdle : dep ≤ maxCallDepth) (hfg : EvalFrameG s) :
    codeRes ∗ □ astEG aX.toNat (.call fe args) ∗ roImg (InExt (w1.toNat, 16)) img ∗ roOn P m ∗
      ms 0x80003254#64 R (InExt (s.toNat - 1088, 1088)) Mt ∗
      ownImg (InExt (inp.toNat + 8, 4)) dimg ∗
      CloHeadK live Wp Φ cd Mt s aX sret inp ret (BitVec.ofNat 64 e) (BitVec.ofNat 64 q) rv argc dep
    ⊢ Wp.W Φ :=
  callCloHead_c hlive Wp hcall hargc hk4 hcf hinpG hinpA hdep hdle hfg
    (callCloHead_p2b hlive Wp hcall hargc hk4 hcf hinpG hinpA hdep hdle hfg)
    (callCloHead_p2c hlive Wp hcall hargc hk4 hcf hinpG hinpA hdep hdle hfg)

end VsaIris.Interp
