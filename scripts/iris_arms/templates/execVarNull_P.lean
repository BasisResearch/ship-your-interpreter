import VsaIris.Interp.Case.{ARM}T

/-!
# `{ARM}`, partial mode (family `execVarNull`, lane E5)

`caseP_{ARM}`: `exec_stmt` on `.varDecl x none` meets its partial
dispatch-point spec: the same runs, `value_null`, then `varTailP`
(`env_define` uncounted; out of memory the arm aborts through `CoreOK`),
returning with `ExecS.varNull`. Error premises as E2's.
Template: `scripts/iris_arms/templates/execVarNull_P.lean`.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim
open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr VsaIris.VsaHeap

theorem caseP_{ARM} {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs} {inp : Nat}
    {Core : IProp GF} (HN : Newlib.NewlibHoles) (hcl : Newlib.CodeLive live)
    (hcore : CoreOK N vsaLayoutP vsaRoomB inp Core)
    {st : St} {d env : Nat} {x : String}
    (hvn : ⊢ ∀ p, valueNullSpec (GF := GF) (vsaModel live) N (wpW (vsaModel live)) p)
    (hed : ⊢ envDefineSpec (GF := GF) (wpW (vsaModel live)) N) :
    errCtx inp ⊢
      execDispP_body (GF := GF) (vsaModel live) N vsaLayoutP vsaRoomB inp Core st d env
        (.varDecl x none) := by
  iintro #Herr
  ihave #Himg := errCtx_img inp $$ Herr
  unfold execDispP_body
  iintro !> %Φ %aS %aE %aRet %s %R %Mt %ret %v8 %v9 %v18 %v19 Hpre HK
  unfold execDispPre
  icases Hpre with ⟨Hms, %hf, #Hcode, #Hast, #Hfb, Hst, Hslot, Hw⟩
  unfold astSG
  icases Hast with ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩
  obtain ⟨pn, pi, hn⟩ := varNode_of hrepr hgeo
  obtain ⟨hfg, hneed⟩ := execFrameGeom_of hf.stack
  have hoff := execSP_offF (s := s) hfg.sf (by have := hfg.hi; omega)
  have g1 : (execSP s + 104#64).toNat = s.toNat - 176 + 104 := hoff 104 (by decide)
  have hslg : SlotGeom (execSP s + 104#64) := by
    have := hfg.lo; have := hfg.hi; have := hfg.al
    refine ⟨?_, ?_, ?_⟩ <;> rw [g1] <;> (try unfold Vsa.Sim.tohostAddr) <;> omega
  ihave #Hdv := roOwn_data hn.node.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (wpW _) (F := iprop(Newlib.binImg ∗ codeRes ∗ roOn P m ∗ frameAt env aE.toNat ∗
      stackScratch (execSP s) (execNeed (.varDecl x none) d - 176) ∗ slot24 aRet.toNat ∗
      world N vsaLayoutP vsaRoomB inp .uncounted st d ∗
      ((∀ (st' : St) (status : Status), ⌜ExecS st d env (.varDecl x none) st' status⌝ -∗
        execDispK (vsaModel live) N vsaLayoutP vsaRoomB inp (wpW (vsaModel live)) Φ .uncounted st' d
          (.varDecl x none) status aRet s R ret v8 v9 v18 v19) ∧
       (iprop(abortAt Core s (execNeed (.varDecl x none) d) ∗ slot24 aRet.toNat) -∗
          (wpW (vsaModel live)).W Φ))))
  rotate_left
  · iframe Hdv Hms Himg Hcode Hro Hfb Hst Hslot Hw HK
  intro F'
  unfold execDispPC
  refine VarArm_run1N hlive hfg.sf hfg.lo hfg.hi hfg.al hn.node.lo hn.node.hi hn.node.off
    hf.regs.s0 hf.regs.a6 hf.regs.a4 hf.regs.sp hn.node.kind hn.node.kindu
    (by rw [hn.init, hn.initNone rfl]) ?_
  intros
  apply swp_closeRM
  intro R0 Mt1 hR0 hMt1
  unfold F'
  iintro ⟨⟨#Himg, #Hcode, #Hro, #Hfb, Hst, Hslot, Hw, HK⟩, Hms⟩
  -- value_null into the frame slot
  ihave Hvn := hvn $$ %(execSP s + 104#64)
  unfold valueNullSpec
  iapply ms_callHelperSlot (wpW _) (i := 0x80004300)
    (jalx_80004300 live (fun p hp => hlive _ (interp_code_80004300 p hp)))
    interp_code_80004300 (by decide) (a := execSP s + 104#64) (R := R0) (Mt := Mt1)
    (S := InExt (s.toNat - 176, 176)) (v := .null)
    (fun b hb => by simp only [VsaIris.InExt] at hb ⊢; rw [g1] at hb; omega) hslg
  iframe Hvn Hcode Hms
  isplitl []
  · ipureintro; subst hR0; ix_reg
  iintro %R1 %w0 %w1 %w2 %hkeep1 #Hv1 Hms
  -- the jump to the shared tail
  iapply wp_swpF (wpW _) (text := interpText ++ dataOf ∅ [])
    (F := iprop(Newlib.binImg ∗ codeRes ∗ roOn P m ∗ frameAt env aE.toNat ∗ valOf N .null w0 w1 w2 ∗
      stackScratch (execSP s) (execNeed (.varDecl x none) d - 176) ∗ slot24 aRet.toNat ∗
      world N vsaLayoutP vsaRoomB inp .uncounted st d ∗
      ((∀ (st' : St) (status : Status), ⌜ExecS st d env (.varDecl x none) st' status⌝ -∗
        execDispK (vsaModel live) N vsaLayoutP vsaRoomB inp (wpW (vsaModel live)) Φ .uncounted st' d
          (.varDecl x none) status aRet s R ret v8 v9 v18 v19) ∧
       (iprop(abortAt Core s (execNeed (.varDecl x none) d) ∗ slot24 aRet.toNat) -∗
          (wpW (vsaModel live)).W Φ))))
  rotate_left
  · iframe Hms Himg Hcode Hro Hfb Hv1 Hst Hslot Hw HK
    iapply codeRes_text $$ Hcode
  intro F'
  refine VarArm_runJ (m := ∅) (s := s) hlive ?_
  intros
  apply swp_closeRM
  intro R2 Mt2 hR2 hMt2
  have hk1 : KeepRegs calleeSaved R R2 := by
    subst hR2 hR0
    intro y hy
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (ix_reg; rw [keep_helper hkeep1 (by decide) (by decide)]; ix_reg)
  have hsub : ∀ y ∈ [20, 21, 22, 23, 24, 25, 26, 27], y ∈ calleeSaved := by decide
  unfold F'
  iintro ⟨⟨#Himg, #Hcode, #Hro, #Hfb, #Hv1, Hst, Hslot, Hw, HK⟩, Hms⟩
  iapply varTailP hlive HN hcl hcore (N := N) (inp := inp) (st := st) (env := env) (v := .null)
    (aS := aS) (aE := aE) (aRet := aRet) (s := s) (ret := ret) (v8 := v8) (v9 := v9) (v18 := v18)
    (v19 := v19) (R0 := R) (R := R2) (Mt := Mt2) (w0 := w0) (w1 := w1) (w2 := w2)
    hf.stack hf.ral hn hgeo ((hk1 2 (by decide)).trans hf.regs.sp)
    ((hk1 8 (by decide)).trans hf.regs.s0) ((hk1 19 (by decide)).trans hf.regs.s3)
    (fun y hy => hk1 y (hsub y hy))
    (by have := hfg.lo; rw [hMt2, hMt1]; ix_esaved hf.saved using hoff)
    (by rw [hMt2, ← g1]; try ix_fwd)
    (by rw [hMt2, show s.toNat - 176 + 112 = (execSP s + 104#64).toNat + 8 by omega]; try ix_fwd)
    (by rw [hMt2, show s.toNat - 176 + 120 = (execSP s + 104#64).toNat + 16 by omega]; try ix_fwd)
  ihave Hed := hed
  iframe Hed Hcode Himg Hro Hfb Hv1 Hms Hst Hslot Hw
  isplit
  · ihave HK := and_elim_l $$ HK
    iapply HK $$ %⟨st.store.define env x .null, st.out⟩ %Status.normal %(ExecS.varNull st d env x)
  · ihave HK := and_elim_r $$ HK
    iexact HK

end VsaIris.Interp
