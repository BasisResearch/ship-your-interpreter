import VsaIris.Interp.Case.ExecWhileT

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim
open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr

theorem caseP_ExecWhile {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat} {Core : IProp GF}
    {st : St} {d env : Nat} {c : Expr} {b : Stmt}
    (hw : whileP_body (GF := GF) live N L Room inp Core d env c b) :
    evalSpecsP (GF := GF) (vsaModel live) N L Room inp Core ∗
      execDispsP (vsaModel live) N L Room inp Core ⊢
      execDispP_body (GF := GF) (vsaModel live) N L Room inp Core st d env (.whileStmt c b) := by
  iintro ⟨#IHe, #IHx⟩
  ihave #IHs := execSpecsP_of_disps hlive Core $$ IHx
  unfold execDispP_body
  iintro !> %Φ %aS %aE %aRet %s %R %Mt %ret %v8 %v9 %v18 %v19 Hpre HK
  unfold execDispPre
  icases Hpre with ⟨Hms, %hf, #Hcode, #Hast, #Hfb, Hst, Hslot, Hw⟩
  unfold astSG
  icases Hast with ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩
  have hn := whileNode_of hrepr hgeo
  obtain ⟨hfg, hneed⟩ := execFrameGeom_of hf.stack
  ihave #Hdv := roOwn_data hn.view $$ [$]
  iapply wp_swpF (wpW _)
  rotate_left
  · icombine IHe IHs Hcode Hro Hfb Hst Hslot Hw HK as HX; isplitl []; iexact Hdv; iframe HX Hms
  intro F'
  unfold execDispPC
  refine WhileArm_run (s := s) hlive hn.lo hn.hi hn.off hf.regs.s0 hf.regs.a6 hf.regs.a4 hn.kind
    hn.kindu ?_
  intros
  apply swp_closeRM
  intro R1 Mt1 hR1 hMt1
  have hh : StmtHead R1 s aS (BitVec.ofNat 64 inp) aRet aE := by
    subst hR1; exact stmtHead_of_disp hf.regs (by ix_reg) (by ix_reg) (by ix_reg) (by ix_reg)
      (by ix_reg)
  have hk1 : KeepRegs [20, 21, 22, 23, 24, 25, 26, 27] R R1 := by
    subst hR1; repeat (first | exact fun _ _ => rfl | refine KeepRegs.upd ?_ (by decide) _)
  unfold F'
  iintro ⟨⟨#IHe, #IHs, #Hcode, #Hro, #Hfb, Hst, Hslot, Hw, HK⟩, Hms⟩
  iapply hw Φ st aS aE aRet s R1 Mt1 _ hh hfg (hf.stack.lower hneed hfg.sf)
    (whileFits_of hf.bodies) hf.slot
  iframe Hms Hcode Hfb Hst Hslot Hw IHe IHs
  isplitl []
  · imodintro; unfold astSG; iexists P, m; iframe Hro; ipureintro; exact ⟨hrepr, hgeo⟩
  isplit
  · iintro %R' %Mt' %st' %status %hE %⟨hk, h10, hu⟩ Hms Hst Hret Hw
    ihave HK := and_elim_l $$ HK
    ihave HK := HK $$ %st' %status %hE
    iapply wp_loopExit hlive (wpW _) hf.stack hf.ral hh.sp hk1 (hMt1 ▸ hf.saved) hk h10 hu
    iframe Hcode Hms Hst Hret Hw HK
  · iintro ⟨HA, Hslot, HS⟩
    ihave HK := and_elim_r $$ HK
    iapply HK
    iframe Hslot
    unfold abortAt
    icases HA with ⟨HC, Hst⟩
    iframe HC
    iapply execFrame_join hf.stack.le hneed $$ [$]

end VsaIris.Interp
