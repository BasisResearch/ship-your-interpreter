import VsaIris.Interp.Case.{ARM}T

/-!
# `{ARM}`, partial mode (family `execWhile`, lane E5)

`caseP_{ARM}`: from the Löb hypotheses and E6's `whileP_body` (proved by
`whileP_all`), `exec_stmt` on `.whileStmt c b` meets its partial
dispatch-point spec: the same dispatch run, the loop with SOME outcome and its
`ExecS` derivation (the entry-shaped Löb hypothesis for the body from
`execSpecsP_of_disps`), the exit `wp_loopExit`; the loop's abort rejoins the
frame (`execFrame_join`).
Template: `scripts/iris_arms/templates/execWhile_P.lean`.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim
open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr

theorem caseP_{ARM} {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
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
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (wpW _) (F := iprop(evalSpecsP (vsaModel live) N L Room inp Core ∗
      execSpecsP (vsaModel live) N L Room inp Core ∗ codeRes ∗ roOn P m ∗ frameAt env aE.toNat ∗
      stackScratch (execSP s) (execNeed (.whileStmt c b) d - 176) ∗ slot24 aRet.toNat ∗
      world N L Room inp .uncounted st d ∗
      ((∀ (st' : St) (status : Status), ⌜ExecS st d env (.whileStmt c b) st' status⌝ -∗
        execDispK (vsaModel live) N L Room inp (wpW (vsaModel live)) Φ .uncounted st' d
          (.whileStmt c b) status aRet s R ret v8 v9 v18 v19) ∧
       (iprop(abortAt Core s (execNeed (.whileStmt c b) d) ∗ slot24 aRet.toNat) -∗
          (wpW (vsaModel live)).W Φ))))
  rotate_left
  · iframe Hdv Hms IHe IHs Hcode Hro Hfb Hst Hslot Hw HK
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
    iapply execFrame_join hf.stack.le hneed $$ [Hst HS]
    iframe Hst HS

end VsaIris.Interp
