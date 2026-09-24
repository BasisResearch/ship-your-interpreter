import VsaIris.Interp.Case.{ARM}T

/-!
# `{ARM}`, partial mode (family `execEval1`, lane E5)

`caseP_{ARM}`: from the Löb hypothesis `evalSpecsP`, `exec_stmt` on `{SM}`
meets its partial dispatch-point spec (`execDispP_body`). The same run as
total mode (`{ARM}_run1`); the child through the Löb hypothesis from the
176-byte frame (`ms_callEvalPF`: an abort rebuilds the frame and aborts the
arm); the tail ({TAILDOC}) returns with the derivation `ExecS.{SEM}`.
Template: `scripts/iris_arms/templates/execEval1_P.lean`.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim
open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr

theorem caseP_{ARM} {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat} {Core : IProp GF}
    {st : St} {d env : Nat} {e : Expr} :
    evalSpecsP (GF := GF) (vsaModel live) N L Room inp Core ⊢
      execDispP_body (GF := GF) (vsaModel live) N L Room inp Core st d env ({SM}) := by
  iintro #IH
  unfold execDispP_body
  iintro !> %Φ %aS %aE %aRet %s %R %Mt %ret %v8 %v9 %v18 %v19 Hpre HK
  unfold execDispPre
  icases Hpre with ⟨Hms, %hf, #Hcode, #Hast, #Hfb, Hst, Hslot, Hw⟩
  unfold astSG
  icases Hast with ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩
  obtain ⟨p, hn⟩ := {NODE} hrepr hgeo
  obtain ⟨hfg, hneed⟩ := execFrameGeom_of hf.stack
  have hoff := execSP_offF (s := s) hfg.sf (by have := hfg.hi; omega)
  have g := callGeomF (f := 176) (o := 16) hf.stack hfg.sf ({NEED} e d) (by decide)
    (by decide) (by decide)
  have g1 : (execSP s + 16#64).toNat = s.toNat - 176 + 16 := g.slot
  have hbb : e.bodiesBound perCallBudget = true := hf.bodies
  ihave #Hdv := roOwn_data hn.node.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (wpW _) (F := iprop(evalSpecsP (vsaModel live) N L Room inp Core ∗
      codeRes ∗ roOn P m ∗ frameAt env aE.toNat ∗
      stackScratch (execSP s) (execNeed ({SM}) d - 176) ∗ slot24 aRet.toNat ∗
      world N L Room inp .uncounted st d ∗
      ((∀ (st' : St) (status : Status), ⌜ExecS st d env ({SM}) st' status⌝ -∗
        execDispK (vsaModel live) N L Room inp (wpW (vsaModel live)) Φ .uncounted st' d
          ({SM}) status aRet s R ret v8 v9 v18 v19) ∧
       (iprop(abortAt Core s (execNeed ({SM}) d) ∗ slot24 aRet.toNat) -∗
          (wpW (vsaModel live)).W Φ))))
  rotate_left
  · iframe Hdv Hms IH Hcode Hro Hfb Hst Hslot Hw; iexact HK
  intro F'
  unfold execDispPC
  refine {ARM}_run1 (aC := BitVec.ofNat 64 p) hlive hfg.sf hfg.lo hfg.hi hfg.al hn.node.lo
    hn.node.hi hn.node.off hf.regs.s0 hf.regs.a6 hf.regs.a4 hf.regs.sp hn.node.kind hn.node.kindu
    hn.field hn.ne ?_
  intros
  apply swp_closeRM
  intro R0 Mt1 hR0 hMt1
  unfold F'
  iintro ⟨⟨#IH, #Hcode, #Hro, #Hfb, Hst, Hslot, Hw, HK⟩, Hms⟩
  -- the child, through the Löb hypothesis
  ihave He := evalSpecsP_at Core st d env e $$ IH
  iapply ms_callEvalPF (N := N) (L := L) (Room := Room) (inp := inp) (i := 0x{J1})
    (jalx_{J1} live (fun p hp => hlive _ (interp_code_{J1} p hp)))
    interp_code_{J1} (by decide) (slot := execSP s + 16#64)
    (aC := BitVec.ofNat 64 p) (aE := aE) (s0 := s) (sF := execSP s) (f := 176)
    (m := execNeed ({SM}) d - 176) (n0 := execNeed ({SM}) d)
    (Out := slot24 aRet.toNat)
    (Kret := iprop(∀ (st' : St) (status : Status), ⌜ExecS st d env ({SM}) st' status⌝ -∗
      execDispK (vsaModel live) N L Room inp (wpW (vsaModel live)) Φ .uncounted st' d
        ({SM}) status aRet s R ret v8 v9 v18 v19))
    (execSP_eq s).symm g.child g.fits g.below (by omega) hf.stack.le g.slotGeom hbb
  iframe He Hcode Hfb Hms Hst Hw Hslot HK
  isplitl []
  · ipureintro
    subst hR0
    refine ⟨⟨by ix_reg, by ix_reg; exact hf.regs.s1, by ix_reg, by ix_reg; exact hf.regs.s3,
      by ix_reg; exact hf.regs.sp⟩, fun b hb => ?_⟩
    simp only [VsaIris.InExt] at hb g1 ⊢; omega
  isplitl []
  · imodintro; rw [hn.toNat]; iapply astEG_of_view hn.child hn.node.geo $$ Hro
  iintro %R1 %w0 %w1 %w2 %st' %v %hE %hkeep1 #Hv1 Hms Hst Hw Hslot HK
  have hk1 : KeepRegs [20, 21, 22, 23, 24, 25, 26, 27] R (upd R1 1 (BitVec.ofNat 64 (0x{J1} + 4))) := by
    subst hR0
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_keep [hkeep1]
  have hsv1 : ExecSaved (slotWrite Mt1 (execSP s + 16#64).toNat w0 w1 w2) s ret v8 v9 v18 v19 := by
    have := hfg.lo; rw [hMt1]; ix_esaved hf.saved using hoff
  -- the tail
{TAIL}
end VsaIris.Interp
