import VsaIris.Interp.Case.{ARM}T
import VsaIris.Interp.ExecOom

/-!
# `{ARM}`, partial mode (family `execFor`, lane E5)

`caseP_{ARM}`: from the Löb hypotheses and E6's partial motives
(`execInitP_body`, `forLoopP_body`: `execInitP_all`, `forLoopP_all`),
`exec_stmt` on `.forStmt init cnd step b` meets its partial dispatch-point
spec: the dispatch, `env_new` uncounted (`ms_callEnvNewP`; out of memory the
arm aborts through `CoreOK`), the init, the loop (either may abort: the frame
rejoins), the exit `wp_loopExit` with `ExecS.forStart`.
Template: `scripts/iris_arms/templates/execFor_P.lean`.
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
    (hen : ⊢ envNewSpec (GF := GF) (wpW (vsaModel live)) N)
    {st : St} {d env : Nat} {init : Option Stmt} {cnd step : Option Expr} {b : Stmt}
    (hinit : execInitP_body (GF := GF) live N vsaLayoutP vsaRoomB inp Core d st.store.frames.size init)
    (hloop : forLoopP_body (GF := GF) live N vsaLayoutP vsaRoomB inp Core d st.store.frames.size cnd
      step b) :
    errCtx inp ∗ evalSpecsP (GF := GF) (vsaModel live) N vsaLayoutP vsaRoomB inp Core ∗
      execDispsP (vsaModel live) N vsaLayoutP vsaRoomB inp Core ⊢
      execDispP_body (GF := GF) (vsaModel live) N vsaLayoutP vsaRoomB inp Core st d env
        (.forStmt init cnd step b) := by
  iintro ⟨#Herr, #IHe, #IHx⟩
  ihave #IHs := execSpecsP_of_disps hlive Core $$ IHx
  ihave #Himg := errCtx_img inp $$ Herr
  unfold execDispP_body
  iintro !> %Φ %aS %aE %aRet %s %R %Mt %ret %v8 %v9 %v18 %v19 Hpre HK
  unfold execDispPre
  icases Hpre with ⟨Hms, %hf, #Hcode, #Hast, #Hfb, Hst, Hslot, Hw⟩
  unfold astSG
  icases Hast with ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩
  have hn := forNode_of hrepr hgeo
  obtain ⟨hfits, hifits⟩ := forFits_of (d := d) hf.bodies
  obtain ⟨hfg, hneed⟩ := execFrameGeom_of hf.stack
  have hbig : envNewNeed ≤ execNeed (.forStmt init cnd step b) d - 176 := by
    have := Stmt.stackNeed_ge (.forStmt init cnd step b)
    unfold execNeed stackBudget evalFrame envNewNeed allocHeadroom
    unfold execFrame at this; omega
  have hle' : execNeed (.forStmt init cnd step b) d - 176 ≤ (execSP s).toNat := by
    rw [hfg.sf]; have := hf.stack.le; omega
  have halloc : st.store.allocFrame (some env) =
      ((st.store.allocFrame (some env)).1, st.store.frames.size) := rfl
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (wpW _) (F := iprop(evalSpecsP (vsaModel live) N vsaLayoutP vsaRoomB inp Core ∗
      execSpecsP (vsaModel live) N vsaLayoutP vsaRoomB inp Core ∗
      Newlib.binImg ∗ codeRes ∗ roOn P m ∗ frameAt env aE.toNat ∗
      stackScratch (execSP s) (execNeed (.forStmt init cnd step b) d - 176) ∗ slot24 aRet.toNat ∗
      world N vsaLayoutP vsaRoomB inp .uncounted st d ∗
      ((∀ (st' : St) (status : Status), ⌜ExecS st d env (.forStmt init cnd step b) st' status⌝ -∗
        execDispK (vsaModel live) N vsaLayoutP vsaRoomB inp (wpW (vsaModel live)) Φ .uncounted st' d
          (.forStmt init cnd step b) status aRet s R ret v8 v9 v18 v19) ∧
       (iprop(abortAt Core s (execNeed (.forStmt init cnd step b) d) ∗ slot24 aRet.toNat) -∗
          (wpW (vsaModel live)).W Φ))))
  rotate_left
  · iframe Hdv Hms IHe IHs Himg Hcode Hro Hfb Hst Hslot Hw HK
  intro F'
  unfold execDispPC
  refine ForArm_run (s := s) hlive hn.lo hn.hi hn.off hf.regs.s0 hf.regs.a6 hf.regs.a4 hn.kind
    hn.kindu ?_
  intros
  apply swp_closeRM
  intro R1 Mt1 hR1 hMt1
  unfold F'
  iintro ⟨⟨#IHe, #IHs, #Himg, #Hcode, #Hro, #Hfb, Hst, Hslot, Hw, HK⟩, Hms⟩
  -- env_new, uncounted: the loop scope, or out of memory
  have h12 : R1 2 = execSP s := by subst hR1; ix_reg; exact hf.regs.sp
  have h110 : R1 10 = aE := by subst hR1; ix_reg; exact hf.regs.s3
  have eSt : stackScratch (GF := GF) (execSP s) (execNeed (.forStmt init cnd step b) d - 176) ⊢
      stackScratch (R1 2) (execNeed (.forStmt init cnd step b) d - 176) := by rw [h12]
  ihave Hst := eSt $$ Hst
  ihave Hen := hen
  have hsp : EnvSp (R1 2) envNewNeed :=
    ⟨by rw [h12, hfg.sf]; have := hfg.lo; unfold htifLo envNewNeed allocHeadroom; omega,
      by rw [h12, hfg.sf]; have := hfg.hi; omega, by rw [h12, hfg.sf]; have := hfg.al; omega⟩
  iapply ms_callEnvNewP (N := N) HN hcl (i := 0x80004238)
    (jalx_80004238 live (fun p hp => hlive _ (interp_code_80004238 p hp)))
    interp_code_80004238 (by decide) (st := st) (d := d) (env := env) (R := R1)
    (n := execNeed (.forStmt init cnd step b) d - 176) hsp hbig (by rw [h12]; exact hle')
    (by rw [h12, hfg.sf]; have := hf.stack.lo; simp only [Vsa.Sim.LayoutInstance.stackSL] at this;
        unfold Vsa.Sim.tohostAddr; omega)
    (by rw [h12, hfg.sf]; have := Stmt.stackNeed_ge (.forStmt init cnd step b); have := hf.stack.le
        unfold execNeed stackBudget evalFrame Newlib.fwriteNeed at *; unfold execFrame at *; omega)
    (by rw [h12, hfg.sf]; have := hfg.hi; omega)
  iframe Hen Hcode Himg Hms Hst Hw
  isplitl []
  · imodintro; rw [h110]; iexact Hfb
  isplit
  rotate_left
  · -- out of memory: the arm aborts
    iintro ⟨HA, HS⟩
    ihave HK := and_elim_r $$ HK
    iapply HK
    iframe Hslot
    unfold abortRes
    ihave ⟨HC, Hst⟩ := abortAt_elim _ _ _ $$ HA
    ihave HC := hcore (R1 2) (execNeed (.forStmt init cnd step b) d - 176) (by rw [h12]; exact hle')
      (by rw [h12, hfg.sf]; have := hf.stack.lo; simp only [Vsa.Sim.LayoutInstance.stackSL] at this; omega)
      (by rw [h12, hfg.sf]; have := hfg.hi; omega) $$ HC
    iapply abortAt_intro
    iframe HC
    rw [h12]
    iapply execFrame_join hf.stack.le hneed $$ [Hst HS]
    iframe Hst HS
  iintro %R2 %hk2 Hst Hw #Hnew Hms
  have eSt' : stackScratch (GF := GF) (R1 2) (execNeed (.forStmt init cnd step b) d - 176) ⊢
      stackScratch (execSP s) (execNeed (.forStmt init cnd step b) d - 176) := by rw [h12]
  ihave Hst := eSt' $$ Hst
  have hk2' : KeepRegs [20, 21, 22, 23, 24, 25, 26, 27] R (upd R2 1 (BitVec.ofNat 64 (0x80004238 + 4))) := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
    subst hR1
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (ix_reg; rw [hk2 _ (by decide) (by decide)]; ix_reg)
  have hih : InitHead (upd R2 1 (BitVec.ofNat 64 (0x80004238 + 4))) s aS (BitVec.ofNat 64 inp) aRet
      (R2 10) := by
    refine ⟨?_, ?_, ?_, ?_, by ix_reg⟩ <;> (ix_reg; rw [hk2 _ (by decide) (by decide)]; subst hR1; ix_reg)
    · exact hf.regs.sp
    · exact hf.regs.s0
    · exact hf.regs.s1
    · exact hf.regs.s2
  have hsub : ∀ x ∈ [20, 21, 22, 23, 24, 25, 26, 27], x ∈ initKeep := by decide
  have hsub' : ∀ x ∈ [20, 21, 22, 23, 24, 25, 26, 27], x ∈ calleeSaved := by decide
  -- the init, then the loop (each may abort: the frame rejoins)
  iapply hinit Φ ⟨(st.store.allocFrame (some env)).1, st.out⟩ cnd step b aS (R2 10) aRet s _ Mt1 _
    hih hfg (hf.stack.lower hneed hfg.sf) hifits hf.slot
  iframe Hms Hcode Hnew Hst Hslot Hw IHs
  isplitl []
  · imodintro; unfold astSG; iexists P, m; iframe Hro; ipureintro; exact ⟨hrepr, hgeo⟩
  isplit
  rotate_left
  · iintro ⟨HA, Hslot, HS⟩
    ihave HK := and_elim_r $$ HK
    iapply HK
    iframe Hslot
    unfold abortAt
    icases HA with ⟨HC, Hst⟩
    iframe HC
    iapply execFrame_join hf.stack.le hneed $$ [Hst HS]
    iframe Hst HS
  iintro %R3 %st' %hEi %⟨hk3, h319⟩ Hms Hst Hslot Hw
  have hh : StmtHead R3 s aS (BitVec.ofNat 64 inp) aRet (R2 10) :=
    ⟨(hk3 2 (by decide)).trans hih.sp, (hk3 8 (by decide)).trans hih.s0,
      (hk3 9 (by decide)).trans hih.s1, (hk3 18 (by decide)).trans hih.s2, h319⟩
  have hk3' : KeepRegs [20, 21, 22, 23, 24, 25, 26, 27] R R3 :=
    fun x hx => (hk3 x (hsub x hx)).trans (hk2' x hx)
  iapply hloop Φ st' init aS (R2 10) aRet s R3 Mt1 _ hh hfg (hf.stack.lower hneed hfg.sf) hfits hf.slot
  iframe Hms Hcode Hnew Hst Hslot Hw IHe IHs
  isplitl []
  · imodintro; unfold astSG; iexists P, m; iframe Hro; ipureintro; exact ⟨hrepr, hgeo⟩
  isplit
  · iintro %R4 %Mt4 %st'' %status %hEl %⟨hk4, h10, hu⟩ Hms Hst Hret Hw
    ihave HK := and_elim_l $$ HK
    ihave HK := HK $$ %st'' %status
      %(ExecS.forStart st d env init cnd step b _ _ st' st'' status halloc hEi hEl)
    iapply wp_loopExit hlive (wpW _) hf.stack hf.ral hh.sp hk3' (hMt1 ▸ hf.saved) hk4 h10 hu
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
