import VsaIris.Interp.ExecArm

/-!
# `{ARM}`, total mode (family `execEval1`, lane E5)

`caseT_{ARM}`: `exec_stmt` on `{SM}` meets its dispatch-point spec
(`execDispT_body`, `SpecExecDisp.lean`), given the child's `evalSpecT_body`.
The kind dispatch and the child's staging are one run (`{ARM}_run1`, to the
`jal eval_expr` at `0x{J1}`); the child writes the frame slot `sp+16`
(`ms_callEvalT`); the tail ({TAILDOC}) is a shared exit lemma of `ExecArm.lean`.
Template: `scripts/iris_arms/templates/execEval1_T.lean`.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim

#ix_seg {ARM}_run1 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aS s aC : BitVec 64}
    (hsf : (s + 18446744073709551440#64).toNat = s.toNat - 176)
    (hs : 0x87800000 + 176 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aS.toNat) (hx2 : aS.toNat + 16 ≤ 0x100000000)
    (hx3 : aS.toNat + 16 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aS.toNat)
    (h8 : R 8 = aS) (h16 : R 16 = 8#64) (h14 : R 14 = 0x80019fb8#64)
    (h2 : R 2 = s + 18446744073709551440#64)
    (hk : ldv .lw m aS.toNat = {TAG}#64) (hku : ldv .lwu m aS.toNat = {TAG}#64)
    (hc : ldv .ld m (aS + 8#64).toNat = aC) (hc0 : aC ≠ 0#64) :
    IW live m (stmtView aS.toNat 16) (InExt (s.toNat - 176, 176)) Q 0x80004014#64 R Mt
  by rw [← upd_eq_self h16]
     ix_run hlive using [h8, h14, h2, hk, hku, hc, hc0, hsf] at 0x{J1}
{TAILSEG}
open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr

theorem caseT_{ARM} {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {st : St} {d env : Nat} {e : Expr} {st' : St} {v : Value} {n : Nat}
    (D : EvalECost st d env e st' v n)
    (he : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env e st' v n D) :
    ⊢ execDispT_body (GF := GF) (vsaModel live) N L Room inp st d env ({SM}) st' ({STATUS}) n
        (.{SEM} st d env e st' v n D) := by
  unfold execDispT_body
  iintro !> %Φ %k %aS %aE %aRet %s %R %Mt %ret %v8 %v9 %v18 %v19 Hpre HK
  unfold execDispPre
  icases Hpre with ⟨Hms, %hf, #Hcode, #Hast, #Hfb, Hst, Hslot, Hw⟩
  unfold astSG
  icases Hast with ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩
  obtain ⟨p, hn⟩ := {NODE} hrepr hgeo
  obtain ⟨hfg, hneed⟩ := execFrameGeom_of hf.stack
  have hoff := execSP_off (s := s) hfg.sf (by have := hfg.hi; omega)
  have g := callGeomF (f := 176) (o := 16) hf.stack hfg.sf ({NEED} e d) (by decide)
    (by decide) (by decide)
  have g1 : (execSP s + 16#64).toNat = s.toNat - 176 + 16 := g.slot
  have hbb : e.bodiesBound perCallBudget = true := hf.bodies
  ihave #Hdv := roOwn_data hn.node.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := iprop(codeRes ∗ roOn P m ∗ frameAt env aE.toNat ∗
      stackScratch (execSP s) (execNeed ({SM}) d - 176) ∗ slot24 aRet.toNat ∗
      world N L Room inp (.counted (k + n)) st d ∗
      execDispK (vsaModel live) N L Room inp (twpW (vsaModel live)) Φ (.counted k) st' d
        ({SM}) ({STATUS}) aRet s R ret v8 v9 v18 v19))
  rotate_left
  · iframe Hdv Hms Hcode Hro Hfb Hst Hslot Hw; iexact HK
  intro F'
  unfold execDispPC
  refine {ARM}_run1 (aC := BitVec.ofNat 64 p) hlive hfg.sf hfg.lo hfg.hi hfg.al hn.node.lo
    hn.node.hi hn.node.off hf.regs.s0 hf.regs.a6 hf.regs.a4 hf.regs.sp hn.node.kind hn.node.kindu
    hn.field hn.ne ?_
  intros
  apply swp_closeRM
  intro R0 Mt1 hR0 hMt1
  unfold F'
  iintro ⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, HK⟩, Hms⟩
  -- the child
  ihave He := he
  iapply ms_callEvalT (N := N) (L := L) (Room := Room) (inp := inp) (i := 0x{J1})
    (jalx_{J1} live (fun p hp => hlive _ (interp_code_{J1} p hp)))
    interp_code_{J1} (by decide) D (k := k) (slot := execSP s + 16#64)
    (aC := BitVec.ofNat 64 p) (aE := aE) (s := execSP s)
    (m := execNeed ({SM}) d - 176) g.child g.fits g.below g.slotGeom hbb
  iframe He Hcode Hfb Hms Hst Hw
  isplitl []
  · ipureintro
    subst hR0
    refine ⟨⟨by ix_reg, by ix_reg; exact hf.regs.s1, by ix_reg, by ix_reg; exact hf.regs.s3,
      by ix_reg; exact hf.regs.sp⟩, fun b hb => ?_⟩
    simp only [VsaIris.InExt] at hb g1 ⊢; omega
  isplitl []
  · imodintro; rw [hn.toNat]; iapply astEG_of_view hn.child hn.node.geo $$ Hro
  iintro %R1 %w0 %w1 %w2 %hkeep1 #Hv1 Hms Hst Hw
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
