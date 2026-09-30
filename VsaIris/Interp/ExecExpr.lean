import VsaIris.Interp.ExecChild
import VsaIris.Interp.SymInterp

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim

#ix_seg ExecExpr_run1 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aS s aC : BitVec 64}
    (hsf : (s + 18446744073709551440#64).toNat = s.toNat - 176)
    (hs : 0x87800000 + 176 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aS.toNat) (hx2 : aS.toNat + 16 ≤ 0x100000000)
    (hx3 : aS.toNat + 16 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aS.toNat)
    (h8 : R 8 = aS) (h16 : R 16 = 8#64) (h14 : R 14 = 0x80019fb8#64)
    (h2 : R 2 = s + 18446744073709551440#64)
    (hk : ldv .lw m aS.toNat = 0#64) (hku : ldv .lwu m aS.toNat = 0#64)
    (hc : ldv .ld m (aS + 8#64).toNat = aC) (hc0 : aC ≠ 0#64) :
    IW live m (stmtView aS.toNat 16) (InExt (s.toNat - 176, 176)) Q 0x80004014#64 R Mt
  by rw [← upd_eq_self h16]
     sym_run hlive using [h8, h14, h2, hk, hku, hc, hc0, hsf] at 0x80004180

#ix_seg ExecExpr_run2 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {s : BitVec 64} :
    IW live m [] (InExt (s.toNat - 176, 176)) Q 0x80004184#64 R Mt
  by sym_run hlive at 0x8000409c

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

theorem exprCore (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs} {L : DlLayout}
    {Room : RoomPred} {inp : Nat} {st : St} {d env : Nat} {e : Expr} :
    ExecChildCore (GF := GF) (live := live) N L Room inp st d env (.expr e) e (fun _ => .normal) := by
  intro Wp Φ Hyp ρin ρout Kin aS aE aRet s R Mt ret v8 v9 v18 v19 hcall
  unfold execDispPre
  iintro ⟨#Hyp, ⟨Hms, %hf, #Hcode, #Hast, #Hfb, Hst, Hslot, Hw⟩, HK⟩
  unfold astSG
  icases Hast with ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩
  obtain ⟨p, hn⟩ := exprNode_of hrepr hgeo
  obtain ⟨hfg, hneed⟩ := execFrameGeom_of hf.stack
  have hoff := execSP_offF (s := s) hfg.sf (by have := hfg.hi; omega)
  have g := callGeomF (f := 176) (o := 16) hf.stack hfg.sf (execNeed_expr e d) (by decide)
    (by decide) (by decide)
  have g1 : (execSP s + 16#64).toNat = s.toNat - 176 + 16 := g.slot
  have hbb : e.bodiesBound perCallBudget = true := hf.bodies
  ihave #Hdv := roOwn_data hn.node.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF Wp (F := iprop(□ Hyp ∗ codeRes ∗ roOn P m ∗ frameAt env aE.toNat ∗
      stackScratch (execSP s) (execNeed (.expr e) d - 176) ∗ slot24 aRet.toNat ∗
      world N L Room inp ρin st d ∗
      Kin))
  rotate_left
  · iframe Hdv Hms Hyp Hcode Hro Hfb Hst Hslot Hw HK
  intro F'
  unfold execDispPC
  refine ExecExpr_run1 (aC := BitVec.ofNat 64 p) hlive hfg.sf hfg.lo hfg.hi hfg.al hn.node.lo
    hn.node.hi hn.node.off hf.regs.s0 hf.regs.a6 hf.regs.a4 hf.regs.sp hn.node.kind hn.node.kindu
    hn.field hn.ne ?_
  intros
  apply swp_closeRM
  intro R0 Mt1 hR0 hMt1
  unfold F'
  iintro ⟨⟨#Hyp, #Hcode, #Hro, #Hfb, Hst, Hslot, Hw, HK⟩, Hms⟩

  iapply hcall 0x80004180 _ (jalx_80004180 live (fun p hp => hlive _ ((interp_code (by decide)) p hp)))
    (interp_code (by decide)) (by decide) (slot := execSP s + 16#64) (aC := BitVec.ofNat 64 p)
    (aE := aE) (sF := execSP s) (f := 176) (m := execNeed (.expr e) d - 176)
    (execSP_eq s).symm g.child g.fits g.below (by omega) hf.stack.le g.slotGeom hbb
  iframe Hyp Hcode Hfb Hms Hst Hw Hslot HK
  isplitl []
  · ipureintro
    subst hR0
    refine ⟨⟨by ix_reg, by ix_reg; exact hf.regs.s1, by ix_reg, by ix_reg; exact hf.regs.s3,
      by ix_reg; exact hf.regs.sp⟩, fun b hb => ?_⟩
    simp only [VsaIris.InExt] at hb g1 ⊢; omega
  isplitl []
  · imodintro; rw [hn.toNat]; iapply astEG_of_view hn.child hn.node.geo $$ Hro
  iintro %R1 %w0 %w1 %w2 %st' %v %hkeep1 #Hv1 Hms Hst Hw Hslot HK
  have hk1 : KeepRegs [20, 21, 22, 23, 24, 25, 26, 27] R (upd R1 1 (BitVec.ofNat 64 (0x80004180 + 4))) := by
    subst hR0
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_keep [hkeep1]
  have hsv1 : ExecSaved (slotWrite Mt1 (execSP s + 16#64).toNat w0 w1 w2) s ret v8 v9 v18 v19 := by
    have := hfg.lo; rw [hMt1]; ix_esaved hf.saved using hoff

  iapply wp_swpF Wp (text := interpText ++ dataOf ∅ [])
    (F := iprop(codeRes ∗ stackScratch (execSP s) (execNeed (.expr e) d - 176) ∗ slot24 aRet.toNat ∗
      world N L Room inp ρout st' d ∗
      execDispK (vsaModel live) N L Room inp Wp Φ ρout st' d
        (.expr e) (.normal) aRet s R ret v8 v9 v18 v19))
  rotate_left
  · iframe Hcode Hms Hst Hslot Hw HK
    iapply codeRes_text $$ Hcode
  intro F'
  refine ExecExpr_run2 (m := ∅) (s := s) hlive ?_
  intros
  apply swp_closeRM
  intro R2 Mt2 hR2 hMt2
  have hepi := wp_execEpi (N := N) (L := L) (Room := Room) (inp := inp) hlive Wp
    (Φ := Φ) (ρ := ρout) (st' := st') (d := d) (sm := .expr e) (status := .normal)
    (aRet := aRet) (s := s) (ret := ret) (v8 := v8) (v9 := v9) (v18 := v18) (v19 := v19) (R0 := R)
    (R := R2) (Mt := Mt2) hf.stack hf.ral
    (by subst hR2 hR0; ix_reg; rw [keep_reg hkeep1 (by decide)]; ix_reg; exact hf.regs.sp)
    (by subst hR2; ix_reg; rfl)
    (by rw [hMt2]; exact hsv1)
    (by subst hR2; repeat (first | exact hk1 | refine KeepRegs.upd ?_ (by decide) _))
  simp only [statusRet] at hepi
  unfold F'
  iintro ⟨⟨#Hcode, Hst, Hslot, Hw, HK⟩, Hms⟩
  iapply hepi
  iframe Hcode Hms Hst Hslot Hw HK


theorem exprT (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs} {L : DlLayout}
    {Room : RoomPred} {inp : Nat} {st : St} {d env : Nat} {e : Expr} {st' : St} {v : Value}
    {n : Nat} (D : EvalECost st d env e st' v n)
    (he : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env e st' v n D) :
    ⊢ execDispT_body (GF := GF) (vsaModel live) N L Room inp st d env (.expr e) st' .normal n
        (.expr st d env e st' v n D) :=
  execChildT_of (stat := fun _ => .normal) _ D he (exprCore hlive)

theorem exprP (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs} {L : DlLayout}
    {Room : RoomPred} {inp : Nat} {Core : IProp GF} {st : St} {d env : Nat} {e : Expr} :
    evalSpecsP (GF := GF) (vsaModel live) N L Room inp Core ⊢
      execDispP_body (GF := GF) (vsaModel live) N L Room inp Core st d env (.expr e) :=
  execChildP_of (stat := fun _ => .normal) (fun st' v h => ExecS.expr st d env e st' v h)
    (exprCore hlive)

end

end VsaIris.Interp
