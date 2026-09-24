import VsaIris.Interp.ExecArm

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
    (hc : ldv .ld m (aS + 8#64).toNat = aC) :
    IW live m (stmtView aS.toNat 16) (InExt (s.toNat - 176, 176)) Q 0x80004014#64 R Mt
  by ix_run hlive using [h8, h16, h14, h2, hk, hku, hc, hsf] at 0x80004180

#ix_seg ExecExpr_run2 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aS s ret v8 v9 v18 v19 : BitVec 64}
    (hsf : (s + 18446744073709551440#64).toNat = s.toNat - 176)
    (hs : 0x87800000 + 176 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hal : ret.toNat % 4 = 0)
    (h2 : R 2 = s + 18446744073709551440#64)
    (hRA : ldv .ld Mt (s + 18446744073709551440#64 + 168#64).toNat = ret)
    (hS0 : ldv .ld Mt (s + 18446744073709551440#64 + 160#64).toNat = v8)
    (hS1 : ldv .ld Mt (s + 18446744073709551440#64 + 152#64).toNat = v9)
    (hS2 : ldv .ld Mt (s + 18446744073709551440#64 + 144#64).toNat = v18)
    (hS3 : ldv .ld Mt (s + 18446744073709551440#64 + 136#64).toNat = v19) :
    IW live m (stmtView aS.toNat 16) (InExt (s.toNat - 176, 176)) Q 0x80004184#64 R Mt
  by ix_run hlive using [h2, hRA, hS0, hS1, hS2, hS3, hsf, hal]

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr

theorem caseT_ExecExpr {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {st : St} {d env : Nat} {e : Expr} {st' : St} {v : Value} {n : Nat}
    (D : EvalECost st d env e st' v n)
    (he : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env e st' v n D) :
    ⊢ execDispT_body (GF := GF) (vsaModel live) N L Room inp st d env (.expr e) st' .normal n
        (.expr st d env e st' v n D) := by
  unfold execDispT_body
  iintro !> %Φ %k %aS %aE %aRet %s %R %Mt %ret %v8 %v9 %v18 %v19 Hpre HK
  unfold execDispPre
  icases Hpre with ⟨Hms, %hf, #Hcode, #Hast, #Hfb, Hst, Hslot, Hw⟩
  unfold astSG
  icases Hast with ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩
  obtain ⟨p, hn, hp, hpe, hpl⟩ : ∃ p, StmtNode m P aS 0 16 ∧
      ldv .ld m (aS + 8#64).toNat = BitVec.ofNat 64 p ∧ ExprReprWithin m P p e ∧ p < 2 ^ 64 := by
    cases hrepr with
    | expr h0 c0 hr cr hx =>
      have hn := stmtNode_of (w := 16) hgeo h0 c0 (by decide) (Or.inr (by decide))
        (fun j h1 h2 => field_mid hr cr h1 (by omega))
      exact ⟨_, hn, field64 hr (by have := hn.hi; omega), hx, readLE_lt hr⟩
  have hpt : (BitVec.ofNat 64 p).toNat = p := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpl]
  obtain ⟨hfg, hneed⟩ := execFrameGeom_of hf.stack
  have hoff := execSP_off (s := s) hfg.sf (by have := hfg.hi; omega)
  have g := callGeomF (f := 176) (o := 16) hf.stack hfg.sf (execNeed_expr e d) (by decide)
    (by decide) (by decide)
  have hbb : e.bodiesBound perCallBudget = true := hf.bodies
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := iprop(codeRes ∗ roOn P m ∗ frameAt env aE.toNat ∗
      stackScratch (execSP s) (execNeed (.expr e) d - 176) ∗ slot24 aRet.toNat ∗
      world N L Room inp (.counted (k + n)) st d ∗
      execDispK (vsaModel live) N L Room inp (twpW (vsaModel live)) Φ (.counted k) st' d (.expr e)
        .normal aRet s R ret v8 v9 v18 v19))
  rotate_left
  · iframe Hdv Hms Hcode Hro Hfb Hst Hslot Hw; iexact HK
  intro F'
  unfold execDispPC
  refine ExecExpr_run1 (aC := BitVec.ofNat 64 p) hlive hfg.sf hfg.lo hfg.hi hfg.al hn.lo hn.hi
    hn.off hf.regs.s0 hf.regs.a6 hf.regs.a4 hf.regs.sp hn.kind hn.kindu hp ?_
  intros
  apply swp_closeM
  intro Mt1 hMt1
  unfold F'
  iintro ⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, HK⟩, Hms⟩
  -- the child
  ihave He := he
  iapply ms_callEvalT (N := N) (L := L) (Room := Room) (inp := inp) (i := 0x80004180)
    (jalx_80004180 live (fun p hp => hlive _ (interp_code_80004180 p hp)))
    interp_code_80004180 (by decide) D (k := k) (slot := execSP s + 16#64)
    (aC := BitVec.ofNat 64 p) (aE := aE) (s := execSP s)
    (m := execNeed (.expr e) d - 176) g.child g.fits g.below g.slotGeom hbb
  iframe He Hcode Hfb Hms Hst Hw
  isplitl []
  · ipureintro
    refine ⟨⟨by ix_reg, by ix_reg; exact hf.regs.s1, by ix_reg, by ix_reg; exact hf.regs.s3,
      by ix_reg; exact hf.regs.sp⟩, fun b hb => ?_⟩
    have g1 : (execSP s + 16#64).toNat = s.toNat - 176 + 16 := g.slot
    simp only [VsaIris.InExt] at hb g1 ⊢; omega
  isplitl []
  · imodintro; rw [hpt]; iapply astEG_of_view hpe hn.geo $$ Hro
  iintro %R1 %w0 %w1 %w2 %hkeep1 #Hv1 Hms Hst Hw
  -- the epilogue
  iapply wp_swpF (twpW _) (text := interpText ++ dataOf m (stmtView aS.toNat 16))
    (F := iprop(stackScratch (execSP s) (execNeed (.expr e) d - 176) ∗ slot24 aRet.toNat ∗
      world N L Room inp (.counted k) st' d ∗
      execDispK (vsaModel live) N L Room inp (twpW (vsaModel live)) Φ (.counted k) st' d (.expr e)
        .normal aRet s R ret v8 v9 v18 v19))
  rotate_left
  · iframe Hms Hst Hslot Hw HK
    iapply roOwn_data hn.view $$ [Hcode Hro]
    iframe Hcode Hro
  intro F'
  refine ExecExpr_run2 (m := m) (aS := aS) (v8 := v8) (v9 := v9) (v18 := v18) (v19 := v19) hlive
    hfg.sf hfg.lo hfg.hi hfg.al hf.ral ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · ix_reg; rw [keep_reg hkeep1 (by decide)]; ix_reg; exact hf.regs.sp
  · rw [hMt1]; ix_fwd; rw [hoff _ (by decide)]; exact hf.saved.ra
  · rw [hMt1]; ix_fwd; rw [hoff _ (by decide)]; exact hf.saved.s0
  · rw [hMt1]; ix_fwd; rw [hoff _ (by decide)]; exact hf.saved.s1
  · rw [hMt1]; ix_fwd; rw [hoff _ (by decide)]; exact hf.saved.s2
  · rw [hMt1]; ix_fwd; rw [hoff _ (by decide)]; exact hf.saved.s3
  intros
  apply swp_closeRM
  intro R' Mt' hR' _
  refine .trans ?_ (execDisp_finish (N := N) (L := L) (Room := Room) (inp := inp) (twpW _)
    (ρ := .counted k) (st' := st') (status := .normal) (aRet := aRet) (R := R) (R' := R')
    (Mt := Mt') (v8 := v8) (v9 := v9) (v18 := v18) (v19 := v19) (pc := ret) hf.stack rfl ?_ ?_)
  rotate_left
  · subst hR'; ix_reg
  · subst hR'
    exact ⟨by ix_reg; exact execSP_restore s, by ix_reg, by ix_reg, by ix_reg, by ix_reg,
      fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_keep [hkeep1],
      by ix_reg; rfl⟩
  unfold F'
  simp only [statusRet]
  iintro ⟨⟨Hst, Hslot, Hw, HK⟩, Hms⟩
  iframe Hms Hst Hw HK Hslot

theorem caseP_ExecExpr {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat} {Core : IProp GF}
    {st : St} {d env : Nat} {e : Expr} :
    evalSpecsP (GF := GF) (vsaModel live) N L Room inp Core ⊢
      execDispP_body (GF := GF) (vsaModel live) N L Room inp Core st d env (.expr e) := by
  iintro #IH
  unfold execDispP_body
  iintro !> %Φ %aS %aE %aRet %s %R %Mt %ret %v8 %v9 %v18 %v19 Hpre HK
  unfold execDispPre
  icases Hpre with ⟨Hms, %hf, #Hcode, #Hast, #Hfb, Hst, Hslot, Hw⟩
  unfold astSG
  icases Hast with ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩
  obtain ⟨p, hn, hp, hpe, hpl⟩ : ∃ p, StmtNode m P aS 0 16 ∧
      ldv .ld m (aS + 8#64).toNat = BitVec.ofNat 64 p ∧ ExprReprWithin m P p e ∧ p < 2 ^ 64 := by
    cases hrepr with
    | expr h0 c0 hr cr hx =>
      have hn := stmtNode_of (w := 16) hgeo h0 c0 (by decide) (Or.inr (by decide))
        (fun j h1 h2 => field_mid hr cr h1 (by omega))
      exact ⟨_, hn, field64 hr (by have := hn.hi; omega), hx, readLE_lt hr⟩
  have hpt : (BitVec.ofNat 64 p).toNat = p := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpl]
  obtain ⟨hfg, hneed⟩ := execFrameGeom_of hf.stack
  have hoff := execSP_off (s := s) hfg.sf (by have := hfg.hi; omega)
  have g := callGeomF (f := 176) (o := 16) hf.stack hfg.sf (execNeed_expr e d) (by decide)
    (by decide) (by decide)
  have hbb : e.bodiesBound perCallBudget = true := hf.bodies
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (wpW _) (F := iprop(evalSpecsP (vsaModel live) N L Room inp Core ∗
      codeRes ∗ roOn P m ∗ frameAt env aE.toNat ∗
      stackScratch (execSP s) (execNeed (.expr e) d - 176) ∗ slot24 aRet.toNat ∗
      world N L Room inp .uncounted st d ∗
      ((∀ (st' : St) (status : Status), ⌜ExecS st d env (.expr e) st' status⌝ -∗
        execDispK (vsaModel live) N L Room inp (wpW (vsaModel live)) Φ .uncounted st' d (.expr e)
          status aRet s R ret v8 v9 v18 v19) ∧
       (iprop(abortAt Core s (execNeed (.expr e) d) ∗ slot24 aRet.toNat) -∗
          (wpW (vsaModel live)).W Φ))))
  rotate_left
  · iframe Hdv Hms IH Hcode Hro Hfb Hst Hslot Hw; iexact HK
  intro F'
  unfold execDispPC
  refine ExecExpr_run1 (aC := BitVec.ofNat 64 p) hlive hfg.sf hfg.lo hfg.hi hfg.al hn.lo hn.hi
    hn.off hf.regs.s0 hf.regs.a6 hf.regs.a4 hf.regs.sp hn.kind hn.kindu hp ?_
  intros
  apply swp_closeM
  intro Mt1 hMt1
  unfold F'
  iintro ⟨⟨#IH, #Hcode, #Hro, #Hfb, Hst, Hslot, Hw, HK⟩, Hms⟩
  -- the child, through the Löb hypothesis
  ihave He := evalSpecsP_at Core st d env e $$ IH
  iapply ms_callEvalPF (N := N) (L := L) (Room := Room) (inp := inp) (i := 0x80004180)
    (jalx_80004180 live (fun p hp => hlive _ (interp_code_80004180 p hp)))
    interp_code_80004180 (by decide) (slot := execSP s + 16#64)
    (aC := BitVec.ofNat 64 p) (aE := aE) (s0 := s) (sF := execSP s) (f := 176)
    (m := execNeed (.expr e) d - 176) (n0 := execNeed (.expr e) d) (Out := slot24 aRet.toNat)
    (Kret := iprop(∀ (st' : St) (status : Status), ⌜ExecS st d env (.expr e) st' status⌝ -∗
      execDispK (vsaModel live) N L Room inp (wpW (vsaModel live)) Φ .uncounted st' d (.expr e)
        status aRet s R ret v8 v9 v18 v19))
    (execSP_eq s).symm g.child g.fits g.below (by omega) hf.stack.le g.slotGeom hbb
  iframe He Hcode Hfb Hms Hst Hw Hslot HK
  isplitl []
  · ipureintro
    refine ⟨⟨by ix_reg, by ix_reg; exact hf.regs.s1, by ix_reg, by ix_reg; exact hf.regs.s3,
      by ix_reg; exact hf.regs.sp⟩, fun b hb => ?_⟩
    have g1 : (execSP s + 16#64).toNat = s.toNat - 176 + 16 := g.slot
    simp only [VsaIris.InExt] at hb g1 ⊢; omega
  isplitl []
  · imodintro; rw [hpt]; iapply astEG_of_view hpe hn.geo $$ Hro
  iintro %R1 %w0 %w1 %w2 %st' %v %hE %hkeep1 #Hv1 Hms Hst Hw Hslot HK
  -- the epilogue
  iapply wp_swpF (wpW _) (text := interpText ++ dataOf m (stmtView aS.toNat 16))
    (F := iprop(stackScratch (execSP s) (execNeed (.expr e) d - 176) ∗ slot24 aRet.toNat ∗
      world N L Room inp .uncounted st' d ∗
      execDispK (vsaModel live) N L Room inp (wpW (vsaModel live)) Φ .uncounted st' d (.expr e)
        .normal aRet s R ret v8 v9 v18 v19))
  rotate_left
  · ihave HK := and_elim_l $$ HK
    ihave HK := HK $$ %st' %Status.normal %(ExecS.expr st d env e st' v hE)
    iframe Hms Hst Hslot Hw HK
    iapply roOwn_data hn.view $$ [Hcode Hro]
    iframe Hcode Hro
  intro F'
  refine ExecExpr_run2 (m := m) (aS := aS) (v8 := v8) (v9 := v9) (v18 := v18) (v19 := v19) hlive
    hfg.sf hfg.lo hfg.hi hfg.al hf.ral ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · ix_reg; rw [keep_reg hkeep1 (by decide)]; ix_reg; exact hf.regs.sp
  · rw [hMt1]; ix_fwd; rw [hoff _ (by decide)]; exact hf.saved.ra
  · rw [hMt1]; ix_fwd; rw [hoff _ (by decide)]; exact hf.saved.s0
  · rw [hMt1]; ix_fwd; rw [hoff _ (by decide)]; exact hf.saved.s1
  · rw [hMt1]; ix_fwd; rw [hoff _ (by decide)]; exact hf.saved.s2
  · rw [hMt1]; ix_fwd; rw [hoff _ (by decide)]; exact hf.saved.s3
  intros
  apply swp_closeRM
  intro R' Mt' hR' _
  refine .trans ?_ (execDisp_finish (N := N) (L := L) (Room := Room) (inp := inp) (wpW _)
    (ρ := .uncounted) (st' := st') (status := .normal) (aRet := aRet) (R := R) (R' := R')
    (Mt := Mt') (v8 := v8) (v9 := v9) (v18 := v18) (v19 := v19) (pc := ret) hf.stack rfl ?_ ?_)
  rotate_left
  · subst hR'; ix_reg
  · subst hR'
    exact ⟨by ix_reg; exact execSP_restore s, by ix_reg, by ix_reg, by ix_reg, by ix_reg,
      fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_keep [hkeep1],
      by ix_reg; rfl⟩
  unfold F'
  simp only [statusRet]
  iintro ⟨⟨Hst, Hslot, Hw, HK⟩, Hms⟩
  iframe Hms Hst Hw HK Hslot

end VsaIris.Interp
