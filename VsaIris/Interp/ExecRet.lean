import VsaIris.Interp.ExecChild

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim

#ix_seg ExecRet_run1 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aS s aC : BitVec 64}
    (hsf : (s + 18446744073709551440#64).toNat = s.toNat - 176)
    (hs : 0x87800000 + 176 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aS.toNat) (hx2 : aS.toNat + 16 ≤ 0x100000000)
    (hx3 : aS.toNat + 16 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aS.toNat)
    (h8 : R 8 = aS) (h16 : R 16 = 8#64) (h14 : R 14 = 0x80019fb8#64)
    (h2 : R 2 = s + 18446744073709551440#64)
    (hk : ldv .lw m aS.toNat = 6#64) (hku : ldv .lwu m aS.toNat = 6#64)
    (hc : ldv .ld m (aS + 8#64).toNat = aC) (hc0 : aC ≠ 0#64) :
    IW live m (stmtView aS.toNat 16) (InExt (s.toNat - 176, 176)) Q 0x80004014#64 R Mt
  by rw [← upd_eq_self h16]
     ix_run hlive using [h8, h14, h2, hk, hku, hc, hc0, hsf] at 0x80004134

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

/-- `ret e` in every child-call mode: evaluate `e` into `sp+16`, copy it to the return slot,
status-3 epilogue. -/
theorem retCore (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs} {L : DlLayout}
    {Room : RoomPred} {inp : Nat} {st : St} {d env : Nat} {e : Expr} :
    ExecChildCore (GF := GF) (live := live) N L Room inp st d env (.ret (some e)) e .ret := by
  intro Wp Φ Hyp ρin ρout Kin aS aE aRet s R Mt ret v8 v9 v18 v19 hcall
  unfold execDispPre
  iintro ⟨#Hyp, ⟨Hms, %hf, #Hcode, #Hast, #Hfb, Hst, Hslot, Hw⟩, HK⟩
  unfold astSG
  icases Hast with ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩
  obtain ⟨p, hn⟩ := retNode_of hrepr hgeo
  obtain ⟨hfg, hneed⟩ := execFrameGeom_of hf.stack
  have hoff := execSP_offF (s := s) hfg.sf (by have := hfg.hi; omega)
  have g := callGeomF (f := 176) (o := 16) hf.stack hfg.sf (execNeed_ret e d) (by decide)
    (by decide) (by decide)
  have g1 : (execSP s + 16#64).toNat = s.toNat - 176 + 16 := g.slot
  have hbb : e.bodiesBound perCallBudget = true := hf.bodies
  ihave #Hdv := roOwn_data hn.node.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF Wp (F := iprop(□ Hyp ∗ codeRes ∗ roOn P m ∗ frameAt env aE.toNat ∗
      stackScratch (execSP s) (execNeed (.ret (some e)) d - 176) ∗ slot24 aRet.toNat ∗
      world N L Room inp ρin st d ∗ Kin))
  rotate_left
  · iframe Hdv Hms Hyp Hcode Hro Hfb Hst Hslot Hw HK
  intro F'
  unfold execDispPC
  refine ExecRet_run1 (aC := BitVec.ofNat 64 p) hlive hfg.sf hfg.lo hfg.hi hfg.al hn.node.lo
    hn.node.hi hn.node.off hf.regs.s0 hf.regs.a6 hf.regs.a4 hf.regs.sp hn.node.kind hn.node.kindu
    hn.field hn.ne ?_
  intros
  apply swp_closeRM
  intro R0 Mt1 hR0 hMt1
  unfold F'
  iintro ⟨⟨#Hyp, #Hcode, #Hro, #Hfb, Hst, Hslot, Hw, HK⟩, Hms⟩
  iapply hcall 0x80004134 _ (jalx_80004134 live (fun p hp => hlive _ ((interp_code (by decide)) p hp)))
    (interp_code (by decide)) (by decide) (slot := execSP s + 16#64) (aC := BitVec.ofNat 64 p)
    (aE := aE) (sF := execSP s) (f := 176) (m := execNeed (.ret (some e)) d - 176)
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
  have hk1 : KeepRegs [20, 21, 22, 23, 24, 25, 26, 27] R (upd R1 1 (BitVec.ofNat 64 (0x80004134 + 4))) := by
    subst hR0
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_keep [hkeep1]
  have hsv1 : ExecSaved (slotWrite Mt1 (execSP s + 16#64).toNat w0 w1 w2) s ret v8 v9 v18 v19 := by
    have := hfg.lo; rw [hMt1]; ix_esaved hf.saved using hoff
  have hcopy := wp_execRetCopy (N := N) (L := L) (Room := Room) (inp := inp) hlive Wp
    (Φ := Φ) (ρ := ρout) (st' := st') (d := d) (sm := .ret (some e)) (v := v) (aRet := aRet)
    (s := s) (ret := ret) (v8 := v8) (v9 := v9) (v18 := v18) (v19 := v19) (w0 := w0) (w1 := w1)
    (w2 := w2) (R0 := R) (R := upd R1 1 (BitVec.ofNat 64 (0x80004134 + 4)))
    (Mt := slotWrite Mt1 (execSP s + 16#64).toNat w0 w1 w2) hf.stack hf.slot hf.ral
    (by subst hR0; ix_reg; rw [keep_reg hkeep1 (by decide)]; ix_reg; exact hf.regs.sp)
    (by subst hR0; ix_reg; rw [keep_reg hkeep1 (by decide)]; ix_reg; exact hf.regs.s2)
    hsv1 hk1
    (by rw [← g1]; ix_fwd)
    (by rw [show s.toNat - 176 + 24 = (execSP s + 16#64).toNat + 8 by omega]; ix_fwd)
    (by rw [show s.toNat - 176 + 32 = (execSP s + 16#64).toNat + 16 by omega]; ix_fwd)
  iapply hcopy
  iframe Hcode Hms Hslot Hv1 Hst Hw HK

theorem retT (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs} {L : DlLayout}
    {Room : RoomPred} {inp : Nat} {st : St} {d env : Nat} {e : Expr} {st' : St} {v : Value}
    {n : Nat} (D : EvalECost st d env e st' v n)
    (he : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env e st' v n D) :
    ⊢ execDispT_body (GF := GF) (vsaModel live) N L Room inp st d env (.ret (some e)) st' (.ret v) n
        (.ret st d env e st' v n D) :=
  execChildT_of (stat := .ret) _ D he (retCore hlive)

theorem retP (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs} {L : DlLayout}
    {Room : RoomPred} {inp : Nat} {Core : IProp GF} {st : St} {d env : Nat} {e : Expr} :
    evalSpecsP (GF := GF) (vsaModel live) N L Room inp Core ⊢
      execDispP_body (GF := GF) (vsaModel live) N L Room inp Core st d env (.ret (some e)) :=
  execChildP_of (stat := .ret) (fun st' v h => ExecS.ret st d env e st' v h) (retCore hlive)

end

end VsaIris.Interp
