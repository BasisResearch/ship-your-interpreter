import VsaIris.Interp.ExecChild
import VsaIris.Interp.SymInterp

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim

#ix_seg IfArm_run1 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aS s aC : BitVec 64}
    (hsf : (s + 18446744073709551440#64).toNat = s.toNat - 176)
    (hs : 0x87800000 + 176 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aS.toNat) (hx2 : aS.toNat + 32 ≤ 0x100000000)
    (hx3 : aS.toNat + 32 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aS.toNat)
    (h8 : R 8 = aS) (h16 : R 16 = 8#64) (h14 : R 14 = 0x80019fb8#64)
    (h2 : R 2 = s + 18446744073709551440#64)
    (hk : ldv .lw m aS.toNat = 3#64) (hku : ldv .lwu m aS.toNat = 3#64)
    (hc : ldv .ld m (aS + 8#64).toNat = aC) :
    IW live m (stmtView aS.toNat 32) (InExt (s.toNat - 176, 176)) Q 0x80004014#64 R Mt
  by rw [← upd_eq_self h16]
     sym_run hlive using [h8, h14, h2, hk, hku, hc, hsf] at 0x800041f8

#ix_seg IfArm_run2 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {s : BitVec 64}
    (hsf : (s + 18446744073709551440#64).toNat = s.toNat - 176)
    (hs : 0x87800000 + 176 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (h2 : R 2 = s + 18446744073709551440#64) :
    IW live m [] (InExt (s.toNat - 176, 176)) Q 0x800041fc#64 R Mt
  by sym_run hlive using [h2, hsf] at 0x80004218

#ix_seg IfArm_runT {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aS s aT : BitVec 64}
    (hx1 : 0x80000000 ≤ aS.toNat) (hx2 : aS.toNat + 32 ≤ 0x100000000)
    (hx3 : aS.toNat + 32 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aS.toNat)
    (h8 : R 8 = aS) (h10 : R 10 = 1#64) (ht : ldv .ld m (aS + 16#64).toNat = aT) :
    IW live m (stmtView aS.toNat 32) (InExt (s.toNat - 176, 176)) Q 0x8000421c#64 R Mt
  by rw [← upd_eq_self h10]
     sym_run hlive using [h8, ht] at 0x80004014

#ix_seg IfArm_runF {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aS s aE : BitVec 64}
    (hx1 : 0x80000000 ≤ aS.toNat) (hx2 : aS.toNat + 32 ≤ 0x100000000)
    (hx3 : aS.toNat + 32 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aS.toNat)
    (h8 : R 8 = aS) (h10 : R 10 = 0#64) (he : ldv .ld m (aS + 24#64).toNat = aE)
    (he0 : aE ≠ 0#64) :
    IW live m (stmtView aS.toNat 32) (InExt (s.toNat - 176, 176)) Q 0x8000421c#64 R Mt
  by rw [← upd_eq_self h10]
     sym_run hlive using [h8, he, he0] at 0x80004014 0x8000409c

#ix_seg IfArm_runN {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aS s : BitVec 64}
    (hx1 : 0x80000000 ≤ aS.toNat) (hx2 : aS.toNat + 32 ≤ 0x100000000)
    (hx3 : aS.toNat + 32 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aS.toNat)
    (h8 : R 8 = aS) (h10 : R 10 = 0#64) (he : ldv .ld m (aS + 24#64).toNat = 0#64) :
    IW live m (stmtView aS.toNat 32) (InExt (s.toNat - 176, 176)) Q 0x8000421c#64 R Mt
  by rw [← upd_eq_self h10]
     sym_run hlive using [h8, he] at 0x8000409c

section Middle

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop} {N : NativeAddrs}

theorem wp_ifTruthy (hlive : ∀ p ∈ interpText, live p.1) (Wp : MachWP (GF := GF) (vsaModel live))
    {Φ : Nat × String → IProp GF} {F : IProp GF} {v : Value} {R0 : Nat → BitVec 64} {M : Mem}
    {s ret v8 v9 v18 v19 w0 w1 w2 : BitVec 64}
    (hfg : ExecFrameGeom s) (h2 : R0 2 = execSP s)
    (hw0 : ldv .ld M (s.toNat - 176 + 56) = w0) (hw1 : ldv .ld M (s.toNat - 176 + 64) = w1)
    (hw2 : ldv .ld M (s.toNat - 176 + 72) = w2) (hsv : ExecSaved M s ret v8 v9 v18 v19)
    (hK : ∀ (R3 : Nat → BitVec 64) (M3 : Mem), KeepRegs calleeSaved R0 R3 →
      R3 10 = (if v.truthy then 1#64 else 0#64) → ExecSaved M3 s ret v8 v9 v18 v19 →
      F ∗ codeRes ∗ ms 0x8000421c#64 R3 (InExt (s.toNat - 176, 176)) M3 ⊢ Wp.W Φ) :
    F ∗ codeRes ∗ ms 0x800041fc#64 R0 (InExt (s.toNat - 176, 176)) M ∗ □ valOf N v w0 w1 w2 ∗
      valueTruthySpec (vsaModel live) N Wp (execSP s + 16#64) v ⊢ Wp.W Φ := by
  have hoff := execSP_offF (s := s) hfg.sf (by have := hfg.hi; omega)
  have g16 : (execSP s + 16#64).toNat = s.toNat - 176 + 16 := hoff 16 (by decide)
  have hslg : SlotGeom (execSP s + 16#64) := by
    have := hfg.lo; have := hfg.hi; have := hfg.al
    refine ⟨?_, ?_, ?_⟩ <;> rw [g16] <;> (try unfold Vsa.Sim.tohostAddr) <;> omega
  iintro ⟨HF, #Hcode, Hms, #Hv, Hvt⟩
  iapply wp_swpF Wp (text := interpText ++ dataOf ∅ [])
  rotate_left
  · icombine HF Hcode Hv Hvt as HF'; isplitl []; iapply codeRes_text $$ Hcode; iframe HF' Hms
  intro F'
  refine IfArm_run2 (m := ∅) hlive hfg.sf hfg.lo hfg.hi hfg.al h2 ?_
  intros
  apply swp_closeRM
  intro R2 M2 hR2 hM2
  have hsv2 : ExecSaved M2 s ret v8 v9 v18 v19 := by
    have := hfg.lo; rw [hM2]; ix_esaved hsv using hoff
  unfold F'
  iintro ⟨⟨HF, #Hcode, #Hv, Hvt⟩, Hms⟩
  unfold valueTruthySpec
  iapply ms_callHelperVal Wp (i := 0x80004218)
    ((step% jalx 0x80004218) live (fun p hp => hlive _ ((interp_code (by decide)) p hp)))
    (interp_code (by decide)) (by decide) (R := R2) (S := InExt (s.toNat - 176, 176)) (Mt := M2)
    (a := execSP s + 16#64) (v := v) (w0 := w0) (w1 := w1) (w2 := w2)
    (Q := fun rv' => iprop(⌜rv' 10 = if v.truthy then 1#64 else 0#64⌝))
    (fun b hb => by simp only [VsaIris.InExt] at hb ⊢; rw [g16] at hb; omega) hslg
    (by rw [hM2]; ix_fwd; rw [hoff _ (by decide), hw0])
    (by rw [hM2, g16, show s.toNat - 176 + 16 + 8 = (s + 18446744073709551440#64 + 24#64).toNat by
      rw [hoff 24 (by decide)]]; ix_fwd; rw [hoff _ (by decide), hw1])
    (by rw [hM2, g16, show s.toNat - 176 + 16 + 16 = (s + 18446744073709551440#64 + 32#64).toNat by
      rw [hoff 32 (by decide)]]; ix_fwd; rw [hoff _ (by decide), hw2])
  iframe Hvt Hcode Hms Hv
  isplitl []
  · ipureintro; subst hR2; ix_reg
  iintro %R' %M3 %hk %hag %h10 Hms
  have hk3 : KeepRegs calleeSaved R0 (upd R' 1 (BitVec.ofNat 64 (0x80004218 + 4))) := by
    intro x hx
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
    subst hR2
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (ix_reg; rw [keep_helper hk (by decide) (by decide)]; ix_reg)
  have h10' : upd R' 1 (BitVec.ofNat 64 (0x80004218 + 4)) 10 = if v.truthy then 1#64 else 0#64 := by
    ix_reg; exact h10
  have hsv3 : ExecSaved M3 s ret v8 v9 v18 v19 := by
    have := hfg.lo
    exact hsv2.congrHi (fun x h1 h2' => hag x (by simp only [InExt]; omega)
      (by simp only [InExt]; rw [g16]; omega)) (by omega)
  iapply hK _ _ hk3 h10' hsv3
  iframe HF Hcode Hms

end Middle

section Prefix

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop} {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}

structure IfRoute (m : Mem) (P : Nat → Prop) (aS : BitVec 64) (c : Expr) (t : Stmt)
    (eo : Option Stmt) (R R3 : Nat → BitVec 64) (M3 : Mem) (s ret v8 v9 v18 v19 : BitVec 64)
    (v : Value) : Prop where
  node : ∃ pc pt pe, IfNode m P aS c t eo pc pt pe
  geo : ∀ k, P k → ReadOK k
  keep : KeepRegs calleeSaved R R3
  a0 : R3 10 = if v.truthy then 1#64 else 0#64
  saved : ExecSaved M3 s ret v8 v9 v18 v19

/-- The `if` prefix in every child-call mode: evaluate the condition into `sp+56`, copy it,
`value_truthy`, and hand the routed state with the child's result to `hK`. -/
theorem ifPrefix (hlive : ∀ p ∈ interpText, live p.1) (Wp : MachWP (GF := GF) (vsaModel live))
    {Φ : Nat × String → IProp GF} {Hyp : IProp GF} {ρin ρout : Regime} {Kin : IProp GF}
    {Kfin : St → Value → IProp GF}
    {st : St} {d env : Nat} {c : Expr} {t : Stmt} {eo : Option Stmt}
    {aS aE aRet s ret v8 v9 v18 v19 : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem} {F : IProp GF}
    (hcall : ChildCall N L Room inp Wp Φ Hyp ρin ρout st d env c s (execNeed (.ifStmt c t eo) d)
      (slot24 aRet.toNat) Kin Kfin)
    (hvt : ⊢ ∀ p w, valueTruthySpec (GF := GF) (vsaModel live) N Wp p w)
    (hf : DispFacts inp st d (.ifStmt c t eo) R Mt aS aE aRet s ret v8 v9 v18 v19)
    (hK : ∀ (P : Nat → Prop) (m : Mem) (R3 : Nat → BitVec 64) (M3 : Mem) (st' : St) (v : Value),
      IfRoute m P aS c t eo R R3 M3 s ret v8 v9 v18 v19 v →
      F ∗ codeRes ∗ roOn P m ∗ frameAt env aE.toNat ∗
        ms 0x8000421c#64 R3 (InExt (s.toNat - 176, 176)) M3 ∗
        stackScratch (execSP s) (execNeed (.ifStmt c t eo) d - 176) ∗ slot24 aRet.toNat ∗
        world N L Room inp ρout st' d ∗ Kfin st' v ⊢ Wp.W Φ) :
    □ Hyp ∗ F ∗ ms execDispPC R (InExt (s.toNat - 176, 176)) Mt ∗ codeRes ∗
      □ astSG aS.toNat (.ifStmt c t eo) ∗ □ frameAt env aE.toNat ∗
      stackScratch (execSP s) (execNeed (.ifStmt c t eo) d - 176) ∗ slot24 aRet.toNat ∗
      world N L Room inp ρin st d ∗ Kin ⊢ Wp.W Φ := by
  iintro ⟨#Hyp, HF, Hms, #Hcode, #Hast, #Hfb, Hst, Hslot, Hw, HK⟩
  unfold astSG
  icases Hast with ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩
  obtain ⟨pc, pt, pe, hn⟩ := ifNode_of hrepr hgeo
  obtain ⟨hfg, hneed⟩ := execFrameGeom_of hf.stack
  have hoff := execSP_offF (s := s) hfg.sf (by have := hfg.hi; omega)
  have g := callGeomF (f := 176) (o := 56) hf.stack hfg.sf (execNeed_if_cond c t eo d) (by decide)
    (by decide) (by decide)
  have g1 : (execSP s + 56#64).toNat = s.toNat - 176 + 56 := g.slot
  have hbb : c.bodiesBound perCallBudget = true := by
    have := hf.bodies; cases eo <;> simp only [Stmt.bodiesBound, Bool.and_eq_true] at this <;>
      first | exact this.1 | exact this.1.1
  ihave #Hdv := roOwn_data hn.node.view $$ [$]
  iapply wp_swpF Wp (F := iprop(□ Hyp ∗ F ∗ codeRes ∗
      roOn P m ∗ frameAt env aE.toNat ∗
      stackScratch (execSP s) (execNeed (.ifStmt c t eo) d - 176) ∗ slot24 aRet.toNat ∗
      world N L Room inp ρin st d ∗ Kin))
  rotate_left
  · iframe Hdv Hms Hyp HF Hcode Hro Hfb Hst Hslot Hw HK
  intro F'
  unfold execDispPC
  refine IfArm_run1 (aC := BitVec.ofNat 64 pc) hlive hfg.sf hfg.lo hfg.hi hfg.al hn.node.lo
    hn.node.hi hn.node.off hf.regs.s0 hf.regs.a6 hf.regs.a4 hf.regs.sp hn.node.kind hn.node.kindu
    hn.cond ?_
  intros
  apply swp_closeRM
  intro R0 Mt1 hR0 hMt1
  unfold F'
  iintro ⟨⟨#Hyp, HF, #Hcode, #Hro, #Hfb, Hst, Hslot, Hw, HK⟩, Hms⟩

  iapply hcall 0x800041f8 _ ((step% jalx 0x800041f8) live (fun p hp => hlive _ ((interp_code (by decide)) p hp)))
    (interp_code (by decide)) (by decide) (slot := execSP s + 56#64) (aC := BitVec.ofNat 64 pc)
    (aE := aE) (sF := execSP s) (f := 176) (m := execNeed (.ifStmt c t eo) d - 176)
    (execSP_eq s).symm g.child g.fits g.below (by omega) hf.stack.le g.slotGeom hbb
  iframe Hyp Hcode Hfb Hms Hst Hw Hslot HK
  isplitl []
  · ipureintro
    subst hR0
    refine ⟨⟨by ix_reg, by ix_reg; exact hf.regs.s1, by ix_reg, by ix_reg; exact hf.regs.s3,
      by ix_reg; exact hf.regs.sp⟩, fun b hb => ?_⟩
    simp only [VsaIris.InExt] at hb g1 ⊢; omega
  isplitl []
  · imodintro; rw [hn.condNat]; iapply astEG_of_view hn.condRepr hn.node.geo $$ Hro
  iintro %R1 %w0 %w1 %w2 %st' %v %hkeep1 #Hv1 Hms Hst Hw Hslot HK
  have hk1 : KeepRegs calleeSaved R (upd R1 1 (BitVec.ofNat 64 (0x800041f8 + 4))) := by
    subst hR0
    intro x hx
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      ix_keep [hkeep1]
  have hsv1 : ExecSaved (slotWrite Mt1 (execSP s + 56#64).toNat w0 w1 w2) s ret v8 v9 v18 v19 := by
    have := hfg.lo; rw [hMt1]; ix_esaved hf.saved using hoff
  have hK' : ∀ (R3 : Nat → BitVec 64) (M3 : Mem),
      KeepRegs calleeSaved (upd R1 1 (BitVec.ofNat 64 (0x800041f8 + 4))) R3 →
      R3 10 = (if v.truthy then 1#64 else 0#64) → ExecSaved M3 s ret v8 v9 v18 v19 →
      iprop(F ∗ roOn P m ∗ frameAt env aE.toNat ∗
        stackScratch (execSP s) (execNeed (.ifStmt c t eo) d - 176) ∗ slot24 aRet.toNat ∗
        world N L Room inp ρout st' d ∗ Kfin st' v) ∗ codeRes ∗
        ms 0x8000421c#64 R3 (InExt (s.toNat - 176, 176)) M3 ⊢ Wp.W Φ := by
    intro R3 M3 hk3 h10 hsv3
    iintro ⟨⟨HF, #Hro, #Hfb, Hst, Hslot, Hw, HK⟩, #Hcode, Hms⟩
    iapply hK P m R3 M3 st' v ⟨⟨pc, pt, pe, hn⟩, hn.node.geo, KeepRegs.trans hk1 hk3, h10, hsv3⟩
    iframe HF Hcode Hro Hfb Hms Hst Hslot Hw HK
  ihave Hvt := hvt $$ %(execSP s + 16#64) %v
  iapply wp_ifTruthy hlive Wp (N := N) (v := v) (R0 := upd R1 1 (BitVec.ofNat 64 (0x800041f8 + 4)))
    (M := slotWrite Mt1 (execSP s + 56#64).toNat w0 w1 w2) (w0 := w0) (w1 := w1) (w2 := w2) hfg
    (by rw [hk1 2 (by decide)]; exact hf.regs.sp)
    (by rw [← g1]; try ix_fwd)
    (by rw [show s.toNat - 176 + 64 = (execSP s + 56#64).toNat + 8 by omega]; try ix_fwd)
    (by rw [show s.toNat - 176 + 72 = (execSP s + 56#64).toNat + 16 by omega]; try ix_fwd) hsv1 hK'
  iframe HF Hro Hfb Hst Hslot Hw HK Hcode Hms Hv1 Hvt


theorem ifPrefixT (hlive : ∀ p ∈ interpText, live p.1) {Φ : Nat × String → IProp GF}
    {st : St} {d env : Nat} {c : Expr} {t : Stmt} {eo : Option Stmt} {st' : St} {v : Value}
    {nc k : Nat} {aS aE aRet s ret v8 v9 v18 v19 : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    {F : IProp GF} (Dc : EvalECost st d env c st' v nc)
    (hc : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env c st' v nc Dc)
    (hvt : ⊢ ∀ p w, valueTruthySpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) p w)
    (hf : DispFacts inp st d (.ifStmt c t eo) R Mt aS aE aRet s ret v8 v9 v18 v19)
    (hK : ∀ (P : Nat → Prop) (m : Mem) (R3 : Nat → BitVec 64) (M3 : Mem),
      IfRoute m P aS c t eo R R3 M3 s ret v8 v9 v18 v19 v →
      F ∗ codeRes ∗ roOn P m ∗ frameAt env aE.toNat ∗
        ms 0x8000421c#64 R3 (InExt (s.toNat - 176, 176)) M3 ∗
        stackScratch (execSP s) (execNeed (.ifStmt c t eo) d - 176) ∗ slot24 aRet.toNat ∗
        world N L Room inp (.counted k) st' d ⊢ (twpW (vsaModel live)).W Φ) :
    F ∗ ms execDispPC R (InExt (s.toNat - 176, 176)) Mt ∗ codeRes ∗
      □ astSG aS.toNat (.ifStmt c t eo) ∗ □ frameAt env aE.toNat ∗
      stackScratch (execSP s) (execNeed (.ifStmt c t eo) d - 176) ∗ slot24 aRet.toNat ∗
      world N L Room inp (.counted (k + nc)) st d ⊢ (twpW (vsaModel live)).W Φ := by
  refine .trans ?_ (ifPrefix hlive (twpW _) (L := L) (Room := Room) (env := env) (F := F) (childCallT (k := k) Dc hc (Kfin := fun st'' v'' =>
    iprop(⌜st'' = st' ∧ v'' = v⌝))) hvt hf ?hk)
  · iintro ⟨HF, Hms, #Hcode, #Hast, #Hfb, Hst, Hslot, Hw⟩
    iframe HF Hms Hcode Hast Hfb Hst Hslot Hw
    isplitl []
    · iapply (intuitionistically_emp (PROP := IProp GF)).2
      ipureintro; trivial
    ipureintro; exact ⟨rfl, rfl⟩
  case hk =>
  intro P m R3 M3 st'' v'' hr
  iintro ⟨HF, Hcode, Hro, Hfb, Hms, Hst, Hslot, Hw, %heq⟩
  obtain ⟨rfl, rfl⟩ := heq
  iapply hK P m R3 M3 hr
  iframe HF Hcode Hro Hfb Hms Hst Hslot Hw

end Prefix

section Routes

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop} {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}

theorem if_bodies {c : Expr} {t : Stmt} {eo : Option Stmt}
    (h : (Stmt.ifStmt c t eo).bodiesBound perCallBudget = true) :
    t.bodiesBound perCallBudget = true ∧ ∀ e, eo = some e → e.bodiesBound perCallBudget = true := by
  cases eo <;> simp only [Stmt.bodiesBound, Bool.and_eq_true] at h
  · exact ⟨h.2, fun _ h => by cases h⟩
  · exact ⟨h.1.2, fun _ he => by cases he; exact h.2⟩

theorem if_dispRegs {R R3 R4 : Nat → BitVec 64} {inp aS aS' aE aRet s : BitVec 64}
    (hd : DispRegs R inp aS aE aRet s) (hk : KeepRegs calleeSaved R R3)
    (h2 : R4 2 = R3 2) (h8 : R4 8 = aS') (h9 : R4 9 = R3 9) (h18 : R4 18 = R3 18)
    (h19 : R4 19 = R3 19) (h16 : R4 16 = 8#64) (h14 : R4 14 = 0x80019fb8#64) :
    DispRegs R4 inp aS' aE aRet s :=
  ⟨h2.trans ((hk 2 (by decide)).trans hd.sp), h8, h9.trans ((hk 9 (by decide)).trans hd.s1),
    h18.trans ((hk 18 (by decide)).trans hd.s2), h19.trans ((hk 19 (by decide)).trans hd.s3), h16, h14⟩

theorem ifRouteThenT (hlive : ∀ p ∈ interpText, live p.1) {Φ : Nat × String → IProp GF}
    {st st' st'' : St} {d env : Nat} {c : Expr} {t : Stmt} {eo : Option Stmt} {status : Status}
    {nt k : Nat} {aS aE aRet s ret v8 v9 v18 v19 : BitVec 64} {R R3 : Nat → BitVec 64}
    {Mt M3 : Mem} {P : Nat → Prop} {m : Mem} {v : Value}
    (Dt : ExecSCost st' d env t st'' status nt)
    (ht : ⊢ execDispT_body (GF := GF) (vsaModel live) N L Room inp st' d env t st'' status nt Dt)
    (hf : DispFacts inp st d (.ifStmt c t eo) R Mt aS aE aRet s ret v8 v9 v18 v19)
    (hr : IfRoute m P aS c t eo R R3 M3 s ret v8 v9 v18 v19 v) (hv : v.truthy = true) :
    execDispK (vsaModel live) N L Room inp (twpW (vsaModel live)) Φ (.counted k) st'' d
        (.ifStmt c t eo) status aRet s R ret v8 v9 v18 v19 ∗ codeRes ∗ roOn P m ∗
      frameAt env aE.toNat ∗ ms 0x8000421c#64 R3 (InExt (s.toNat - 176, 176)) M3 ∗
      stackScratch (execSP s) (execNeed (.ifStmt c t eo) d - 176) ∗ slot24 aRet.toNat ∗
      world N L Room inp (.counted (k + nt)) st' d ⊢ (twpW (vsaModel live)).W Φ := by
  obtain ⟨pc, pt, pe, hn⟩ := hr.node
  have hle : execNeed t d ≤ execNeed (.ifStmt c t eo) d := by
    have := execNeed_if_then c t eo d; unfold execFrame at this; omega
  iintro ⟨HK, #Hcode, #Hro, #Hfb, Hms, Hst, Hslot, Hw⟩
  ihave #Hdv := roOwn_data hn.node.view $$ [$]
  iapply wp_swpF (twpW _)
  rotate_left
  · icombine Hcode Hro Hfb Hst Hslot Hw HK as HF; isplitl []; iexact Hdv; iframe HF Hms
  intro F'
  refine IfArm_runT (aT := BitVec.ofNat 64 pt) hlive hn.node.lo hn.node.hi hn.node.off
    ((hr.keep 8 (by decide)).trans hf.regs.s0) (by rw [hr.a0, hv]; rfl) hn.thn ?_
  intros
  apply swp_closeRM
  intro R4 M4 hR4 hM4
  have hk4 : KeepRegs [20, 21, 22, 23, 24, 25, 26, 27] R R4 := by
    subst hR4
    repeat (first | exact hr.keep.sub (by decide) | refine KeepRegs.upd ?_ (by decide) _)
  have hdr : DispRegs R4 (BitVec.ofNat 64 inp) (BitVec.ofNat 64 pt) aE aRet s := by
    subst hR4
    exact if_dispRegs hf.regs hr.keep (by ix_reg) (by ix_reg) (by ix_reg) (by ix_reg) (by ix_reg)
      (by ix_reg) (by ix_reg)
  have hchild := execDispT_apply ht Φ k (BitVec.ofNat 64 pt) aE aRet s R4 M4 ret v8 v9 v18 v19
  unfold F'
  iintro ⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, HK⟩, Hms⟩
  unfold execDispPC at hchild
  iapply ifRedispatch (twpW _) hf.stack hle hk4 hchild
    ⟨hdr, hM4 ▸ hr.saved, hf.ral, hf.stack.narrow hle, hf.slot, (if_bodies hf.bodies).1⟩
  unfold execDispPC
  iframe Hms Hcode Hfb Hst Hslot Hw HK
  imodintro
  unfold astSG
  iexists P, m
  iframe Hro
  ipureintro; exact ⟨by rw [hn.thnNat]; exact hn.thnRepr, hr.geo⟩

theorem ifRouteElseT (hlive : ∀ p ∈ interpText, live p.1) {Φ : Nat × String → IProp GF}
    {st st' st'' : St} {d env : Nat} {c : Expr} {t e : Stmt} {status : Status}
    {ne k : Nat} {aS aE aRet s ret v8 v9 v18 v19 : BitVec 64} {R R3 : Nat → BitVec 64}
    {Mt M3 : Mem} {P : Nat → Prop} {m : Mem} {v : Value}
    (De : ExecSCost st' d env e st'' status ne)
    (he : ⊢ execDispT_body (GF := GF) (vsaModel live) N L Room inp st' d env e st'' status ne De)
    (hf : DispFacts inp st d (.ifStmt c t (some e)) R Mt aS aE aRet s ret v8 v9 v18 v19)
    (hr : IfRoute m P aS c t (some e) R R3 M3 s ret v8 v9 v18 v19 v) (hv : v.truthy = false) :
    execDispK (vsaModel live) N L Room inp (twpW (vsaModel live)) Φ (.counted k) st'' d
        (.ifStmt c t (some e)) status aRet s R ret v8 v9 v18 v19 ∗ codeRes ∗ roOn P m ∗
      frameAt env aE.toNat ∗ ms 0x8000421c#64 R3 (InExt (s.toNat - 176, 176)) M3 ∗
      stackScratch (execSP s) (execNeed (.ifStmt c t (some e)) d - 176) ∗ slot24 aRet.toNat ∗
      world N L Room inp (.counted (k + ne)) st' d ⊢ (twpW (vsaModel live)).W Φ := by
  obtain ⟨pc, pt, pe, hn⟩ := hr.node
  obtain ⟨her, hne⟩ := hn.elsRepr e rfl
  have hle : execNeed e d ≤ execNeed (.ifStmt c t (some e)) d := by
    have := execNeed_if_else c t e d; unfold execFrame at this; omega
  iintro ⟨HK, #Hcode, #Hro, #Hfb, Hms, Hst, Hslot, Hw⟩
  ihave #Hdv := roOwn_data hn.node.view $$ [$]
  iapply wp_swpF (twpW _)
  rotate_left
  · icombine Hcode Hro Hfb Hst Hslot Hw HK as HF; isplitl []; iexact Hdv; iframe HF Hms
  intro F'
  refine IfArm_runF (aE := BitVec.ofNat 64 pe) hlive hn.node.lo hn.node.hi hn.node.off
    ((hr.keep 8 (by decide)).trans hf.regs.s0) (by rw [hr.a0, hv]; rfl) hn.els hne ?_
    (fun _ h => absurd hne h)
  intros
  apply swp_closeRM
  intro R4 M4 hR4 hM4
  have hk4 : KeepRegs [20, 21, 22, 23, 24, 25, 26, 27] R R4 := by
    subst hR4
    repeat (first | exact hr.keep.sub (by decide) | refine KeepRegs.upd ?_ (by decide) _)
  have hdr : DispRegs R4 (BitVec.ofNat 64 inp) (BitVec.ofNat 64 pe) aE aRet s := by
    subst hR4
    exact if_dispRegs hf.regs hr.keep (by ix_reg) (by ix_reg) (by ix_reg) (by ix_reg) (by ix_reg)
      (by ix_reg) (by ix_reg)
  have hchild := execDispT_apply he Φ k (BitVec.ofNat 64 pe) aE aRet s R4 M4 ret v8 v9 v18 v19
  unfold F'
  iintro ⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, HK⟩, Hms⟩
  unfold execDispPC at hchild
  iapply ifRedispatch (twpW _) hf.stack hle hk4 hchild
    ⟨hdr, hM4 ▸ hr.saved, hf.ral, hf.stack.narrow hle, hf.slot, (if_bodies hf.bodies).2 e rfl⟩
  unfold execDispPC
  iframe Hms Hcode Hfb Hst Hslot Hw HK
  imodintro
  unfold astSG
  iexists P, m
  iframe Hro
  ipureintro; exact ⟨by rw [hn.elsNat]; exact her, hr.geo⟩

theorem ifRouteNone (hlive : ∀ p ∈ interpText, live p.1) (Wp : MachWP (GF := GF) (vsaModel live))
    {Φ : Nat × String → IProp GF} {ρ : Regime} {st st' : St} {d env : Nat} {c : Expr} {t : Stmt}
    {aS aE aRet s ret v8 v9 v18 v19 : BitVec 64} {R R3 : Nat → BitVec 64}
    {Mt M3 : Mem} {P : Nat → Prop} {m : Mem} {v : Value}
    (hf : DispFacts inp st d (.ifStmt c t none) R Mt aS aE aRet s ret v8 v9 v18 v19)
    (hr : IfRoute m P aS c t none R R3 M3 s ret v8 v9 v18 v19 v) (hv : v.truthy = false) :
    execDispK (vsaModel live) N L Room inp Wp Φ ρ st' d (.ifStmt c t none) .normal aRet s R ret
        v8 v9 v18 v19 ∗ codeRes ∗ roOn P m ∗
      frameAt env aE.toNat ∗ ms 0x8000421c#64 R3 (InExt (s.toNat - 176, 176)) M3 ∗
      stackScratch (execSP s) (execNeed (.ifStmt c t none) d - 176) ∗ slot24 aRet.toNat ∗
      world N L Room inp ρ st' d ⊢ Wp.W Φ := by
  obtain ⟨pc, pt, pe, hn⟩ := hr.node
  iintro ⟨HK, #Hcode, #Hro, #Hfb, Hms, Hst, Hslot, Hw⟩
  ihave #Hdv := roOwn_data hn.node.view $$ [$]
  iapply wp_swpF Wp
  rotate_left
  · icombine Hcode Hst Hslot Hw HK as HF; isplitl []; iexact Hdv; iframe HF Hms
  intro F'
  refine IfArm_runN hlive hn.node.lo hn.node.hi hn.node.off
    ((hr.keep 8 (by decide)).trans hf.regs.s0) (by rw [hr.a0, hv]; rfl)
    (by rw [hn.els, hn.elsNone rfl]) ?_
  intros
  apply swp_closeRM
  intro R4 M4 hR4 hM4
  have hepi := wp_execEpi (N := N) (L := L) (Room := Room) (inp := inp) hlive Wp
    (Φ := Φ) (ρ := ρ) (st' := st') (d := d) (sm := .ifStmt c t none) (status := .normal)
    (aRet := aRet) (s := s) (ret := ret) (v8 := v8) (v9 := v9) (v18 := v18) (v19 := v19) (R0 := R)
    (R := R4) (Mt := M4) hf.stack hf.ral
    (by subst hR4; ix_reg; rw [hr.keep 2 (by decide)]; exact hf.regs.sp)
    (by subst hR4; ix_reg; rfl) (hM4 ▸ hr.saved)
    (by subst hR4; repeat (first | exact hr.keep.sub (by decide) | refine KeepRegs.upd ?_ (by decide) _))
  simp only [statusRet] at hepi
  unfold F'
  iintro ⟨⟨#Hcode, Hst, Hslot, Hw, HK⟩, Hms⟩
  iapply hepi
  iframe Hcode Hms Hst Hslot Hw HK

end Routes

section Partial

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop} {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}

theorem ifPrefixP (hlive : ∀ p ∈ interpText, live p.1) {Φ : Nat × String → IProp GF}
    {Core : IProp GF} {st : St} {d env : Nat} {c : Expr} {t : Stmt} {eo : Option Stmt}
    {aS aE aRet s ret v8 v9 v18 v19 : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    {F Kret : IProp GF}
    (hvt : ⊢ ∀ p w, valueTruthySpec (GF := GF) (vsaModel live) N (wpW (vsaModel live)) p w)
    (hf : DispFacts inp st d (.ifStmt c t eo) R Mt aS aE aRet s ret v8 v9 v18 v19)
    (hK : ∀ (P : Nat → Prop) (m : Mem) (R3 : Nat → BitVec 64) (M3 : Mem) (st' : St) (v : Value),
      EvalE st d env c st' v → IfRoute m P aS c t eo R R3 M3 s ret v8 v9 v18 v19 v →
      F ∗ codeRes ∗ roOn P m ∗ frameAt env aE.toNat ∗
        ms 0x8000421c#64 R3 (InExt (s.toNat - 176, 176)) M3 ∗
        stackScratch (execSP s) (execNeed (.ifStmt c t eo) d - 176) ∗ slot24 aRet.toNat ∗
        world N L Room inp .uncounted st' d ∗
        (Kret ∧ (iprop(abortAt Core s (execNeed (.ifStmt c t eo) d) ∗ slot24 aRet.toNat) -∗
          (wpW (vsaModel live)).W Φ)) ⊢ (wpW (vsaModel live)).W Φ) :
    evalSpecsP (vsaModel live) N L Room inp Core ∗ F ∗
      ms execDispPC R (InExt (s.toNat - 176, 176)) Mt ∗ codeRes ∗
      □ astSG aS.toNat (.ifStmt c t eo) ∗ □ frameAt env aE.toNat ∗
      stackScratch (execSP s) (execNeed (.ifStmt c t eo) d - 176) ∗ slot24 aRet.toNat ∗
      world N L Room inp .uncounted st d ∗
      (Kret ∧ (iprop(abortAt Core s (execNeed (.ifStmt c t eo) d) ∗ slot24 aRet.toNat) -∗
        (wpW (vsaModel live)).W Φ)) ⊢ (wpW (vsaModel live)).W Φ := by
  refine .trans ?_ (ifPrefix hlive (wpW _) (L := L) (Room := Room) (env := env) (F := F) (childCallP (Core := Core) (Kret := Kret)
    (Kfin := fun st' v => iprop(⌜EvalE st d env c st' v⌝ ∗
      (Kret ∧ (iprop(abortAt Core s (execNeed (.ifStmt c t eo) d) ∗ slot24 aRet.toNat) -∗
        (wpW (vsaModel live)).W Φ)))) ?hc) hvt hf ?hk)
  · iintro ⟨#IH, HF, Hms, #Hcode, #Hast, #Hfb, Hst, Hslot, Hw, HK⟩
    iframe IH HF Hms Hcode Hast Hfb Hst Hslot Hw HK
  case hc => intro st' v h; iintro H; iframe H; ipureintro; exact h
  case hk =>
  intro P m R3 M3 st' v hr
  iintro ⟨HF, Hcode, Hro, Hfb, Hms, Hst, Hslot, Hw, %hE, HK⟩
  iapply hK P m R3 M3 st' v hE hr
  iframe HF Hcode Hro Hfb Hms Hst Hslot Hw HK

abbrev IfKP (Φ : Nat × String → IProp GF) (Core : IProp GF) (st : St) (d env : Nat)
    (sm : Stmt) (aRet s : BitVec 64) (R : Nat → BitVec 64) (ret v8 v9 v18 v19 : BitVec 64) :
    IProp GF :=
  iprop((∀ (st'' : St) (status : Status), ⌜ExecS st d env sm st'' status⌝ -∗
      execDispK (vsaModel live) N L Room inp (wpW (vsaModel live)) Φ .uncounted st'' d sm status
        aRet s R ret v8 v9 v18 v19) ∧
    (iprop(abortAt Core s (execNeed sm d) ∗ slot24 aRet.toNat) -∗ (wpW (vsaModel live)).W Φ))

theorem ifBranchP {Φ : Nat × String → IProp GF} {Core : IProp GF}
    {st st' : St} {d env : Nat} {sm sm' : Stmt}
    {aS' aE aRet s ret v8 v9 v18 v19 : BitVec 64} {R R4 : Nat → BitVec 64} {M4 : Mem}
    (hsg : StackGeom s (execNeed sm d)) (hle : execNeed sm' d ≤ execNeed sm d)
    (hk : KeepRegs [20, 21, 22, 23, 24, 25, 26, 27] R R4)
    (hE : ∀ st'' status, ExecS st' d env sm' st'' status → ExecS st d env sm st'' status)
    (hf : DispFacts inp st' d sm' R4 M4 aS' aE aRet s ret v8 v9 v18 v19) :
    execDispP_body (vsaModel live) N L Room inp Core st' d env sm' ∗
      ms execDispPC R4 (InExt (s.toNat - 176, 176)) M4 ∗ codeRes ∗ □ astSG aS'.toNat sm' ∗
      □ frameAt env aE.toNat ∗ stackScratch (execSP s) (execNeed sm d - 176) ∗ slot24 aRet.toNat ∗
      world N L Room inp .uncounted st' d ∗
      IfKP (live := live) (N := N) (L := L) (Room := Room) (inp := inp) Φ Core st d env sm aRet s R
        ret v8 v9 v18 v19
    ⊢ (wpW (vsaModel live)).W Φ := by
  obtain ⟨hfg, h176⟩ := execFrameGeom_of hf.stack
  iintro ⟨Hspec, Hms, #Hcode, #Hast, #Hfb, Hst, Hslot, Hw, HK⟩
  ihave ⟨Hsl, Hst⟩ := stack_redispatch hsg hle h176 hfg.sf $$ Hst
  ihave HK := execDispKP_redispatch hsg hle hk hE $$ [$]
  iapply execDispP_apply (N := N) (L := L) (Room := Room) (inp := inp) Φ aS' aE aRet s R4 M4 ret
    v8 v9 v18 v19
  iframe Hspec HK
  unfold execDispPre
  iframe Hms Hcode Hast Hfb Hst Hslot Hw
  ipureintro; exact hf

theorem ifRouteThenP (hlive : ∀ p ∈ interpText, live p.1) {Φ : Nat × String → IProp GF}
    {Core : IProp GF} {st st' : St} {d env : Nat} {c : Expr} {t : Stmt} {eo : Option Stmt}
    {aS aE aRet s ret v8 v9 v18 v19 : BitVec 64} {R R3 : Nat → BitVec 64}
    {Mt M3 : Mem} {P : Nat → Prop} {m : Mem} {v : Value}
    (hEc : EvalE st d env c st' v)
    (hf : DispFacts inp st d (.ifStmt c t eo) R Mt aS aE aRet s ret v8 v9 v18 v19)
    (hr : IfRoute m P aS c t eo R R3 M3 s ret v8 v9 v18 v19 v) (hv : v.truthy = true) :
    execDispsP (vsaModel live) N L Room inp Core ∗ codeRes ∗ roOn P m ∗
      frameAt env aE.toNat ∗ ms 0x8000421c#64 R3 (InExt (s.toNat - 176, 176)) M3 ∗
      stackScratch (execSP s) (execNeed (.ifStmt c t eo) d - 176) ∗ slot24 aRet.toNat ∗
      world N L Room inp .uncounted st' d ∗
      IfKP (live := live) (N := N) (L := L) (Room := Room) (inp := inp) Φ Core st d env
        (.ifStmt c t eo) aRet s R ret v8 v9 v18 v19
    ⊢ (wpW (vsaModel live)).W Φ := by
  obtain ⟨pc, pt, pe, hn⟩ := hr.node
  have hle : execNeed t d ≤ execNeed (.ifStmt c t eo) d := by
    have := execNeed_if_then c t eo d; unfold execFrame at this; omega
  iintro ⟨#IH, #Hcode, #Hro, #Hfb, Hms, Hst, Hslot, Hw, HK⟩
  ihave HX := execDispsP_at Core st' d env t $$ IH
  ihave #Hdv := roOwn_data hn.node.view $$ [$]
  iapply wp_swpF_later (X := execDispP_body (vsaModel live) N L Room inp Core st' d env t)
  rotate_left
  · icombine Hcode Hro Hfb Hst Hslot Hw HK as HF; isplitl []; iexact Hdv; iframe HF HX Hms
  intro F'
  refine IfArm_runT (aT := BitVec.ofNat 64 pt) hlive hn.node.lo hn.node.hi hn.node.off
    ((hr.keep 8 (by decide)).trans hf.regs.s0) (by rw [hr.a0, hv]; rfl) hn.thn ?_
  intros
  apply swp_closeRM_ne _ (by decide)
  intro R4 M4 hR4 hM4
  have hk4 : KeepRegs [20, 21, 22, 23, 24, 25, 26, 27] R R4 := by
    subst hR4
    repeat (first | exact hr.keep.sub (by decide) | refine KeepRegs.upd ?_ (by decide) _)
  have hdr : DispRegs R4 (BitVec.ofNat 64 inp) (BitVec.ofNat 64 pt) aE aRet s := by
    subst hR4
    exact if_dispRegs hf.regs hr.keep (by ix_reg) (by ix_reg) (by ix_reg) (by ix_reg) (by ix_reg)
      (by ix_reg) (by ix_reg)
  unfold F'
  iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, HK⟩, HX⟩, Hms⟩
  iapply ifBranchP hf.stack hle hk4 (fun st'' status h => ExecS.ifTrue st d env c t eo st' st'' v
    status hEc hv h) ⟨hdr, hM4 ▸ hr.saved, hf.ral, hf.stack.narrow hle, hf.slot, (if_bodies hf.bodies).1⟩
  unfold execDispPC
  iframe HX Hms Hcode Hfb Hst Hslot Hw HK
  imodintro
  unfold astSG
  iexists P, m
  iframe Hro
  ipureintro; exact ⟨by rw [hn.thnNat]; exact hn.thnRepr, hr.geo⟩

theorem ifRouteElseP (hlive : ∀ p ∈ interpText, live p.1) {Φ : Nat × String → IProp GF}
    {Core : IProp GF} {st st' : St} {d env : Nat} {c : Expr} {t e : Stmt}
    {aS aE aRet s ret v8 v9 v18 v19 : BitVec 64} {R R3 : Nat → BitVec 64}
    {Mt M3 : Mem} {P : Nat → Prop} {m : Mem} {v : Value}
    (hEc : EvalE st d env c st' v)
    (hf : DispFacts inp st d (.ifStmt c t (some e)) R Mt aS aE aRet s ret v8 v9 v18 v19)
    (hr : IfRoute m P aS c t (some e) R R3 M3 s ret v8 v9 v18 v19 v) (hv : v.truthy = false) :
    execDispsP (vsaModel live) N L Room inp Core ∗ codeRes ∗ roOn P m ∗
      frameAt env aE.toNat ∗ ms 0x8000421c#64 R3 (InExt (s.toNat - 176, 176)) M3 ∗
      stackScratch (execSP s) (execNeed (.ifStmt c t (some e)) d - 176) ∗ slot24 aRet.toNat ∗
      world N L Room inp .uncounted st' d ∗
      IfKP (live := live) (N := N) (L := L) (Room := Room) (inp := inp) Φ Core st d env
        (.ifStmt c t (some e)) aRet s R ret v8 v9 v18 v19
    ⊢ (wpW (vsaModel live)).W Φ := by
  obtain ⟨pc, pt, pe, hn⟩ := hr.node
  obtain ⟨her, hne⟩ := hn.elsRepr e rfl
  have hle : execNeed e d ≤ execNeed (.ifStmt c t (some e)) d := by
    have := execNeed_if_else c t e d; unfold execFrame at this; omega
  iintro ⟨#IH, #Hcode, #Hro, #Hfb, Hms, Hst, Hslot, Hw, HK⟩
  ihave HX := execDispsP_at Core st' d env e $$ IH
  ihave #Hdv := roOwn_data hn.node.view $$ [$]
  iapply wp_swpF_later (X := execDispP_body (vsaModel live) N L Room inp Core st' d env e)
  rotate_left
  · icombine Hcode Hro Hfb Hst Hslot Hw HK as HF; isplitl []; iexact Hdv; iframe HF HX Hms
  intro F'
  refine IfArm_runF (aE := BitVec.ofNat 64 pe) hlive hn.node.lo hn.node.hi hn.node.off
    ((hr.keep 8 (by decide)).trans hf.regs.s0) (by rw [hr.a0, hv]; rfl) hn.els hne ?_
    (fun _ h => absurd hne h)
  intros
  apply swp_closeRM_ne _ (by decide)
  intro R4 M4 hR4 hM4
  have hk4 : KeepRegs [20, 21, 22, 23, 24, 25, 26, 27] R R4 := by
    subst hR4
    repeat (first | exact hr.keep.sub (by decide) | refine KeepRegs.upd ?_ (by decide) _)
  have hdr : DispRegs R4 (BitVec.ofNat 64 inp) (BitVec.ofNat 64 pe) aE aRet s := by
    subst hR4
    exact if_dispRegs hf.regs hr.keep (by ix_reg) (by ix_reg) (by ix_reg) (by ix_reg) (by ix_reg)
      (by ix_reg) (by ix_reg)
  unfold F'
  iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, HK⟩, HX⟩, Hms⟩
  iapply ifBranchP hf.stack hle hk4 (fun st'' status h => ExecS.ifFalse st d env c t e st' st'' v
    status hEc hv h) ⟨hdr, hM4 ▸ hr.saved, hf.ral, hf.stack.narrow hle, hf.slot,
      (if_bodies hf.bodies).2 e rfl⟩
  unfold execDispPC
  iframe HX Hms Hcode Hfb Hst Hslot Hw HK
  imodintro
  unfold astSG
  iexists P, m
  iframe Hro
  ipureintro; exact ⟨by rw [hn.elsNat]; exact her, hr.geo⟩

end Partial

end VsaIris.Interp
