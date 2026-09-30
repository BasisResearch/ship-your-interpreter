import VsaIris.Interp.BinPrelude

/-!
The partial (abort-aware) binary prelude: `binPreludeP` runs both children through the
recursive `evalSpecsP` hypothesis and hands the operator tail its `ExitK` for every
semantically produced value and its `AbortK`.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

/-- The caller continuation of a partial `eval_expr` spec. -/
abbrev evalKP (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (inp : Nat) (Core : IProp GF)
    (st : St) (d env : Nat) (e : Expr) (sret s ret : BitVec 64) (rv : Nat → BitVec 64)
    (Φ : Nat × String → IProp GF) : IProp GF :=
  iprop((PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ (∃ st' v, ⌜EvalE st d env e st' v⌝ ∗
      evalPost N L Room inp .uncounted st' d e v sret s rv) -∗ (wpW (vsaModel live)).W Φ) ∧
    (abortAt Core s (evalNeed e d) ∗ slot24 sret.toNat -∗ (wpW (vsaModel live)).W Φ))

/-- The tail's view of the partial prelude: the operands' derivations, the state at the
dispatch, the exit for every value the operator semantics produces, and the abort. -/
abbrev BinTailP (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (inp : Nat) (Core : IProp GF)
    (st : St) (d env : Nat) (op : BinOp) (l r : Expr) : Prop :=
  ∀ (Φ : Nat × String → IProp GF) (sret aE aX s ret : BitVec 64) (rv R : Nat → BitVec 64)
    (P : Nat → Prop) (m Mt : Mem) (w0 w1 w2 u0 u1 u2 : BitVec 64) (st1 st2 : St) (lv rv' : Value)
    (K : IProp GF),
    EvalE st d env l st1 lv → EvalE st1 d env r st2 rv' →
    ArmGeo s ret sret (evalNeed (.binary op l r) d) → BinOpNode m P aX (binOpTok op) →
    BinMid s sret (BitVec.ofNat 64 inp) rv R Mt ret aX lv rv' w0 w1 w2 u0 u1 u2 →
    (∀ v, binOpSem st2.store op lv rv' = some v →
      ExitK (wpW (vsaModel live)) Φ N s ret sret rv (evalNeed (.binary op l r) d) v
        (world N L Room inp .uncounted st2 d) K) →
    AbortK (wpW (vsaModel live)) Φ inp Core s sret (evalNeed (.binary op l r) d) K →
    BinTail (wpW (vsaModel live)) Φ N
      (binArmF N P m env aE s (evalNeed (.binary op l r) d) sret
        (world N L Room inp .uncounted st2 d) K) R s Mt lv rv' w0 w1 w2 u0 u1 u2

theorem binPreludeP_R (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat} {Core : IProp GF}
    {st st1 : St} {d env : Nat} {op : BinOp} {l r : Expr} {lv : Value}
    (tail : BinTailP (GF := GF) (live := live) N L Room inp Core st d env op l r)
    (hEl : EvalE st d env l st1 lv)
    {Φ : Nat × String → IProp GF} {sret aE aX s ret : BitVec 64}
    {rv R : Nat → BitVec 64} {P : Nat → Prop} {m Mt : Mem} {w0 w1 w2 : BitVec 64} {aR : Nat}
    (g : ArmGeo s ret sret (evalNeed (.binary op l r) d)) (hn : BinOpNode m P aX (binOpTok op))
    (hR : BinRight m P aX r aR) (hbr : r.bodiesBound perCallBudget = true)
    (b : BinLeft s sret (BitVec.ofNat 64 inp) aE rv R Mt ret aX lv w0 w1 w2) :
    ArmAt (wpW (vsaModel live)) Φ
      (evalArmF P m env aE (evalSP s) (evalNeed (.binary op l r) d - 1088) (slot24 sret.toNat)
        (world N L Room inp .uncounted st1 d)
        iprop(evalKP (live := live) N L Room inp Core st d env (.binary op l r) sret s ret rv Φ ∗
          evalSpecsP (vsaModel live) N L Room inp Core ∗ errCtx inp ∗ □ valOf N lv w0 w1 w2))
      0x800034fc#64 R (InExt (s.toNat - 1088, 1088)) Mt := by
  have hsf := g.sf; have hs' := g.lo; have hs2 := g.hi; have hs3 := g.al
  have hx1 := hn.lo; have hx2 := hn.hi; have hx3 := hn.off
  have hoff := g.off
  have hneed := g.need
  have gR := evalCallGeom (o := 144) g.sg
    (by have := evalNeed_binary_right op l r d; unfold evalFrame at this; omega) (by decide) (by decide)
  have htl' : w0.toNat % 2 ^ 32 < 2 ^ 31 := by rw [b.tl]; exact valTag_lt _
  refine ArmAt.seg (wpW _) hn.view ?_
  refine BinaryAddIntT_run2 (aE := aE) (inp := BitVec.ofNat 64 inp) (w1 := w1)
    (kL := BitVec.ofNat 64 (w0.toNat % 2 ^ 32)) hlive hsf hs' hs2 hs3 hx1 hx2 hx3
    b.r8 b.r2 b.r18 hR.ptr b.ae b.kl b.l1 ?_
  intros
  apply swp_closeM
  intro Mt2 hMt2
  unfold evalArmF
  iintro ⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, Hk, #IH, #HE, #Hv1⟩, Hms⟩
  ihave Hr := evalSpecsP_at Core st1 d env r $$ IH
  iapply ms_callEvalP (N := N) (L := L) (Room := Room) (inp := inp) (i := 0x80003518)
    (jalx_80003518 live (fun p hp => hlive _ (interp_code_80003518 p hp)))
    interp_code_80003518 (by decide) (Core := Core) (st := st1) (d := d) (env := env) (e := r)
    (slot := s + 18446744073709550528#64 + 144#64) (aC := BitVec.ofNat 64 aR) (aE := aE)
    (s0 := s) (sret0 := sret) (m := evalNeed (.binary op l r) d - 1088)
    (n0 := evalNeed (.binary op l r) d) (Out := slot24 sret.toNat)
    (Kret := iprop(PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ (∃ st' v, ⌜EvalE st d env (.binary op l r) st' v⌝ ∗
          evalPost N L Room inp .uncounted st' d (.binary op l r) v sret s rv) -∗
          (wpW (vsaModel live)).W Φ)) .rfl
    gR.child gR.fits gR.below (by omega) g.sg.le gR.slotGeom hbr
  iframe Hr Hcode Hfb Hms Hst Hw Hslot Hk
  isplitl []
  · ipureintro
    refine ⟨⟨by ix_reg, by ix_reg, by ix_reg, by ix_reg, by ix_reg; exact b.r2⟩, fun b hb => ?_⟩
    have g1 := gR.slot; have g2 := gR.sp; simp only [VsaIris.InExt, evalSP] at hb g1 g2 ⊢; omega
  isplitl []
  · imodintro
    rw [show (BitVec.ofNat 64 aR).toNat = aR by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hR.lt]]
    iapply astEG_of_view hR.repr hR.ok $$ Hro
  iintro %R2 %u0 %u1 %u2 %st2 %rv' %hEr %hkeep2 #Hv2 Hms Hst Hw Hslot Hk
  ihave %htr := valOf_tag N rv' u0 u1 u2 $$ Hv2
  subst hMt2
  have ht := tail Φ sret aE aX s ret rv _ P m _ w0 w1 w2 u0 u1 u2 st1 st2 lv rv'
    iprop(evalKP (live := live) N L Room inp Core st d env (.binary op l r) sret s ret rv Φ ∗ errCtx inp) hEl hEr
    g hn (binMid_of_left g b (by ix_keep [hkeep2]; exact b.r9) (by ix_keep [hkeep2]) hkeep2 htr)
    (fun v hv R' hkeep => by
      iintro ⟨Hpc, Hra, Hregs, Hst, Hval, Hw, Hk, -⟩
      ihave Hk := and_elim_l $$ Hk
      iapply Hk $$ Hpc Hra
      iexists st2, v
      isplitl []
      · ipureintro; exact EvalE.binary st d env op l r st1 st2 lv rv' v hEl hEr hv
      unfold evalPost
      iexists R'
      iframe Hregs Hst Hval Hw
      ipureintro; exact hkeep)
    (by
      unfold AbortK
      iintro ⟨Hk, #HE⟩
      iframe HE
      iapply and_elim_r $$ Hk)
  unfold BinTail at ht
  iapply ht
  iframe Hv1 Hv2 Hms; unfold binArmF evalArmF; iframe Hcode Hro Hfb Hst Hslot Hw Hk; iexact HE

theorem binPreludeP (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat} {Core : IProp GF}
    {st : St} {d env : Nat} {op : BinOp} {l r : Expr}
    (tail : BinTailP (GF := GF) (live := live) N L Room inp Core st d env op l r) :
    evalSpecsP (GF := GF) (vsaModel live) N L Room inp Core ∗ errCtx inp ⊢
      evalSpecP_body (vsaModel live) N L Room inp Core st d env (.binary op l r) := by
  iintro ⟨#IH, #HE⟩
  unfold evalSpecP_body fnSpecAbort
  iintro %sret %aE %aX %s %rv !> %ret %Φ Hpc Hra ⟨%hal, Hpre⟩ Hk
  unfold evalPre
  icases Hpre with ⟨Hregs, %hregs, #Hcode, #Hast, #Hfb, Hst, %hsg, Hslot, %hslg, %hbb, Hw⟩
  unfold astEG
  icases Hast with ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩
  obtain ⟨aL, aR, hn, hrl, hrr, haL, haR⟩ := binNode_of_repr hrepr hgeo
  have hneed : 1088 ≤ evalNeed (.binary op l r) d := by
    have := Expr.stackNeed_ge (.binary op l r); unfold evalNeed stackBudget; unfold evalFrame at this; omega
  have hs := hsg.lo; have hs2 := hsg.hi; have hs3 := hsg.al; have hs4 := hsg.le
  unfold Vsa.Sim.LayoutInstance.stackSL at hs hs2
  simp only at hs hs2
  have hs' : 0x87800000 + 1088 ≤ s.toNat := by omega
  have hsF : s - 1088#64 = s + 18446744073709550528#64 := evalSP_eq s
  have hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088 := by
    rw [← hsF]; exact toNat_sub_frame (by simp only [BitVec.toNat_ofNat]; omega)
  have gL := evalCallGeom (o := 120) hsg
    (by have := evalNeed_binary_left op l r d; unfold evalFrame at this; omega) (by decide) (by decide)
  have hbl : l.bodiesBound perCallBudget = true := by
    simp only [Expr.bodiesBound, Bool.and_eq_true] at hbb; exact hbb.1
  have hbr : r.bodiesBound perCallBudget = true := by
    simp only [Expr.bodiesBound, Bool.and_eq_true] at hbb; exact hbb.2
  have hLt : (BitVec.ofNat 64 aL).toNat = aL := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt haL]
  have hx1 := hn.lo; have hx2 := hn.hi; have hx3 := hn.off
  have hoff := evalSP_off (s := s) hsf (by omega)
  have geo : ArmGeo s ret sret (evalNeed (.binary op l r) d) :=
    ⟨hsf, hs', hs2, hs3, hsg, hneed, hal, hslg⟩
  have node : BinOpNode m P aX (binOpTok op) := ⟨hn.op, hn.view, hx1, hx2, hx3⟩
  ihave ⟨Hst, HF⟩ := stackScratch_frame (f := 1088#64) hsg.le hneed $$ Hst
  rw [hsF, hsf, show (1088#64).toNat = 1088 from rfl]
  ihave ⟨%Mt0, Hms⟩ := ms_intro $$ [Hpc Hra Hregs HF]
  · iframe Hpc Hra Hregs; unfold blockOwn; iexact HF
  iapply ArmAt.seg (wpW _) (Out := slot24 sret.toNat)
    (Wd := world N L Room inp .uncounted st d)
    (K := iprop(evalKP (live := live) N L Room inp Core st d env (.binary op l r) sret s ret rv Φ ∗
      evalSpecsP (vsaModel live) N L Room inp Core ∗ errCtx inp)) hn.view
  rotate_left
  · iframe Hms; unfold evalArmF; iframe Hcode Hro Hfb Hst Hslot Hw Hk IH; iexact HE
  unfold evalEntryPC
  refine BinaryAddIntT_run1 hlive hsf hs' hs2 hs3 hx1 hx2 hx3 (by ix_reg; exact hregs.a0)
    (by ix_reg; exact hregs.a1) (by ix_reg; exact hregs.a2) (by ix_reg; exact hregs.a3)
    (by ix_reg; exact hregs.sp) hn.kind hn.kindu ?_
  intros
  apply swp_closeM
  intro Mt1 hMt1
  have hsv1 : EvalSaved Mt1 s ret (rv 8) (rv 9) (rv 18) (rv 19) := by
    subst hMt1; constructor <;> (ix_fwd using [hoff]; ix_reg)
  have hA1 : ldv .ld Mt1 (s.toNat - 1088) = aE := by subst hMt1; ix_fwd
  unfold evalArmF
  iintro ⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, Hk, #IH, #HE⟩, Hms⟩
  ihave Hl := evalSpecsP_at Core st d env l $$ IH
  iapply ms_callEvalP (N := N) (L := L) (Room := Room) (inp := inp) (i := 0x800034f8)
    (jalx_800034f8 live (fun p hp => hlive _ (interp_code_800034f8 p hp)))
    interp_code_800034f8 (by decide) (Core := Core) (st := st) (d := d) (env := env) (e := l)
    (slot := s + 18446744073709550528#64 + 120#64) (aC := BitVec.ofNat 64 aL) (aE := aE)
    (s0 := s) (sret0 := sret) (m := evalNeed (.binary op l r) d - 1088)
    (n0 := evalNeed (.binary op l r) d) (Out := slot24 sret.toNat)
    (Kret := iprop(PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ (∃ st' v, ⌜EvalE st d env (.binary op l r) st' v⌝ ∗
          evalPost N L Room inp .uncounted st' d (.binary op l r) v sret s rv) -∗
          (wpW (vsaModel live)).W Φ)) .rfl
    gL.child gL.fits gL.below (by omega) hsg.le gL.slotGeom hbl
  iframe Hl Hcode Hfb Hms Hst Hw Hslot Hk
  isplitl []
  · ipureintro
    refine ⟨⟨by ix_reg, by ix_reg; exact hregs.a1, by ix_reg; exact hn.left,
      by ix_reg; exact hregs.a3, by ix_reg⟩, fun b hb => ?_⟩
    have g1 := gL.slot; have g2 := gL.sp; simp only [VsaIris.InExt, evalSP] at hb g1 g2 ⊢; omega
  isplitl []
  · imodintro; rw [hLt]; iapply astEG_of_view hrl hgeo $$ Hro
  iintro %R1 %w0 %w1 %w2 %st1 %lv %hEl %hkeep1 #Hv1 Hms Hst Hw Hslot Hk
  ihave %htl := valOf_tag N lv w0 w1 w2 $$ Hv1
  have htl' : w0.toNat % 2 ^ 32 < 2 ^ 31 := by rw [htl]; exact valTag_lt _
  have bl : BinLeft s sret (BitVec.ofNat 64 inp) aE rv (upd R1 1 (BitVec.ofNat 64 (0x800034f8 + 4)))
      (slotWrite Mt1 (s + 18446744073709550528#64 + 120#64).toNat w0 w1 w2) ret aX lv w0 w1 w2 := {
    r2 := by ix_keep [hkeep1]
    r8 := by ix_keep [hkeep1]
    r9 := by ix_keep [hkeep1]
    r18 := by ix_keep [hkeep1]
    hi := fun x hx => by
      simp only [hiSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_keep [hkeep1]
    sp := hregs.sp
    saved := by ix_saved hsv1 using hoff
    ae := by ix_fwd; exact hA1
    kl := by ix_fwd
    l0 := by ix_fwd
    l1 := by ix_fwd
    l2 := by ix_fwd
    tl := htl }
  iapply binPreludeP_R hlive tail hEl geo node ⟨hn.right, hrr, haR, hgeo⟩ hbr bl
  iframe Hms; unfold evalArmF; iframe Hcode Hro Hfb Hst Hslot Hw Hk IH HE; iexact Hv1

end

end VsaIris.Interp
