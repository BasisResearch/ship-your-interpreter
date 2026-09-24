import VsaIris.Interp.Case.BinaryAddIntT
{IMPORTS}import VsaIris.Interp.ErrArm
import VsaIris.Interp.BinArm

/-!
# `{ARM}`, partial mode (family `binP`, INTERP_DESIGN.md §6, §4.2; lane E2)

`caseP_{ARM}`: from the Löb hypothesis `evalSpecsP` and the error context
`errCtx`, `eval_expr` on `.binary {OP} l r` meets its partial,
outcome-quantified spec, for EVERY outcome of the operands: the case has no
exported branch. The children are called through the Löb hypothesis
(`ms_callEvalP`); after both return, the case splits on their actual kinds
({ROWSDOC}), and `#ix_tree` joins the rows. A success row runs as in total mode
(the same run lemmas) and ends with `EvalE.binary`; an error row calls
`value_kind_name` and `runtime_error` (`ms_rtErrEval`: the arm aborts with
`abortAt Core s n ∗ slot24 sret`). Template:
`scripts/iris_arms/templates/binP_*.lean`.
-/

namespace VsaIris.Interp
open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim
open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr VsaIris.Newlib

{RUNS}
#ix_piece {ARM}P_p1 {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat} {Core : IProp GF}
    {st : St} {d env : Nat} {l r : Expr}
{HYPS}    evalSpecsP (GF := GF) (vsaModel live) N L Room inp Core ∗ errCtx inp{LHSX} ⊢
      evalSpecP_body (GF := GF) (vsaModel live) N L Room inp Core st d env (.binary {OP} l r) by
  iintro ⟨#IH, #HE{INTROX}⟩
  unfold evalSpecP_body fnSpecAbort
  iintro %sret %aE %aX %s %rv !> %ret %Φ Hpc Hra ⟨%hal, Hpre⟩ Hk
  unfold evalPre
  icases Hpre with ⟨Hregs, %hregs, #Hcode, #Hast, #Hfb, Hst, %hsg, Hslot, %hslg, %hbb, Hw⟩
  unfold astEG
  icases Hast with ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩
  obtain ⟨aL, aR, hn, hrl, hrr, haL, haR⟩ := binNode_of_repr hrepr hgeo
  have hneed : 1088 ≤ evalNeed (.binary {OP} l r) d := by
    have := Expr.stackNeed_ge (.binary {OP} l r); unfold evalNeed stackBudget; unfold evalFrame at this; omega
  have hs := hsg.lo; have hs2 := hsg.hi; have hs3 := hsg.al; have hs4 := hsg.le
  unfold Vsa.Sim.LayoutInstance.stackSL at hs hs2
  simp only at hs hs2
  have hs' : 0x87800000 + 1088 ≤ s.toNat := by omega
  have hsF : s - 1088#64 = s + 18446744073709550528#64 := evalSP_eq s
  have hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088 := by
    rw [← hsF]; exact toNat_sub_frame (by simp only [BitVec.toNat_ofNat]; omega)
  have gL := evalCallGeom (o := 120) hsg
    (by have := evalNeed_binary_left {OP} l r d; unfold evalFrame at this; omega) (by decide) (by decide)
  have gR := evalCallGeom (o := 144) hsg
    (by have := evalNeed_binary_right {OP} l r d; unfold evalFrame at this; omega) (by decide) (by decide)
  have hbl : l.bodiesBound perCallBudget = true := by
    simp only [Expr.bodiesBound, Bool.and_eq_true] at hbb; exact hbb.1
  have hbr : r.bodiesBound perCallBudget = true := by
    simp only [Expr.bodiesBound, Bool.and_eq_true] at hbb; exact hbb.2
  have hLt : (BitVec.ofNat 64 aL).toNat = aL := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt haL]
  have hRt : (BitVec.ofNat 64 aR).toNat = aR := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt haR]
  have hx1 := hn.lo; have hx2 := hn.hi; have hx3 := hn.off
  have hoff := evalSP_off (s := s) hsf (by omega)
  ihave ⟨Hst, HF⟩ := stackScratch_frame (f := 1088#64) hsg.le hneed $$ Hst
  rw [hsF, hsf, show (1088#64).toNat = 1088 from rfl]
  ihave ⟨%Mt0, Hms⟩ := ms_intro $$ [Hpc Hra Hregs HF]
  · iframe Hpc Hra Hregs; unfold blockOwn; iexact HF
  -- run 1
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (wpW _) (F := iprop(evalArmF P m env aE (s + 18446744073709550528#64)
      (evalNeed (.binary {OP} l r) d - 1088) (slot24 sret.toNat)
      (world N L Room inp .uncounted st d)
      iprop((PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ (∃ st' v, ⌜EvalE st d env (.binary {OP} l r) st' v⌝ ∗
          evalPost N L Room inp .uncounted st' d (.binary {OP} l r) v sret s rv) -∗
          (wpW (vsaModel live)).W Φ) ∧
        (abortAt Core s (evalNeed (.binary {OP} l r) d) ∗ slot24 sret.toNat -∗
          (wpW (vsaModel live)).W Φ)) ∗
      evalSpecsP (vsaModel live) N L Room inp Core ∗ errCtx inp))
  rotate_left
  · unfold evalArmF; iframe Hdv Hms; isplitr [IH HE]
    · iframe Hcode Hro Hfb Hst Hslot Hw; iexact Hk
    · iframe IH; iexact HE
  intro F'
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
  unfold F' evalArmF
  iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, Hk⟩, #IH, #HE⟩, Hms⟩
  -- the left child, through the Löb hypothesis
  ihave Hl := evalSpecsP_at Core st d env l $$ IH
  iapply ms_callEvalP (N := N) (L := L) (Room := Room) (inp := inp) (i := 0x800034f8)
    (jalx_800034f8 live (fun p hp => hlive _ (interp_code_800034f8 p hp)))
    interp_code_800034f8 (by decide) (Core := Core) (st := st) (d := d) (env := env) (e := l)
    (slot := s + 18446744073709550528#64 + 120#64) (aC := BitVec.ofNat 64 aL) (aE := aE)
    (s0 := s) (sret0 := sret) (m := evalNeed (.binary {OP} l r) d - 1088)
    (n0 := evalNeed (.binary {OP} l r) d) (Out := slot24 sret.toNat)
    (Kret := iprop(PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ (∃ st' v, ⌜EvalE st d env (.binary {OP} l r) st' v⌝ ∗
          evalPost N L Room inp .uncounted st' d (.binary {OP} l r) v sret s rv) -∗
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
  ihave #Hv1c := Hv1
  ihave %htl := valOf_tag N lv w0 w1 w2 $$ Hv1c
  have htl' : w0.toNat % 2 ^ 32 < 2 ^ 31 := by rw [htl]; cases lv <;> simp [valTag]

#ix_piece {ARM}P_p2 from {ARM}P_p1 by
  -- run 2: stage the right child
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (wpW _) (F := iprop(evalArmF P m env aE (s + 18446744073709550528#64)
      (evalNeed (.binary {OP} l r) d - 1088) (slot24 sret.toNat)
      (world N L Room inp .uncounted st1 d)
      iprop((PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ (∃ st' v, ⌜EvalE st d env (.binary {OP} l r) st' v⌝ ∗
          evalPost N L Room inp .uncounted st' d (.binary {OP} l r) v sret s rv) -∗
          (wpW (vsaModel live)).W Φ) ∧
        (abortAt Core s (evalNeed (.binary {OP} l r) d) ∗ slot24 sret.toNat -∗
          (wpW (vsaModel live)).W Φ)) ∗
      evalSpecsP (vsaModel live) N L Room inp Core ∗ errCtx inp ∗ □ valOf N lv w0 w1 w2))
  rotate_left
  · unfold evalArmF; iframe Hdv Hms; isplitr [IH HE Hv1]
    · iframe Hcode Hro Hfb Hst Hslot Hw; iexact Hk
    · iframe IH HE; iexact Hv1
  intro F'
  refine BinaryAddIntT_run2 (aE := aE) (inp := BitVec.ofNat 64 inp) (w1 := w1)
    (kL := BitVec.ofNat 64 (w0.toNat % 2 ^ 32)) hlive hsf hs' hs2 hs3 hx1 hx2 hx3
    ?_ ?_ ?_ hn.right ?_ ?_ ?_ ?_
  · ix_keep [hkeep1]
  · ix_keep [hkeep1]
  · ix_keep [hkeep1]
  · ix_fwd; exact hA1
  · ix_fwd
  · ix_fwd
  intros
  apply swp_closeM
  intro Mt2 hMt2
  have hsv2 : EvalSaved Mt2 s ret (rv 8) (rv 9) (rv 18) (rv 19) := by
    rw [hMt2]; ix_saved hsv1 using hoff
  unfold F' evalArmF
  iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, Hk⟩, #IH, #HE, #Hv1⟩, Hms⟩
  -- the right child, through the Löb hypothesis
  ihave Hr := evalSpecsP_at Core st1 d env r $$ IH
  iapply ms_callEvalP (N := N) (L := L) (Room := Room) (inp := inp) (i := 0x80003518)
    (jalx_80003518 live (fun p hp => hlive _ (interp_code_80003518 p hp)))
    interp_code_80003518 (by decide) (Core := Core) (st := st1) (d := d) (env := env) (e := r)
    (slot := s + 18446744073709550528#64 + 144#64) (aC := BitVec.ofNat 64 aR) (aE := aE)
    (s0 := s) (sret0 := sret) (m := evalNeed (.binary {OP} l r) d - 1088)
    (n0 := evalNeed (.binary {OP} l r) d) (Out := slot24 sret.toNat)
    (Kret := iprop(PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ (∃ st' v, ⌜EvalE st d env (.binary {OP} l r) st' v⌝ ∗
          evalPost N L Room inp .uncounted st' d (.binary {OP} l r) v sret s rv) -∗
          (wpW (vsaModel live)).W Φ)) .rfl
    gR.child gR.fits gR.below (by omega) hsg.le gR.slotGeom hbr
  iframe Hr Hcode Hfb Hms Hst Hw Hslot Hk
  isplitl []
  · ipureintro
    refine ⟨⟨by ix_reg, by ix_reg, by ix_reg, by ix_reg, by ix_keep [hkeep1]⟩, fun b hb => ?_⟩
    have g1 := gR.slot; have g2 := gR.sp; simp only [VsaIris.InExt, evalSP] at hb g1 g2 ⊢; omega
  isplitl []
  · imodintro; rw [hRt]; iapply astEG_of_view hrr hgeo $$ Hro
  iintro %R2 %u0 %u1 %u2 %st2 %rv' %hEr %hkeep2 #Hv2 Hms Hst Hw Hslot Hk
  ihave #Hv2c := Hv2
  ihave %htr := valOf_tag N rv' u0 u1 u2 $$ Hv2c
  have htr' : u0.toNat % 2 ^ 32 < 2 ^ 31 := by rw [htr]; cases rv' <;> simp [valTag]
{SPLIT}
