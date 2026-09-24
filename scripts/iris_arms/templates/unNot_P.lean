import VsaIris.Interp.Case.{ARM}T

/-!
# `{ARM}`, partial mode (family `unNot`, INTERP_DESIGN.md §6, §4.2)

`caseP_{ARM}`: from the Löb hypothesis `evalSpecsP`, `eval_expr` on
`.unary .not e` meets its partial, outcome-quantified spec. The operand is
called through the Löb hypothesis (`ms_callEvalP`); every value it returns
finishes as in total mode (the run lemmas `{ARM}T_run*`) with the derivation
`EvalE.not`. The arm has no error branch.
Template: `scripts/iris_arms/templates/unNot_P.lean`.
-/

namespace VsaIris.Interp
open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim
open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr

#ix_piece {ARM}P_p1 {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat} {Core : IProp GF}
    {st : St} {d env : Nat} {e : Expr}
    (hvt : ⊢ ∀ p v, valueTruthySpec (GF := GF) (vsaModel live) N (wpW (vsaModel live)) p v)
    (hvb : ⊢ ∀ p b, valueBoolSpec (GF := GF) (vsaModel live) N (wpW (vsaModel live)) p b) :
    evalSpecsP (GF := GF) (vsaModel live) N L Room inp Core ⊢
      evalSpecP_body (GF := GF) (vsaModel live) N L Room inp Core st d env (.unary .not e) by
  iintro #IH
  unfold evalSpecP_body fnSpecAbort
  iintro %sret %aE %aX %s %rv !> %ret %Φ Hpc Hra ⟨%hal, Hpre⟩ Hk
  unfold evalPre
  icases Hpre with ⟨Hregs, %hregs, #Hcode, #Hast, #Hfb, Hst, %hsg, Hslot, %hslg, %hbb, Hw⟩
  unfold astEG
  icases Hast with ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩
  obtain ⟨aC, hn, hrc, haC⟩ := unNode_of_repr hrepr hgeo
  have hneed : 1088 ≤ evalNeed (.unary .not e) d := by
    have := Expr.stackNeed_ge (.unary .not e); unfold evalNeed stackBudget; unfold evalFrame at this; omega
  have hs := hsg.lo; have hs2 := hsg.hi; have hs3 := hsg.al; have hs4 := hsg.le
  unfold Vsa.Sim.LayoutInstance.stackSL at hs hs2
  simp only at hs hs2
  have hs' : 0x87800000 + 1088 ≤ s.toNat := by omega
  have hsF : s - 1088#64 = s + 18446744073709550528#64 := evalSP_eq s
  have hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088 := by
    rw [← hsF]; exact toNat_sub_frame (by simp only [BitVec.toNat_ofNat]; omega)
  have gC := evalCallGeom (o := 144) hsg
    (by have := evalNeed_unary .not e d; unfold evalFrame at this; omega) (by decide) (by decide)
  have hbc : e.bodiesBound perCallBudget = true := Expr.bodiesBound_unary hbb
  have hCt : (BitVec.ofNat 64 aC).toNat = aC := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt haC]
  have hx1 := hn.lo; have hx2 := hn.hi; have hx3 := hn.off
  have hoff := evalSP_off (s := s) hsf (by omega)
  ihave ⟨Hst, HF⟩ := stackScratch_frame (f := 1088#64) hsg.le hneed $$ Hst
  rw [hsF, hsf, show (1088#64).toNat = 1088 from rfl]
  ihave ⟨%Mt0, Hms⟩ := ms_intro $$ [Hpc Hra Hregs HF]
  · iframe Hpc Hra Hregs; unfold blockOwn; iexact HF
  -- run 1: prologue, kind dispatch, stage the operand
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (wpW _) (F := iprop(evalArmF P m env aE (s + 18446744073709550528#64)
      (evalNeed (.unary .not e) d - 1088) (slot24 sret.toNat)
      (world N L Room inp .uncounted st d)
      iprop((PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ (∃ st' v', ⌜EvalE st d env (.unary .not e) st' v'⌝ ∗
          evalPost N L Room inp .uncounted st' d (.unary .not e) v' sret s rv) -∗
          (wpW (vsaModel live)).W Φ) ∧
        (abortAt Core s (evalNeed (.unary .not e) d) ∗ slot24 sret.toNat -∗
          (wpW (vsaModel live)).W Φ)) ∗
      evalSpecsP (vsaModel live) N L Room inp Core))
  rotate_left
  · unfold evalArmF; iframe Hdv Hms; isplitr [IH]
    · iframe Hcode Hro Hfb Hst Hslot Hw; iexact Hk
    · iexact IH
  intro F'
  unfold evalEntryPC
  refine {ARM}T_run1 hlive hsf hs' hs2 hs3 hx1 hx2 hx3 (by ix_reg; exact hregs.a0)
    (by ix_reg; exact hregs.a1) (by ix_reg; exact hregs.a2) (by ix_reg; exact hregs.a3)
    (by ix_reg; exact hregs.sp) hn.kind hn.kindu ?_
  intros
  apply swp_closeM
  intro Mt1 hMt1
  have hsv1 : EvalSaved3 Mt1 s ret (rv 8) (rv 9) (rv 18) := by
    subst hMt1; constructor <;> (ix_fwd using [hoff]; ix_reg)
  unfold F' evalArmF
  iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, Hk⟩, #IH⟩, Hms⟩
  -- the operand, through the Löb hypothesis
  ihave He := evalSpecsP_at Core st d env e $$ IH
  iapply ms_callEvalP (N := N) (L := L) (Room := Room) (inp := inp) (i := 0x800035e8)
    (jalx_800035e8 live (fun p hp => hlive _ (interp_code_800035e8 p hp)))
    interp_code_800035e8 (by decide) (Core := Core) (st := st) (d := d) (env := env) (e := e)
    (slot := s + 18446744073709550528#64 + 144#64) (aC := BitVec.ofNat 64 aC) (aE := aE)
    (s0 := s) (sret0 := sret) (m := evalNeed (.unary .not e) d - 1088)
    (n0 := evalNeed (.unary .not e) d) (Out := slot24 sret.toNat)
    (Kret := iprop(PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ (∃ st' v', ⌜EvalE st d env (.unary .not e) st' v'⌝ ∗
          evalPost N L Room inp .uncounted st' d (.unary .not e) v' sret s rv) -∗
          (wpW (vsaModel live)).W Φ)) .rfl
    gC.child gC.fits gC.below (by omega) hsg.le gC.slotGeom hbc
  iframe He Hcode Hfb Hms Hst Hw Hslot Hk
  isplitl []
  · ipureintro
    refine ⟨⟨by ix_reg, by ix_reg; exact hregs.a1, by ix_reg; exact hn.child,
      by ix_reg; exact hregs.a3, by ix_reg⟩, fun b hb => ?_⟩
    have g1 := gC.slot; have g2 := gC.sp; simp only [VsaIris.InExt, evalSP] at hb g1 g2 ⊢; omega
  isplitl []
  · imodintro; rw [hCt]; iapply astEG_of_view hrc hgeo $$ Hro
  iintro %R1 %w0 %w1 %w2 %st1 %v %hE %hkeep1 #Hv1 Hms Hst Hw Hslot Hk


#ix_piece {ARM}P_p2 from {ARM}P_p1 by
  -- run 2: operator test, copy the operand to `sp+64`
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (wpW _) (F := iprop(evalArmF P m env aE (s + 18446744073709550528#64)
      (evalNeed (.unary .not e) d - 1088) (slot24 sret.toNat)
      (world N L Room inp .uncounted st1 d)
      iprop((PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ (∃ st' v', ⌜EvalE st d env (.unary .not e) st' v'⌝ ∗
          evalPost N L Room inp .uncounted st' d (.unary .not e) v' sret s rv) -∗
          (wpW (vsaModel live)).W Φ) ∧
        (abortAt Core s (evalNeed (.unary .not e) d) ∗ slot24 sret.toNat -∗
          (wpW (vsaModel live)).W Φ)) ∗ □ valOf N v w0 w1 w2))
  rotate_left
  · unfold evalArmF; iframe Hdv Hms; isplitr [Hv1]
    · iframe Hcode Hro Hfb Hst Hslot Hw; iexact Hk
    · iexact Hv1
  intro F'
  refine {ARM}T_run2 (aX := aX) (s := s) hlive hsf hs' hs2 hs3 hx1 hx2 hx3 ?_ ?_ hn.op ?_
  · ix_keep [hkeep1]
  · ix_keep [hkeep1]
  intros
  apply swp_closeM
  intro Mt2 hMt2
  have hsv2 : EvalSaved3 Mt2 s ret (rv 8) (rv 9) (rv 18) := by
    rw [hMt2]; ix_saved3 hsv1 using hoff
  unfold F' evalArmF
  iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, Hk⟩, #Hv1⟩, Hms⟩
  -- value_truthy on the copy
  have hc0 : ldv .ld Mt2 (s.toNat - 1088 + 64) = w0 := by rw [hMt2]; ix_fwdF hoff
  have hc8 : ldv .ld Mt2 (s.toNat - 1088 + 72) = w1 := by rw [hMt2]; ix_fwdF hoff
  have hc16 : ldv .ld Mt2 (s.toNat - 1088 + 80) = w2 := by rw [hMt2]; ix_fwdF hoff
  ihave Hvt := hvt $$ %(s + 18446744073709550528#64 + 64#64) %v
  iapply ms_callTruthy (wpW _) (i := 0x80003614)
    (jalx_80003614 live (fun p hp => hlive _ (interp_code_80003614 p hp)))
    interp_code_80003614 (by decide) (S := InExt (s.toNat - 1088, 1088)) ⟨hoff 64 (by decide), rfl, rfl⟩
    (fun b hb => by rw [hoff 64 (by decide)] at hb; simp only [VsaIris.InExt] at hb ⊢; omega)
    ⟨by rw [hoff 64 (by decide)]; omega, by rw [hoff 64 (by decide)]; unfold Vsa.Sim.tohostAddr; omega,
      by rw [hoff 64 (by decide)]; omega⟩
    hc0 hc8 hc16
  iframe Hvt Hcode Hv1 Hms
  isplitl []
  · ipureintro; ix_reg
  iintro %R2 %Mt2' %⟨hkeep2, hbit, hag2⟩ Hms
  have hsv2' : EvalSaved3 Mt2' s ret (rv 8) (rv 9) (rv 18) :=
    hsv2.agree fun a h1 h2 => hag2 a (by simp only [VsaIris.InExt]; omega)
      (by rw [hoff 64 (by decide)]; simp only [VsaIris.InExt]; omega)

#ix_piece {ARM}P_p3 from {ARM}P_p2 by
  -- run 3: `seqz`, stage `value_bool`
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (wpW _) (F := evalArmF P m env aE (s + 18446744073709550528#64)
      (evalNeed (.unary .not e) d - 1088) (slot24 sret.toNat)
      (world N L Room inp .uncounted st1 d)
      iprop((PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ (∃ st' v', ⌜EvalE st d env (.unary .not e) st' v'⌝ ∗
          evalPost N L Room inp .uncounted st' d (.unary .not e) v' sret s rv) -∗
          (wpW (vsaModel live)).W Φ) ∧
        (abortAt Core s (evalNeed (.unary .not e) d) ∗ slot24 sret.toNat -∗
          (wpW (vsaModel live)).W Φ)))
  rotate_left
  · unfold evalArmF; iframe Hdv Hms Hcode Hro Hfb Hst Hslot Hw; iexact Hk
  intro F'
  refine {ARM}T_run3 (aX := aX) (s := s) hlive hsf hs' hs2 hs3 ?_
  apply swp_closeM
  intro Mt3 hMt3
  have hsv3 : EvalSaved3 Mt3 s ret (rv 8) (rv 9) (rv 18) := by rw [hMt3]; exact hsv2'
  unfold F' evalArmF
  iintro ⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, Hk⟩, Hms⟩
  -- value_bool
  ihave Hvb := hvb $$ %sret %(seqzV (if v.truthy then 1#64 else 0#64))
  unfold valueBoolSpec
  iapply ms_callHelper (wpW _) (i := 0x80003620)
    (jalx_80003620 live (fun p hp => hlive _ (interp_code_80003620 p hp)))
    interp_code_80003620 (by decide)
  iframe Hvb Hcode Hms
  isplitl []
  · ipureintro; exact ⟨by ix_keep [hkeep2, hkeep1], by ix_reg; rw [hbit]⟩
  isplitl [Hslot]
  · iframe Hslot; ipureintro; exact hslg
  iintro %R3 %hkeep3 Hval Hms
  rw [seqzBit_ne]

#ix_piece {ARM}P_p4 from {ARM}P_p3 by
  -- run 4: the epilogue
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (wpW _) (F := evalArmF P m env aE (s + 18446744073709550528#64)
      (evalNeed (.unary .not e) d - 1088) (valAt N sret.toNat (.bool (!v.truthy)))
      (world N L Room inp .uncounted st1 d)
      iprop((PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ (∃ st' v', ⌜EvalE st d env (.unary .not e) st' v'⌝ ∗
          evalPost N L Room inp .uncounted st' d (.unary .not e) v' sret s rv) -∗
          (wpW (vsaModel live)).W Φ) ∧
        (abortAt Core s (evalNeed (.unary .not e) d) ∗ slot24 sret.toNat -∗
          (wpW (vsaModel live)).W Φ)))
  rotate_left
  · unfold evalArmF; iframe Hdv Hms Hcode Hro Hfb Hst Hval Hw; iexact Hk
  intro F'
  refine {ARM}T_run4 (aX := aX) (s := s) (ret := ret) (v8 := rv 8) (v9 := rv 9)
    (v18 := rv 18) hlive hsf hs' hs2 hs3 hal ?_ ?_ ?_ ?_ ?_ ?_
  · ix_keep [hkeep3, hkeep2, hkeep1]
  · rw [hoff _ (by decide)]; exact hsv3.ra
  · rw [hoff _ (by decide)]; exact hsv3.s0
  · rw [hoff _ (by decide)]; exact hsv3.s1
  · rw [hoff _ (by decide)]; exact hsv3.s2
  intros
  apply swp_closeF
  unfold F' evalArmF
  iintro ⟨⟨#Hcode, #Hro, #Hfb, Hst, Hval, Hw, Hk⟩, Hms⟩
  ihave ⟨Hpc, Hra, Hregs, HS⟩ := ms_exit $$ Hms
  ihave Hst := evalFrame_join hsg.le hneed $$ [Hst HS]
  · iframe Hst HS
  ihave Hra := ptsto_eq (show _ = ret by ix_reg) $$ Hra
  ihave Hk := and_elim_l $$ Hk
  iapply Hk $$ Hpc Hra
  iexists st1, (.bool (!v.truthy))
  isplitl []
  · ipureintro; exact EvalE.not st d env e st1 v hE
  unfold evalPost
  iexists _
  iframe Hregs Hst Hval Hw
  ipureintro
  intro x hx
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · ix_reg; exact evalSP_restore s |>.trans hregs.sp.symm
  all_goals ix_keep [hkeep3, hkeep2, hkeep1]

#ix_chain caseP_{ARM} := [{ARM}P_p1, {ARM}P_p2, {ARM}P_p3, {ARM}P_p4]

end VsaIris.Interp
