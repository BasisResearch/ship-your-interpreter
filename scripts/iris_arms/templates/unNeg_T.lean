import VsaIris.Interp.ArmLogical

/-!
# `{ARM}`, total mode (family `unNeg`, INTERP_DESIGN.md §6)

`caseT_{ARM}`: `eval_expr` on `.unary .neg e` over an int operand meets its
total, derivation-indexed spec, given the operand's spec and `value_int`'s
spec. Three symbolic runs (`#ix_seg`): prologue and operand; the operator
test, the int kind test and the negation (the node's line is a havoc load);
the epilogue. The glue in three pieces (`#ix_piece`, split at the calls),
assembled by `#ix_chain`. Template: `scripts/iris_arms/templates/unNeg_T.lean`.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim

#ix_seg {ARM}T_run1 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s aE inp sret : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aX.toNat) (hx2 : aX.toNat + 24 ≤ 0x100000000)
    (hx3 : aX.toNat + 24 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aX.toNat)
    (h10 : R 10 = sret) (h11 : R 11 = inp) (h12 : R 12 = aX) (h13 : R 13 = aE) (h2 : R 2 = s)
    (hk : ldv .lw m aX.toNat = 8#64) (hku : ldv .lwu m aX.toNat = 8#64) :
    IW live m (unView aX.toNat) (InExt (s.toNat - 1088, 1088)) Q 0x80003164#64 R Mt
  by ix_run hlive using [h10, h11, h12, h13, h2, hk, hku, hsf] at 0x800035e8

#ix_seg {ARM}T_run2 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s sret : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aX.toNat) (hx2 : aX.toNat + 24 ≤ 0x100000000)
    (hx3 : aX.toNat + 24 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aX.toNat)
    (h8 : R 8 = aX) (h2 : R 2 = s + 18446744073709550528#64) (h9 : R 9 = sret)
    (hop : ldv .lw m (aX + 8#64).toNat = 12#64)
    (hK : ldv .lw Mt (s + 18446744073709550528#64 + 144#64).toNat = 2#64) :
    IW live m (unView aX.toNat) (InExt (s.toNat - 1088, 1088)) Q 0x800035ec#64 R Mt
  by ix_run hlive using [h8, h2, h9, hop, hK, hsf] at 0x800039d8

#ix_seg {ARM}T_run3 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s ret v8 v9 v18 : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hal : ret.toNat % 4 = 0)
    (h2 : R 2 = s + 18446744073709550528#64)
    (hRA : ldv .ld Mt (s + 18446744073709550528#64 + 1080#64).toNat = ret)
    (hS0 : ldv .ld Mt (s + 18446744073709550528#64 + 1072#64).toNat = v8)
    (hS1 : ldv .ld Mt (s + 18446744073709550528#64 + 1064#64).toNat = v9)
    (hS2 : ldv .ld Mt (s + 18446744073709550528#64 + 1056#64).toNat = v18) :
    IW live m (unView aX.toNat) (InExt (s.toNat - 1088, 1088)) Q 0x800039dc#64 R Mt
  by ix_run hlive using [h2, hRA, hS0, hS1, hS2, hsf, hal]

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr

#ix_piece {ARM}T_p1 {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {st st1 : St} {d env : Nat} {e : Expr} {a : Int} {n : Nat}
    (De : EvalECost st d env e st1 (.int a) n)
    (D : EvalECost st d env (.unary .neg e) st1 (.int (wrap64 (-a))) n)
    (he : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env e st1 (.int a) n De)
    (hvi : ⊢ ∀ p n, valueIntSpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) p n) :
    ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env (.unary .neg e) st1
        (.int (wrap64 (-a))) n D by
  unfold evalSpecT_body fnSpecW
  iintro %k %sret %aE %aX %s %rv !> %ret %Φ Hpc Hra ⟨%hal, Hpre⟩ Hk
  unfold evalPre
  icases Hpre with ⟨Hregs, %hregs, #Hcode, #Hast, #Hfb, Hst, %hsg, Hslot, %hslg, %hbb, Hw⟩
  unfold astEG
  icases Hast with ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩
  obtain ⟨aC, hn, hrc, haC⟩ := unNode_of_repr hrepr hgeo
  have hneed : 1088 ≤ evalNeed (.unary .neg e) d := by
    have := Expr.stackNeed_ge (.unary .neg e); unfold evalNeed stackBudget; unfold evalFrame at this; omega
  have hs := hsg.lo; have hs2 := hsg.hi; have hs3 := hsg.al; have hs4 := hsg.le
  unfold Vsa.Sim.LayoutInstance.stackSL at hs hs2
  simp only at hs hs2
  have hs' : 0x87800000 + 1088 ≤ s.toNat := by omega
  have hsF : s - 1088#64 = s + 18446744073709550528#64 := evalSP_eq s
  have hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088 := by
    rw [← hsF]; exact toNat_sub_frame (by simp only [BitVec.toNat_ofNat]; omega)
  have gC := evalCallGeom (o := 144) hsg
    (by have := evalNeed_unary .neg e d; unfold evalFrame at this; omega) (by decide) (by decide)
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
  iapply wp_swpF (twpW _) (F := evalArmF P m env aE (s + 18446744073709550528#64)
      (evalNeed (.unary .neg e) d - 1088) (slot24 sret.toNat)
      (world N L Room inp (.counted (k + n)) st d)
      iprop(PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ evalPost N L Room inp (.counted k) st1 d (.unary .neg e)
        (.int (wrap64 (-a))) sret s rv -∗ (twpW (vsaModel live)).W Φ))
  rotate_left
  · unfold evalArmF; iframe Hdv Hms Hcode Hro Hfb Hst Hslot Hw; iexact Hk
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
  iintro ⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, Hk⟩, Hms⟩
  -- the operand
  ihave He := he
  iapply ms_callEvalT (N := N) (L := L) (Room := Room) (inp := inp) (i := 0x800035e8)
    (jalx_800035e8 live (fun p hp => hlive _ (interp_code_800035e8 p hp)))
    interp_code_800035e8 (by decide) De (k := k) (slot := s + 18446744073709550528#64 + 144#64)
    (aC := BitVec.ofNat 64 aC) (aE := aE) (s := s + 18446744073709550528#64)
    (m := evalNeed (.unary .neg e) d - 1088)
    gC.child gC.fits gC.below gC.slotGeom hbc
  iframe He Hcode Hfb Hms Hst Hw
  isplitl []
  · ipureintro
    refine ⟨⟨by ix_reg, by ix_reg; exact hregs.a1, by ix_reg; exact hn.child,
      by ix_reg; exact hregs.a3, by ix_reg⟩, fun b hb => ?_⟩
    have g1 := gC.slot; have g2 := gC.sp; simp only [VsaIris.InExt, evalSP] at hb g1 g2 ⊢; omega
  isplitl []
  · imodintro; rw [hCt]; iapply astEG_of_view hrc hgeo $$ Hro
  iintro %R1 %w0 %w1 %w2 %hkeep1 #Hv1 Hms Hst Hw
  unfold valOf
  icases Hv1 with %⟨hw0, hw1⟩
  have hk0 := ofNat_lo32 hw0

#ix_piece {ARM}T_p2 from {ARM}T_p1 by
  -- run 2: operator test, int kind test, negation
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := evalArmF P m env aE (s + 18446744073709550528#64)
      (evalNeed (.unary .neg e) d - 1088) (slot24 sret.toNat)
      (world N L Room inp (.counted k) st1 d)
      iprop(PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ evalPost N L Room inp (.counted k) st1 d (.unary .neg e)
        (.int (wrap64 (-a))) sret s rv -∗ (twpW (vsaModel live)).W Φ))
  rotate_left
  · unfold evalArmF; iframe Hdv Hms Hcode Hro Hfb Hst Hslot Hw; iexact Hk
  intro F'
  refine {ARM}T_run2 (aX := aX) (s := s) (sret := sret) hlive hsf hs' hs2 hs3 hx1 hx2 hx3 ?_ ?_ ?_ hn.op ?_ ?_
  · ix_keep [hkeep1]
  · ix_keep [hkeep1]
  · ix_keep [hkeep1]
  · ix_fwd; exact hk0
  intros
  apply swp_closeM
  intro Mt2 hMt2
  have hsv2 : EvalSaved3 Mt2 s ret (rv 8) (rv 9) (rv 18) := by
    rw [hMt2]; ix_saved3 hsv1 using hoff
  unfold F' evalArmF
  iintro ⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, Hk⟩, Hms⟩
  -- value_int
  ihave Hvi := hvi $$ %sret %(-w1)
  unfold valueIntSpec
  iapply ms_callHelper (twpW _) (i := 0x800039d8)
    (jalx_800039d8 live (fun p hp => hlive _ (interp_code_800039d8 p hp)))
    interp_code_800039d8 (by decide)
  iframe Hvi Hcode Hms
  isplitl []
  · ipureintro; exact ⟨by ix_keep [hkeep1], by ix_reg; ix_fwd; rw [BitVec.zero_sub]⟩
  isplitl [Hslot]
  · iframe Hslot; ipureintro; exact hslg
  iintro %R3 %hkeep3 Hval Hms
  have hneg : (-w1).toInt = wrap64 (-a) := by rw [toInt_neg_wrap, hw1]
  rw [hneg]

#ix_piece {ARM}T_p3 from {ARM}T_p2 by
  -- run 4: the epilogue
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := evalArmF P m env aE (s + 18446744073709550528#64)
      (evalNeed (.unary .neg e) d - 1088) (valAt N sret.toNat (.int (wrap64 (-a))))
      (world N L Room inp (.counted k) st1 d)
      iprop(PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ evalPost N L Room inp (.counted k) st1 d (.unary .neg e)
        (.int (wrap64 (-a))) sret s rv -∗ (twpW (vsaModel live)).W Φ))
  rotate_left
  · unfold evalArmF; iframe Hdv Hms Hcode Hro Hfb Hst Hval Hw; iexact Hk
  intro F'
  refine {ARM}T_run3 (aX := aX) (s := s) (ret := ret) (v8 := rv 8) (v9 := rv 9)
    (v18 := rv 18) hlive hsf hs' hs2 hs3 hal ?_ ?_ ?_ ?_ ?_ ?_
  · ix_keep [hkeep3, hkeep1]
  · rw [hoff _ (by decide)]; exact hsv2.ra
  · rw [hoff _ (by decide)]; exact hsv2.s0
  · rw [hoff _ (by decide)]; exact hsv2.s1
  · rw [hoff _ (by decide)]; exact hsv2.s2
  intros
  apply swp_closeF
  unfold F' evalArmF
  iintro ⟨⟨#Hcode, #Hro, #Hfb, Hst, Hval, Hw, Hk⟩, Hms⟩
  ihave ⟨Hpc, Hra, Hregs, HS⟩ := ms_exit $$ Hms
  ihave Hst := evalFrame_join hsg.le hneed $$ [Hst HS]
  · iframe Hst HS
  ihave Hra := ptsto_eq (show _ = ret by ix_reg) $$ Hra
  iapply Hk $$ Hpc Hra
  unfold evalPost
  iexists _
  iframe Hregs Hst Hval Hw
  ipureintro
  intro x hx
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · ix_reg; exact evalSP_restore s |>.trans hregs.sp.symm
  all_goals ix_keep [hkeep3, hkeep1]

#ix_chain caseT_{ARM} := [{ARM}T_p1, {ARM}T_p2, {ARM}T_p3]

end VsaIris.Interp
