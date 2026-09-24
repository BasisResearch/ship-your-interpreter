import VsaIris.Interp.ArmLogical

/-!
# `{ARM}`, total mode (family `logLong`, INTERP_DESIGN.md §6)

`caseT_{ARM}`: `eval_expr` on `.logical {LOP} l r` whose left operand does not
decide the result (`truthy = {TRU}`) meets its total, derivation-indexed spec,
given the children's specs and the `value_truthy`/`value_bool` specs. Six
symbolic runs (`#ix_seg`): prologue and left operand; copy and
`value_truthy`; the branch on the bit and the right operand; copy and
`value_truthy`; `value_bool`; the epilogue. The glue in six pieces
(`#ix_piece`, split at the calls), assembled by `#ix_chain`. Each
`value_truthy` call lends the helper the copy at `sp+64` (`ms_callTruthy`).
Template: `scripts/iris_arms/templates/logLong_T.lean`.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim

#ix_seg {ARM}T_run1 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s aE inp sret : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aX.toNat) (hx2 : aX.toNat + 32 ≤ 0x100000000)
    (hx3 : aX.toNat + 32 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aX.toNat)
    (h10 : R 10 = sret) (h11 : R 11 = inp) (h12 : R 12 = aX) (h13 : R 13 = aE) (h2 : R 2 = s)
    (hk : ldv .lw m aX.toNat = 7#64) (hku : ldv .lwu m aX.toNat = 7#64) :
    IW live m (binView aX.toNat) (InExt (s.toNat - 1088, 1088)) Q 0x80003164#64 R Mt
  by ix_run hlive using [h10, h11, h12, h13, h2, hk, hku, hsf] at 0x80003568

#ix_seg {ARM}T_run2 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aX.toNat) (hx2 : aX.toNat + 32 ≤ 0x100000000)
    (hx3 : aX.toNat + 32 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aX.toNat)
    (h8 : R 8 = aX) (h2 : R 2 = s + 18446744073709550528#64)
    (hop : ldv .lw m (aX + 8#64).toNat = {TOK}#64) :
    IW live m (binView aX.toNat) (InExt (s.toNat - 1088, 1088)) Q 0x8000356c#64 R Mt
  by ix_run hlive using [h8, h2, hop, hsf] at 0x{J2}

#ix_seg {ARM}T_run3 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s aE inp aR : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aX.toNat) (hx2 : aX.toNat + 32 ≤ 0x100000000)
    (hx3 : aX.toNat + 32 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aX.toNat)
    (h8 : R 8 = aX) (h2 : R 2 = s + 18446744073709550528#64) (h18 : R 18 = inp)
    (hright : ldv .ld m (aX + 24#64).toNat = aR)
    (hA : ldv .ld Mt (s.toNat - 1088) = aE) :
    IW live m (binView aX.toNat) (InExt (s.toNat - 1088, 1088)) Q 0x{R3}#64 (upd R 10 {BIT}#64) Mt
  by ix_run hlive using [h8, h2, h18, hright, hA, hsf] at 0x{J3}

#ix_seg {ARM}T_run4 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (h2 : R 2 = s + 18446744073709550528#64) :
    IW live m (binView aX.toNat) (InExt (s.toNat - 1088, 1088)) Q 0x{R4}#64 R Mt
  by ix_run hlive using [h2, hsf] at 0x800035cc

#ix_seg {ARM}T_run5 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s : BitVec 64} :
    IW live m (binView aX.toNat) (InExt (s.toNat - 1088, 1088)) Q 0x800035d0#64 R Mt
  by ix_run hlive at 0x800035d8

#ix_seg {ARM}T_run6 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
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
    IW live m (binView aX.toNat) (InExt (s.toNat - 1088, 1088)) Q 0x800035dc#64 R Mt
  by ix_run hlive using [h2, hRA, hS0, hS1, hS2, hsf, hal]


open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr

#ix_piece {ARM}T_p1 {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {st st1 st2 : St} {d env : Nat} {l r : Expr} {lv rv' : Value} {nl nr : Nat}
    (Dl : EvalECost st d env l st1 lv nl) (htl : lv.truthy = {TRU})
    (Dr : EvalECost st1 d env r st2 rv' nr)
    (D : EvalECost st d env (.logical {LOP} l r) st2 (.bool rv'.truthy) (nl + nr))
    (hl : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env l st1 lv nl Dl)
    (hr : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st1 d env r st2 rv' nr Dr)
    (hvt : ⊢ ∀ p v, valueTruthySpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) p v)
    (hvb : ⊢ ∀ p b, valueBoolSpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) p b) :
    ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env (.logical {LOP} l r) st2
        (.bool rv'.truthy) (nl + nr) D by
  unfold evalSpecT_body fnSpecW
  iintro %k %sret %aE %aX %s %rv !> %ret %Φ Hpc Hra ⟨%hal, Hpre⟩ Hk
  unfold evalPre
  icases Hpre with ⟨Hregs, %hregs, #Hcode, #Hast, #Hfb, Hst, %hsg, Hslot, %hslg, %hbb, Hw⟩
  unfold astEG
  icases Hast with ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩
  obtain ⟨aL, aR, hn, hrl, hrr, haL, haR⟩ := logNode_of_repr hrepr hgeo
  have hneed : 1088 ≤ evalNeed (.logical {LOP} l r) d := by
    have := Expr.stackNeed_ge (.logical {LOP} l r); unfold evalNeed stackBudget; unfold evalFrame at this; omega
  have hs := hsg.lo; have hs2 := hsg.hi; have hs3 := hsg.al; have hs4 := hsg.le
  unfold Vsa.Sim.LayoutInstance.stackSL at hs hs2
  simp only at hs hs2
  have hs' : 0x87800000 + 1088 ≤ s.toNat := by omega
  have hsF : s - 1088#64 = s + 18446744073709550528#64 := evalSP_eq s
  have hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088 := by
    rw [← hsF]; exact toNat_sub_frame (by simp only [BitVec.toNat_ofNat]; omega)
  have gL := evalCallGeom (o := 120) hsg
    (by have := evalNeed_logical_left {LOP} l r d; unfold evalFrame at this; omega) (by decide) (by decide)
  have gR := evalCallGeom (o := {SR}) hsg
    (by have := evalNeed_logical_right {LOP} l r d; unfold evalFrame at this; omega) (by decide) (by decide)
  have hbl : l.bodiesBound perCallBudget = true := (Expr.bodiesBound_logical hbb).1
  have hbr : r.bodiesBound perCallBudget = true := (Expr.bodiesBound_logical hbb).2
  have hLt : (BitVec.ofNat 64 aL).toNat = aL := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt haL]
  have hRt : (BitVec.ofNat 64 aR).toNat = aR := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt haR]
  have hx1 := hn.lo; have hx2 := hn.hi; have hx3 := hn.off
  have hoff := evalSP_off (s := s) hsf (by omega)
  ihave ⟨Hst, HF⟩ := stackScratch_frame (f := 1088#64) hsg.le hneed $$ Hst
  rw [hsF, hsf, show (1088#64).toNat = 1088 from rfl]
  ihave ⟨%Mt0, Hms⟩ := ms_intro $$ [Hpc Hra Hregs HF]
  · iframe Hpc Hra Hregs; unfold blockOwn; iexact HF
  -- run 1: prologue, kind dispatch, stage the left operand
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := evalArmF P m env aE (s + 18446744073709550528#64)
      (evalNeed (.logical {LOP} l r) d - 1088) (slot24 sret.toNat)
      (world N L Room inp (.counted (k + (nl + nr))) st d)
      iprop(PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ evalPost N L Room inp (.counted k) st2 d (.logical {LOP} l r)
        (.bool rv'.truthy) sret s rv -∗ (twpW (vsaModel live)).W Φ))
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
  have hA1 : ldv .ld Mt1 (s.toNat - 1088) = aE := by subst hMt1; ix_fwd
  unfold F' evalArmF
  iintro ⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, Hk⟩, Hms⟩
  -- the left operand
  ihave Hl := hl
  rw [show k + (nl + nr) = k + nr + nl by omega]
  iapply ms_callEvalT (N := N) (L := L) (Room := Room) (inp := inp) (i := 0x80003568)
    (jalx_80003568 live (fun p hp => hlive _ (interp_code_80003568 p hp)))
    interp_code_80003568 (by decide) Dl (k := k + nr) (slot := s + 18446744073709550528#64 + 120#64)
    (aC := BitVec.ofNat 64 aL) (aE := aE) (s := s + 18446744073709550528#64)
    (m := evalNeed (.logical {LOP} l r) d - 1088)
    gL.child gL.fits gL.below gL.slotGeom hbl
  iframe Hl Hcode Hfb Hms Hst Hw
  isplitl []
  · ipureintro
    refine ⟨⟨by ix_reg, by ix_reg; exact hregs.a1, by ix_reg; exact hn.left,
      by ix_reg; exact hregs.a3, by ix_reg⟩, fun b hb => ?_⟩
    have g1 := gL.slot; have g2 := gL.sp; simp only [VsaIris.InExt, evalSP] at hb g1 g2 ⊢; omega
  isplitl []
  · imodintro; rw [hLt]; iapply astEG_of_view hrl hgeo $$ Hro
  iintro %R1 %w0 %w1 %w2 %hkeep1 #Hv1 Hms Hst Hw

#ix_piece {ARM}T_p2 from {ARM}T_p1 by
  -- run 2: operator test, copy the left value to `sp+64`
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := iprop(evalArmF P m env aE (s + 18446744073709550528#64)
      (evalNeed (.logical {LOP} l r) d - 1088) (slot24 sret.toNat)
      (world N L Room inp (.counted (k + nr)) st1 d)
      iprop(PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ evalPost N L Room inp (.counted k) st2 d (.logical {LOP} l r)
        (.bool rv'.truthy) sret s rv -∗ (twpW (vsaModel live)).W Φ) ∗ □ valOf N lv w0 w1 w2))
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
  have hA2 : ldv .ld Mt2 (s.toNat - 1088) = aE := by rw [hMt2]; ix_fwdF hoff; exact hA1
  unfold F' evalArmF
  iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, Hk⟩, #Hv1⟩, Hms⟩
  -- value_truthy on the copy
  have hc0 : ldv .ld Mt2 (s.toNat - 1088 + 64) = w0 := by rw [hMt2]; ix_fwdF hoff
  have hc8 : ldv .ld Mt2 (s.toNat - 1088 + 72) = w1 := by rw [hMt2]; ix_fwdF hoff
  have hc16 : ldv .ld Mt2 (s.toNat - 1088 + 80) = w2 := by rw [hMt2]; ix_fwdF hoff
  ihave Hvt := hvt $$ %(s + 18446744073709550528#64 + 64#64) %lv
  iapply ms_callTruthy (twpW _) (i := 0x{J2})
    (jalx_{J2} live (fun p hp => hlive _ (interp_code_{J2} p hp)))
    interp_code_{J2} (by decide) (S := InExt (s.toNat - 1088, 1088)) ⟨hoff 64 (by decide), rfl, rfl⟩
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
  have hA2' : ldv .ld Mt2' (s.toNat - 1088) = aE := by
    rw [ldv_ld_congr fun j hj => hag2 _ (by simp only [VsaIris.InExt]; omega)
      (by rw [hoff 64 (by decide)]; simp only [VsaIris.InExt]; omega)]; exact hA2
  rw [htl] at hbit

#ix_piece {ARM}T_p3 from {ARM}T_p2 by
  -- run 3: the branch on the bit, stage the right operand
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := evalArmF P m env aE (s + 18446744073709550528#64)
      (evalNeed (.logical {LOP} l r) d - 1088) (slot24 sret.toNat)
      (world N L Room inp (.counted (k + nr)) st1 d)
      iprop(PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ evalPost N L Room inp (.counted k) st2 d (.logical {LOP} l r)
        (.bool rv'.truthy) sret s rv -∗ (twpW (vsaModel live)).W Φ))
  rotate_left
  · unfold evalArmF; iframe Hdv Hms Hcode Hro Hfb Hst Hslot Hw; iexact Hk
  intro F'
  refine iw_regFact (k := 10) (v := {BIT}#64) (by ix_reg; exact hbit) ?_
  refine {ARM}T_run3 (aX := aX) (s := s) (aE := aE) (inp := BitVec.ofNat 64 inp) hlive hsf hs' hs2 hs3
    hx1 hx2 hx3 ?_ ?_ ?_ hn.right hA2' ?_
  · ix_reg; ix_keep [hkeep2, hkeep1]
  · ix_reg; ix_keep [hkeep2, hkeep1]
  · ix_reg; ix_keep [hkeep2, hkeep1]
  intros
  apply swp_closeM
  intro Mt3 hMt3
  have hsv3 : EvalSaved3 Mt3 s ret (rv 8) (rv 9) (rv 18) := by rw [hMt3]; exact hsv2'
  unfold F' evalArmF
  iintro ⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, Hk⟩, Hms⟩
  -- the right operand
  ihave Hr := hr
  iapply ms_callEvalT (N := N) (L := L) (Room := Room) (inp := inp) (i := 0x{J3})
    (jalx_{J3} live (fun p hp => hlive _ (interp_code_{J3} p hp)))
    interp_code_{J3} (by decide) Dr (k := k) (slot := s + 18446744073709550528#64 + {SR}#64)
    (aC := BitVec.ofNat 64 aR) (aE := aE) (s := s + 18446744073709550528#64)
    (m := evalNeed (.logical {LOP} l r) d - 1088)
    gR.child gR.fits gR.below gR.slotGeom hbr
  iframe Hr Hcode Hfb Hms Hst Hw
  isplitl []
  · ipureintro
    refine ⟨⟨by ix_reg, by ix_reg, by ix_reg, by ix_reg, by ix_keep [hkeep2, hkeep1]⟩,
      fun b hb => ?_⟩
    have g1 := gR.slot; have g2 := gR.sp; simp only [VsaIris.InExt, evalSP] at hb g1 g2 ⊢; omega
  isplitl []
  · imodintro; rw [hRt]; iapply astEG_of_view hrr hgeo $$ Hro
  iintro %R3 %u0 %u1 %u2 %hkeep3 #Hv3 Hms Hst Hw

#ix_piece {ARM}T_p4 from {ARM}T_p3 by
  -- run 4: copy the right value to `sp+64`
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := iprop(evalArmF P m env aE (s + 18446744073709550528#64)
      (evalNeed (.logical {LOP} l r) d - 1088) (slot24 sret.toNat)
      (world N L Room inp (.counted k) st2 d)
      iprop(PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ evalPost N L Room inp (.counted k) st2 d (.logical {LOP} l r)
        (.bool rv'.truthy) sret s rv -∗ (twpW (vsaModel live)).W Φ) ∗ □ valOf N rv' u0 u1 u2))
  rotate_left
  · unfold evalArmF; iframe Hdv Hms; isplitr [Hv3]
    · iframe Hcode Hro Hfb Hst Hslot Hw; iexact Hk
    · iexact Hv3
  intro F'
  refine {ARM}T_run4 (aX := aX) (s := s) hlive hsf hs' hs2 hs3 ?_ ?_
  · ix_keep [hkeep3, hkeep2, hkeep1]
  intros
  apply swp_closeM
  intro Mt4 hMt4
  have hsv4 : EvalSaved3 Mt4 s ret (rv 8) (rv 9) (rv 18) := by
    rw [hMt4]; ix_saved3 hsv3 using hoff
  unfold F' evalArmF
  iintro ⟨⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, Hk⟩, #Hv3⟩, Hms⟩
  -- value_truthy on the copy
  have hd0 : ldv .ld Mt4 (s.toNat - 1088 + 64) = u0 := by rw [hMt4]; ix_fwdF hoff
  have hd8 : ldv .ld Mt4 (s.toNat - 1088 + 72) = u1 := by rw [hMt4]; ix_fwdF hoff
  have hd16 : ldv .ld Mt4 (s.toNat - 1088 + 80) = u2 := by rw [hMt4]; ix_fwdF hoff
  ihave Hvt := hvt $$ %(s + 18446744073709550528#64 + 64#64) %rv'
  iapply ms_callTruthy (twpW _) (i := 0x800035cc)
    (jalx_800035cc live (fun p hp => hlive _ (interp_code_800035cc p hp)))
    interp_code_800035cc (by decide) (S := InExt (s.toNat - 1088, 1088)) ⟨hoff 64 (by decide), rfl, rfl⟩
    (fun b hb => by rw [hoff 64 (by decide)] at hb; simp only [VsaIris.InExt] at hb ⊢; omega)
    ⟨by rw [hoff 64 (by decide)]; omega, by rw [hoff 64 (by decide)]; unfold Vsa.Sim.tohostAddr; omega,
      by rw [hoff 64 (by decide)]; omega⟩
    hd0 hd8 hd16
  iframe Hvt Hcode Hv3 Hms
  isplitl []
  · ipureintro; ix_reg
  iintro %R4 %Mt4' %⟨hkeep4, hbit4, hag4⟩ Hms
  have hsv4' : EvalSaved3 Mt4' s ret (rv 8) (rv 9) (rv 18) :=
    hsv4.agree fun a h1 h2 => hag4 a (by simp only [VsaIris.InExt]; omega)
      (by rw [hoff 64 (by decide)]; simp only [VsaIris.InExt]; omega)

#ix_piece {ARM}T_p5 from {ARM}T_p4 by
  -- run 5: stage `value_bool` on the bit
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := evalArmF P m env aE (s + 18446744073709550528#64)
      (evalNeed (.logical {LOP} l r) d - 1088) (slot24 sret.toNat)
      (world N L Room inp (.counted k) st2 d)
      iprop(PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ evalPost N L Room inp (.counted k) st2 d (.logical {LOP} l r)
        (.bool rv'.truthy) sret s rv -∗ (twpW (vsaModel live)).W Φ))
  rotate_left
  · unfold evalArmF; iframe Hdv Hms Hcode Hro Hfb Hst Hslot Hw; iexact Hk
  intro F'
  refine {ARM}T_run5 (aX := aX) (s := s) hlive ?_
  apply swp_closeM
  intro Mt5 hMt5
  have hsv5 : EvalSaved3 Mt5 s ret (rv 8) (rv 9) (rv 18) := by rw [hMt5]; exact hsv4'
  unfold F' evalArmF
  iintro ⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, Hk⟩, Hms⟩
  -- value_bool
  ihave Hvb := hvb $$ %sret %(if rv'.truthy then 1#64 else 0#64)
  unfold valueBoolSpec
  iapply ms_callHelper (twpW _) (i := 0x800035d8)
    (jalx_800035d8 live (fun p hp => hlive _ (interp_code_800035d8 p hp)))
    interp_code_800035d8 (by decide)
  iframe Hvb Hcode Hms
  isplitl []
  · ipureintro; exact ⟨by ix_keep [hkeep4, hkeep3, hkeep2, hkeep1], by ix_reg; exact hbit4⟩
  isplitl [Hslot]
  · iframe Hslot; ipureintro; exact hslg
  iintro %R5 %hkeep5 Hval Hms
  rw [boolBit_ne]

#ix_piece {ARM}T_p6 from {ARM}T_p5 by
  -- run 6: the epilogue
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := evalArmF P m env aE (s + 18446744073709550528#64)
      (evalNeed (.logical {LOP} l r) d - 1088) (valAt N sret.toNat (.bool rv'.truthy))
      (world N L Room inp (.counted k) st2 d)
      iprop(PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ evalPost N L Room inp (.counted k) st2 d (.logical {LOP} l r)
        (.bool rv'.truthy) sret s rv -∗ (twpW (vsaModel live)).W Φ))
  rotate_left
  · unfold evalArmF; iframe Hdv Hms Hcode Hro Hfb Hst Hval Hw; iexact Hk
  intro F'
  refine {ARM}T_run6 (aX := aX) (s := s) (ret := ret) (v8 := rv 8) (v9 := rv 9)
    (v18 := rv 18) hlive hsf hs' hs2 hs3 hal ?_ ?_ ?_ ?_ ?_ ?_
  · ix_keep [hkeep5, hkeep4, hkeep3, hkeep2, hkeep1]
  · rw [hoff _ (by decide)]; exact hsv5.ra
  · rw [hoff _ (by decide)]; exact hsv5.s0
  · rw [hoff _ (by decide)]; exact hsv5.s1
  · rw [hoff _ (by decide)]; exact hsv5.s2
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
  all_goals ix_keep [hkeep5, hkeep4, hkeep3, hkeep2, hkeep1]

#ix_chain caseT_{ARM} := [{ARM}T_p1, {ARM}T_p2, {ARM}T_p3, {ARM}T_p4, {ARM}T_p5, {ARM}T_p6]

end VsaIris.Interp
