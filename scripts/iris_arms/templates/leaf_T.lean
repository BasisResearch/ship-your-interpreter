import VsaIris.Interp.LeafArm
import VsaIris.Interp.SpecValue

/-!
# `{ARM}`, total mode (family `leaf`, INTERP_DESIGN.md §6, lane E1)

`caseT_{ARM}`: `eval_expr` on `{CTOR}` meets its total, derivation-indexed
spec, given `{HELPERNAME}`'s spec. Two symbolic runs (`#ix_seg`: the prologue
and kind dispatch up to the helper's `jal`, then the shared epilogue) and the
helper call, in two pieces (`#ix_piece`) assembled by `#ix_chain`. Template:
`scripts/iris_arms/templates/leaf_T.lean`.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim

#ix_seg {ARM}T_run1 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s aE inp sret : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aX.toNat) (hx2 : aX.toNat + {W8} ≤ 0x100000000)
    (hx3 : aX.toNat + {W8} ≤ tohostAddr ∨ tohostAddr + 16 ≤ aX.toNat)
    (h10 : R 10 = sret) (h11 : R 11 = inp) (h12 : R 12 = aX) (h13 : R 13 = aE) (h2 : R 2 = s)
    (hk : ldv .lw m aX.toNat = {TAG}#64) (hku : ldv .lwu m aX.toNat = {TAG}#64) :
    IW live m (leafView aX.toNat {W}) (InExt (s.toNat - 1088, 1088)) Q 0x80003164#64 R Mt
  by ix_run hlive using [h10, h11, h12, h13, h2, hk, hku, hsf] at 0x{J}


#ix_seg {ARM}T_run2 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
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
    IW live m (leafView aX.toNat {W}) (InExt (s.toNat - 1088, 1088)) Q 0x{R2}#64 R Mt
  by ix_run hlive using [h2, hRA, hS0, hS1, hS2, hsf, hal]


open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr

#ix_piece {ARM}T_p1 {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {st : St} {d env : Nat} {BINDERS}
    (D : EvalECost st d env {CTOR} st {VAL} 0)
    (hvi : ⊢ {HSPEC}) :
    ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env {CTOR} st {VAL} 0 D by
  unfold evalSpecT_body fnSpecW
  iintro %k %sret %aE %aX %s %rv !> %ret %Φ Hpc Hra ⟨%hal, Hpre⟩ Hk
  unfold evalPre
  icases Hpre with ⟨Hregs, %hregs, #Hcode, #Hast, #Hfb, Hst, %hsg, Hslot, %hslg, %hbb, Hw⟩
  unfold astEG
  icases Hast with ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩
  {NODE}
  have hneed : 1088 ≤ evalNeed {CTOR} d := by
    have := Expr.stackNeed_ge {CTOR}; unfold evalNeed stackBudget; unfold evalFrame at this; omega
  have hs := hsg.lo; have hs2 := hsg.hi; have hs3 := hsg.al; have hs4 := hsg.le
  unfold Vsa.Sim.LayoutInstance.stackSL at hs hs2
  simp only at hs hs2
  have hs' : 0x87800000 + 1088 ≤ s.toNat := by omega
  have hsF : s - 1088#64 = s + 18446744073709550528#64 := evalSP_eq s
  have hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088 := by
    rw [← hsF]; exact toNat_sub_frame (by simp only [BitVec.toNat_ofNat]; omega)
  have hx1 := hn.lo; have hx2 := hn.hi; have hx3 := hn.off
  have hoff := evalSP_off (s := s) hsf (by omega)
  ihave ⟨Hst, HF⟩ := stackScratch_frame (f := 1088#64) hsg.le hneed $$ Hst
  rw [hsF, hsf, show (1088#64).toNat = 1088 from rfl]
  ihave ⟨%Mt0, Hms⟩ := ms_intro $$ [Hpc Hra Hregs HF]
  · iframe Hpc Hra Hregs; unfold blockOwn; iexact HF
  -- run 1: prologue, kind dispatch, the helper's arguments
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := evalArmF P m env aE (s + 18446744073709550528#64)
      (evalNeed {CTOR} d - 1088) (slot24 sret.toNat)
      (world N L Room inp (.counted (k + 0)) st d)
      iprop(PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ evalPost N L Room inp (.counted k) st d {CTOR}
        {VAL} sret s rv -∗ (twpW (vsaModel live)).W Φ))
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
  have hRA1 : ldv .ld Mt1 (s + 18446744073709550528#64 + 1080#64).toNat = ret := by
    subst hMt1; ix_fwd using [hoff]; ix_reg
  have hS01 : ldv .ld Mt1 (s + 18446744073709550528#64 + 1072#64).toNat = rv 8 := by
    subst hMt1; ix_fwd using [hoff]; ix_reg
  have hS11 : ldv .ld Mt1 (s + 18446744073709550528#64 + 1064#64).toNat = rv 9 := by
    subst hMt1; ix_fwd using [hoff]; ix_reg
  have hS21 : ldv .ld Mt1 (s + 18446744073709550528#64 + 1056#64).toNat = rv 18 := by
    subst hMt1; ix_fwd using [hoff]; ix_reg
  unfold F' evalArmF
  iintro ⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, Hk⟩, Hms⟩
  -- the helper
  ihave Hvi := hvi $$ {HINST}
  unfold {HSPECNAME}
  iapply ms_callHelper (twpW _) (i := 0x{J})
    (jalx_{J} live (fun p hp => hlive _ (interp_code_{J} p hp)))
    interp_code_{J} (by decide)
  iframe Hvi Hcode Hms
  isplitl []
  · ipureintro; {PINS}
  isplitl [Hslot]
  · iframe Hslot; {PRE}
  iintro %R3 %hkeep3 Hval Hms
  {POST}

#ix_piece {ARM}T_p2 from {ARM}T_p1 by
  -- run 2: the epilogue
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := evalArmF P m env aE (s + 18446744073709550528#64)
      (evalNeed {CTOR} d - 1088) (valAt N sret.toNat {VAL})
      (world N L Room inp (.counted (k + 0)) st d)
      iprop(PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ evalPost N L Room inp (.counted k) st d {CTOR}
        {VAL} sret s rv -∗ (twpW (vsaModel live)).W Φ))
  rotate_left
  · unfold evalArmF; iframe Hdv Hms Hcode Hro Hfb Hst Hval Hw; iexact Hk
  intro F'
  refine {ARM}T_run2 (aX := aX) (s := s) (ret := ret) (v8 := rv 8) (v9 := rv 9)
    (v18 := rv 18) hlive hsf hs' hs2 hs3 hal ?_ hRA1 hS01 hS11 hS21 ?_
  · ix_keep [hkeep3]
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
  rw [Nat.add_zero]
  iframe Hregs Hst Hval Hw
  ipureintro
  intro x hx
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · ix_reg; exact evalSP_restore s |>.trans hregs.sp.symm
  all_goals ix_keep [hkeep3]

#ix_chain caseT_{ARM} := [{ARM}T_p1, {ARM}T_p2]

end VsaIris.Interp
