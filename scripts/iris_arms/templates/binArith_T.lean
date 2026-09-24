import VsaIris.Interp.Case.BinaryAddIntT
import VsaIris.Interp.BinArm
import VsaIris.Interp.ProofArith

/-!
# `{ARM}`, total mode (family `binArith`, INTERP_DESIGN.md §6; lane E2)

`caseT_{ARM}`: `eval_expr` on `.binary {OP} l r` over two ints meets its total,
derivation-indexed spec, given the children's specs and `value_int`'s spec.
libgcc's routine is followed inside the run (`iw_jal`, `ProofArith.lean`).
The prologue and both children's staging are lane G's runs
(`BinaryAddIntT_run1`/`_run2`: they do not depend on the operator); the
operator dispatch and the tail are two runs of this row, the glue four pieces
(`#ix_piece`, split at the calls), assembled by `#ix_chain`. Template:
`scripts/iris_arms/templates/binArith_T.lean`.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim

#ix_seg {R3NAME} {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s sret w1 : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aX.toNat) (hx2 : aX.toNat + 32 ≤ 0x100000000)
    (hx3 : aX.toNat + 32 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aX.toNat)
    (h8 : R 8 = aX) (h2 : R 2 = s + 18446744073709550528#64) (h9 : R 9 = sret) (h19 : R 19 = w1)
    (hop : ldv .lw m (aX + 8#64).toNat = {TOK}#64)
    (hKL : ldv .ld Mt (s.toNat - 1088) = 2#64)
    (hKR : ldv .lw Mt (s + 18446744073709550528#64 + 144#64).toNat = 2#64){HBBIND} :
    IW live m (binView aX.toNat) (InExt (s.toNat - 1088, 1088)) Q 0x8000351c#64 R Mt
{R3TAIL}
{RUN3B}


#ix_seg {ARM}T_run4 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s ret v8 v9 v18 v19 : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hal : ret.toNat % 4 = 0)
    (h2 : R 2 = s + 18446744073709550528#64)
    (hRA : ldv .ld Mt (s + 18446744073709550528#64 + 1080#64).toNat = ret)
    (hS0 : ldv .ld Mt (s + 18446744073709550528#64 + 1072#64).toNat = v8)
    (hS1 : ldv .ld Mt (s + 18446744073709550528#64 + 1064#64).toNat = v9)
    (hS2 : ldv .ld Mt (s + 18446744073709550528#64 + 1056#64).toNat = v18)
    (hS3 : ldv .ld Mt (s + 18446744073709550528#64 + 1048#64).toNat = v19) :
    IW live m (binView aX.toNat) (InExt (s.toNat - 1088, 1088)) Q 0x{R4}#64 R Mt
  by ix_run hlive using [h2, hRA, hS0, hS1, hS2, hS3, hsf, hal]


open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr

#ix_piece {ARM}T_p1 {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {st st1 st2 : St} {d env : Nat} {l r : Expr} {a b : Int} {nl nr : Nat}
    (Dl : EvalECost st d env l st1 (.int a) nl) (Dr : EvalECost st1 d env r st2 (.int b) nr)
    (D : EvalECost st d env (.binary {OP} l r) st2 {RES} (nl + nr)){HB0}
    (hl : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env l st1 (.int a) nl Dl)
    (hr : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st1 d env r st2 (.int b) nr Dr)
    ({HNAME} : ⊢ ∀ p b, {HSPEC} (GF := GF) (vsaModel live) N (twpW (vsaModel live)) p b) :
    ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env (.binary {OP} l r) st2
        {RES} (nl + nr) D by
  unfold evalSpecT_body fnSpecW
  iintro %k %sret %aE %aX %s %rv !> %ret %Φ Hpc Hra ⟨%hal, Hpre⟩ Hk
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
  -- run 1: prologue, kind dispatch, stage the left child
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := evalArmF P m env aE (s + 18446744073709550528#64)
      (evalNeed (.binary {OP} l r) d - 1088) (slot24 sret.toNat)
      (world N L Room inp (.counted (k + (nl + nr))) st d)
      iprop(PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ evalPost N L Room inp (.counted k) st2 d (.binary {OP} l r)
        {RES} sret s rv -∗ (twpW (vsaModel live)).W Φ))
  rotate_left
  · unfold evalArmF; iframe Hdv Hms Hcode Hro Hfb Hst Hslot Hw; iexact Hk
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
  iintro ⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, Hk⟩, Hms⟩
  -- the left child
  ihave Hl := hl
  rw [show k + (nl + nr) = k + nr + nl by omega]
  iapply ms_callEvalT (N := N) (L := L) (Room := Room) (inp := inp) (i := 0x800034f8)
    (jalx_800034f8 live (fun p hp => hlive _ (interp_code_800034f8 p hp)))
    interp_code_800034f8 (by decide) Dl (k := k + nr) (slot := s + 18446744073709550528#64 + 120#64)
    (aC := BitVec.ofNat 64 aL) (aE := aE) (s := s + 18446744073709550528#64)
    (m := evalNeed (.binary {OP} l r) d - 1088)
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
  unfold valOf
  icases Hv1 with %⟨hw0, hw1⟩
  have hk0 := ofNat_lo32 hw0

#ix_piece {ARM}T_p2 from {ARM}T_p1 by
  -- run 2: stage the right child
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := evalArmF P m env aE (s + 18446744073709550528#64)
      (evalNeed (.binary {OP} l r) d - 1088) (slot24 sret.toNat)
      (world N L Room inp (.counted (k + nr)) st1 d)
      iprop(PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ evalPost N L Room inp (.counted k) st2 d (.binary {OP} l r)
        {RES} sret s rv -∗ (twpW (vsaModel live)).W Φ))
  rotate_left
  · unfold evalArmF; iframe Hdv Hms Hcode Hro Hfb Hst Hslot Hw; iexact Hk
  intro F'
  refine BinaryAddIntT_run2 (aE := aE) (inp := BitVec.ofNat 64 inp) (w1 := w1) (kL := 2#64) hlive hsf hs' hs2 hs3 hx1 hx2 hx3 ?_ ?_ ?_ hn.right ?_ ?_ ?_ ?_
  · ix_keep [hkeep1]
  · ix_keep [hkeep1]
  · ix_keep [hkeep1]
  · ix_fwd; exact hA1
  · ix_fwd; exact hk0
  · ix_fwd
  intros
  apply swp_closeM
  intro Mt2 hMt2
  have hsv2 : EvalSaved Mt2 s ret (rv 8) (rv 9) (rv 18) (rv 19) := by
    rw [hMt2]; ix_saved hsv1 using hoff
  unfold F' evalArmF
  iintro ⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, Hk⟩, Hms⟩
  -- the right child
  ihave Hr := hr
  iapply ms_callEvalT (N := N) (L := L) (Room := Room) (inp := inp) (i := 0x80003518)
    (jalx_80003518 live (fun p hp => hlive _ (interp_code_80003518 p hp)))
    interp_code_80003518 (by decide) Dr (k := k) (slot := s + 18446744073709550528#64 + 144#64)
    (aC := BitVec.ofNat 64 aR) (aE := aE) (s := s + 18446744073709550528#64)
    (m := evalNeed (.binary {OP} l r) d - 1088)
    gR.child gR.fits gR.below gR.slotGeom hbr
  iframe Hr Hcode Hfb Hms Hst Hw
  isplitl []
  · ipureintro
    refine ⟨⟨by ix_reg, by ix_reg, by ix_reg, by ix_reg, by ix_keep [hkeep1]⟩, fun b hb => ?_⟩
    have g1 := gR.slot; have g2 := gR.sp; simp only [VsaIris.InExt, evalSP] at hb g1 g2 ⊢; omega
  isplitl []
  · imodintro; rw [hRt]; iapply astEG_of_view hrr hgeo $$ Hro
  iintro %R2 %u0 %u1 %u2 %hkeep2 #Hv2 Hms Hst Hw
  unfold valOf
  icases Hv2 with %⟨hu0, hu1⟩
  have hk0' := ofNat_lo32 hu0

#ix_piece {ARM}T_p3 from {ARM}T_p2 by
  -- run 3: operator dispatch, int/int checks, the operation
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := evalArmF P m env aE (s + 18446744073709550528#64)
      (evalNeed (.binary {OP} l r) d - 1088) (slot24 sret.toNat)
      (world N L Room inp (.counted k) st2 d)
      iprop(PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ evalPost N L Room inp (.counted k) st2 d (.binary {OP} l r)
        {RES} sret s rv -∗ (twpW (vsaModel live)).W Φ))
  rotate_left
  · unfold evalArmF; iframe Hdv Hms Hcode Hro Hfb Hst Hslot Hw; iexact Hk
  intro F'
  refine {ARM}T_run3 (aX := aX) (s := s) (sret := sret) (w1 := w1) hlive hsf hs' hs2 hs3 hx1 hx2 hx3
    ?_ ?_ ?_ ?_ hn.op ?_ ?_{ZEROHOLE} ?_
  · ix_keep [hkeep2, hkeep1]
  · ix_keep [hkeep2, hkeep1]
  · ix_keep [hkeep2, hkeep1]
  · ix_keep [hkeep2]
  · ix_fwd; rw [hMt2]; ix_fwd
  · ix_fwd; exact hk0'{ZEROBULLET}
  intros
  -- the libgcc call, followed inside the run
  refine iw_jal 0x{JL} _ _ (jalx_{JL} live (fun p hp => hlive _ (interp_code_{JL} p hp)))
    interp_code_{JL} rfl ?_
  refine {LIBIW} hlive {LX} {LY} 0x{RETA}#64 _ _ {LIBHY}?_ ?_ ?_ (by decide) (fun R' hq hkeep => ?_)
  · {B10}
  · {B11}
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, Nat.reduceAdd]
  have hR'2 : R' 2 = s + 18446744073709550528#64 := by
    rw [hkeep 2 {KEEPARGS}]; ix_reg; ix_keep [hkeep2, hkeep1]
  have hR'k : ∀ z ∈ [20, 21, 22, 23, 24, 25, 26, 27], R' z = rv z := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (rw [hkeep _ {KEEPARGS}]; ix_reg; ix_keep [hkeep2, hkeep1])
  refine {ARM}T_run3b (s := s) (sret := sret) hlive hsf hs' hs2 hs3 ?_ ?_
  · rw [hkeep 9 {KEEPARGS}]; ix_reg; ix_keep [hkeep2, hkeep1]
  intros
  apply swp_closeM
  intro Mt3 hMt3
  have hsv3 : EvalSaved Mt3 s ret (rv 8) (rv 9) (rv 18) (rv 19) := by
    rw [hMt3]; ix_saved hsv2 using hoff
  unfold F' evalArmF
  iintro ⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, Hk⟩, Hms⟩
  -- {HELPERC}
  ihave Hvi := {HNAME} $$ %sret %(R' 10)
  unfold {HSPEC}
  iapply ms_callHelper (twpW _) (i := 0x{J3})
    (jalx_{J3} live (fun p hp => hlive _ (interp_code_{J3} p hp)))
    interp_code_{J3} (by decide)
  iframe Hvi Hcode Hms
  isplitl []
  · ipureintro; exact ⟨by ix_reg, by ix_reg⟩
  isplitl [Hslot]
  · iframe Hslot; ipureintro; exact hslg
  iintro %R3 %hkeep3 Hval Hms
  have hsum : (R' 10).toInt = {RESI} := by {SUMPF}
  rw [hsum]

#ix_piece {ARM}T_p4 from {ARM}T_p3 by
  -- run 4: the epilogue
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (twpW _) (F := evalArmF P m env aE (s + 18446744073709550528#64)
      (evalNeed (.binary {OP} l r) d - 1088) (valAt N sret.toNat {RES})
      (world N L Room inp (.counted k) st2 d)
      iprop(PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ evalPost N L Room inp (.counted k) st2 d (.binary {OP} l r)
        {RES} sret s rv -∗ (twpW (vsaModel live)).W Φ))
  rotate_left
  · unfold evalArmF; iframe Hdv Hms Hcode Hro Hfb Hst Hval Hw; iexact Hk
  intro F'
  refine {ARM}T_run4 (aX := aX) (s := s) (ret := ret) (v8 := rv 8) (v9 := rv 9)
    (v18 := rv 18) (v19 := rv 19) hlive hsf hs' hs2 hs3 hal ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    rw [keep_helper hkeep3 (by decide) (by decide)]
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hR'2
  · rw [hoff _ (by decide)]; exact hsv3.ra
  · rw [hoff _ (by decide)]; exact hsv3.s0
  · rw [hoff _ (by decide)]; exact hsv3.s1
  · rw [hoff _ (by decide)]; exact hsv3.s2
  · rw [hoff _ (by decide)]; exact hsv3.s3
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
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · ix_reg; exact evalSP_restore s |>.trans hregs.sp.symm
  all_goals first
    | (ix_reg; done)
    | (simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
       rw [keep_helper hkeep3 (by decide) (by decide)]
       simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
       exact hR'k _ (by decide))

#ix_chain caseT_{ARM} := [{ARM}T_p1, {ARM}T_p2, {ARM}T_p3, {ARM}T_p4]



end VsaIris.Interp
