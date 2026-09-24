import VsaIris.Interp.Case.{ARM}T
import VsaIris.Interp.LeafErr

/-!
# `{ARM}`, partial mode (family `var`, INTERP_DESIGN.md §6, §4.2, lane E1)

`caseP_{ARM}`: `eval_expr` on `.var x` meets its partial, outcome-quantified
spec. After `env_get` the case splits on the lookup: found, the total case's
tail (`{ARM}T_run2`) returns with `EvalE.var`; unbound, the `beqz` goes to
`runtime_error(in, line, "undefined variable '%s'", name, 0)` (`ev_rtErr`),
which aborts. The error arm needs `leafErrCtx` and `ErrRoom` (`LeafErr.lean`,
INTERP_DESIGN.md Q7), and the case is stated at `Core := evalCore`.
Template: `scripts/iris_arms/templates/var_P.lean`.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim

#ix_seg {ARM}P_run3 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s sret inp : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aX.toNat) (hx2 : aX.toNat + 16 ≤ 0x100000000)
    (hx3 : aX.toNat + 16 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aX.toNat)
    (h8 : R 8 = aX) (h18 : R 18 = inp) (h2 : R 2 = s + 18446744073709550528#64) :
    IW live m (leafView aX.toNat 8)
    (fun b => InExt (s.toNat - 1088, 1088) b ∨ InExt (sret.toNat, 24) b) Q 0x{E1TO}#64 R Mt
  by ix_run hlive using [h8, h18, h2, hsf] at 0x{EJ}

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr VsaIris.Newlib

#ix_piece {ARM}P_p1 {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {st : St} {d env : Nat} {x : String} (HN : NewlibHoles) (hcl : CodeLive live)
    (hroom : ErrRoom (.var x) d)
    (hget : ⊢ envGetSpec (GF := GF) (wpW (vsaModel live)) N) :
    leafErrCtx inp ∗ evalSpecsP (GF := GF) (vsaModel live) N L Room inp (evalCore N L Room inp) ⊢
      evalSpecP_body (GF := GF) (vsaModel live) N L Room inp (evalCore N L Room inp) st d env
        (.var x) by
  iintro ⟨#HE, #-⟩
  unfold evalSpecP_body fnSpecAbort
  iintro %sret %aE %aX %s %rv !> %ret %Φ Hpc Hra ⟨%hal, Hpre⟩ Hk
  unfold evalPre
  icases Hpre with ⟨Hregs, %hregs, #Hcode, #Hast, #Hfb, Hst, %hsg, Hslot, %hslg, %hbb, Hw⟩
  unfold astEG
  icases Hast with ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩
  obtain ⟨q, hn, hfs⟩ := leafNode_var hrepr hgeo
  have hqt : (BitVec.ofNat 64 q).toNat = q := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfs.lt]
  have hneed : 1088 + envGetNeed ≤ evalNeed (.var x) d := by
    unfold evalNeed stackBudget envGetNeed; simp only [Expr.stackNeed, evalFrame]; omega
  have hs := hsg.lo; have hs2 := hsg.hi; have hs3 := hsg.al; have hs4 := hsg.le
  unfold Vsa.Sim.LayoutInstance.stackSL at hs hs2
  simp only at hs hs2
  have hs' : 0x87800000 + 1088 ≤ s.toNat := by omega
  have hsF : s - 1088#64 = s + 18446744073709550528#64 := evalSP_eq s
  have hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088 := by
    rw [← hsF]; exact toNat_sub_frame (by simp only [BitVec.toNat_ofNat]; omega)
  have hx1 := hn.lo; have hx2 := hn.hi; have hx3 := hn.off
  have hoff := evalSP_off (s := s) hsf (by omega)
  have hq1 := hslg.al; have hq2 := hslg.lo; have hq3 := hslg.hi
  have hneed' : 1088 ≤ evalNeed (.var x) d := by unfold envGetNeed at hneed; omega
  ihave ⟨Hst, HF⟩ := stackScratch_frame (f := 1088#64) hsg.le hneed' $$ Hst
  rw [hsF, hsf, show (1088#64).toNat = 1088 from rfl]
  ihave ⟨%Mt0, Hms, %hdj⟩ := ms_intro_sret $$ [Hpc Hra Hregs HF Hslot]
  · iframe Hpc Hra Hregs Hslot; unfold blockOwn; iexact HF
  -- run 1: prologue, kind dispatch, `env_get(env, name, sp + 240)`
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (wpW _) (F := iprop(leafErrCtx inp ∗ codeRes ∗ roOn P m ∗ frameAt env aE.toNat ∗
      stackScratch (s + 18446744073709550528#64) (evalNeed (.var x) d - 1088) ∗
      world N L Room inp .uncounted st d ∗
      ((PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ (∃ st' v, ⌜EvalE st d env (.var x) st' v⌝ ∗
          evalPost N L Room inp .uncounted st' d (.var x) v sret s rv) -∗
          (wpW (vsaModel live)).W Φ) ∧
        (abortAt (evalCore N L Room inp) s (evalNeed (.var x) d) ∗ slot24 sret.toNat -∗
          (wpW (vsaModel live)).W Φ))))
  rotate_left
  · iframe HE Hdv Hms Hcode Hro Hfb Hst Hw; iexact Hk
  intro F'
  unfold evalEntryPC
  refine {ARM}T_run1 hlive hsf hs' hs2 hs3 hx1 hx2 hx3 (by ix_reg; exact hregs.a0)
    (by ix_reg; exact hregs.a1) (by ix_reg; exact hregs.a2) (by ix_reg; exact hregs.a3)
    (by ix_reg; exact hregs.sp) hn.kind hn.kindu ?_
  intros
  apply swp_closeRM
  intro R1 Mt1 hR1 hMt1
  have hRA1 : ldv .ld Mt1 (s + 18446744073709550528#64 + 1080#64).toNat = ret := by
    subst hMt1; ix_fwd using [hoff]; ix_reg
  have hS01 : ldv .ld Mt1 (s + 18446744073709550528#64 + 1072#64).toNat = rv 8 := by
    subst hMt1; ix_fwd using [hoff]; ix_reg
  have hS11 : ldv .ld Mt1 (s + 18446744073709550528#64 + 1064#64).toNat = rv 9 := by
    subst hMt1; ix_fwd using [hoff]; ix_reg
  have hS21 : ldv .ld Mt1 (s + 18446744073709550528#64 + 1056#64).toNat = rv 18 := by
    subst hMt1; ix_fwd using [hoff]; ix_reg
  have e10 : R1 10 = aE := by subst hR1; ix_reg; try exact hregs.a3
  have e11 : R1 11 = BitVec.ofNat 64 q := by subst hR1; ix_reg; try exact hfs.ptr
  have e12 : R1 12 = s + 18446744073709550528#64 + 240#64 := by subst hR1; ix_reg
  have e2 : R1 2 = s + 18446744073709550528#64 := by subst hR1; ix_reg
  have e9 : R1 9 = sret := by subst hR1; ix_reg; try exact hregs.a0
  have hk1 : KeepRegs [19, 20, 21, 22, 23, 24, 25, 26, 27] rv R1 := by
    subst hR1; intro y hy
    simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_reg
  have ho : (R1 12).toNat = s.toNat - 1088 + 240 := by rw [e12]; exact hoff 240 (by decide)
  unfold F'
  iintro ⟨⟨#HE, #Hcode, #Hro, #Hfb, Hst, Hw, Hk⟩, Hms⟩
  -- `env_get`: the out slot lent from the frame, the store opened out of the world
  ihave ⟨Hms, Hout⟩ := ms_carveSlot (a := (R1 12).toNat) (fun b hb => by
    rw [ho] at hb; simp only [frS, VsaIris.InExt] at hb ⊢; omega) $$ Hms
  ihave ⟨Hslack, Hst⟩ := stackScratch_narrow (n := evalNeed (.var x) d - 1088) (m := envGetNeed)
    (by rw [hsf]; omega)
    (by omega) $$ Hst
  unfold world worldE
  icases Hw with ⟨%H, %B, Hh, Hs, Hc, Hio, Hi, %hB⟩
  ihave #Hget := hget
  unfold envGetSpec
  ihave #Hg := Hget $$ %st.store %B %env %x %(R1 10) %(R1 11) %(R1 12) %(R1 2)
    %(getSaved.map fun j => (j, R1 j)) %(by simp [getSaved])
  ihave #Hx := strAt_of_cstringWithin hfs.str (sharedWin_of_readOK hgeo) $$ Hro
  iapply ms_callEnv3 (wpW _) (i := 0x{J}) (entry := envGetPC) (R := R1)
    (jalx_{J} live (fun p hp => hlive _ (interp_code_{J} p hp)))
    interp_code_{J} (by decide)
    (φ := EnvSp (R1 2) envGetNeed ∧ SlotWin (R1 12).toNat)
    ⟨⟨(by rw [e2, hsf]; unfold htifLo envGetNeed; unfold Vsa.Sim.tohostAddr at *; omega),
       (by rw [e2, hsf]; omega), (by rw [e2, hsf]; omega)⟩,
     ⟨(by rw [ho]; omega), (by rw [ho]; omega),
       (by rw [ho]; unfold htifLo; unfold Vsa.Sim.tohostAddr at *; omega), (by rw [ho]; omega)⟩⟩
    (X := iprop(stackScratch (R1 2) envGetNeed ∗ frameAt env (R1 10).toNat ∗
      strAt (R1 11).toNat x ∗ slot24 (R1 12).toNat ∗ storeRepr N st.store B))
    (Y := fun res => iprop(stackScratch (R1 2) envGetNeed ∗ storeRepr N st.store B ∗
      getOut N st.store env x (R1 12) res))
  iframe Hg Hcode Hms Hs Hout
  isplitl [Hst]
  · rw [e2, e10, e11, hqt]; iframe Hst Hfb Hx
  iintro %R2 %hkeep2 ⟨Hst, Hs, Hget⟩ Hms
  rw [e2]
  ihave Hst := stackScratch_widen (n := evalNeed (.var x) d - 1088) (m := envGetNeed)
    (by rw [hsf]; omega) (by omega) $$ [Hslack Hst]
  · iframe Hslack Hst

#ix_piece {ARM}P_p2 from {ARM}P_p1 by
  by_cases hnone : st.store.get? env x = none
  · -- unbound: the slot back, `beqz` to the error arm, `runtime_error`
    unfold getOut
    rw [hnone]
    icases Hget with ⟨%hres, Hout⟩
    ihave ⟨%Mt2, Hms⟩ := ms_unslot (a := (R1 12).toNat) (S := frS (s.toNat - 1088) sret.toNat)
      (fun b hb => by rw [ho] at hb; simp only [frS, VsaIris.InExt] at hb ⊢; omega) $$ [Hms Hout]
    · iframe Hms Hout
    ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
    · iframe Hcode Hro
    iapply wp_swpF (wpW _) (F := iprop(leafErrCtx inp ∗ codeRes ∗ strAt q x ∗
        stackScratch (s + 18446744073709550528#64) (evalNeed (.var x) d - 1088) ∗
        world N L Room inp .uncounted st d ∗
        (abortAt (evalCore N L Room inp) s (evalNeed (.var x) d) ∗ slot24 sret.toNat -∗
            (wpW (vsaModel live)).W Φ)))
    rotate_left
    · ihave Hk := and_elim_r $$ Hk
      iframe HE Hdv Hms Hcode Hst Hk
      isplitr [Hh Hs Hc Hio Hi]
      · iapply strAt_of_cstringWithin hfs.str (sharedWin_of_readOK hgeo) $$ Hro
      unfold world worldE
      iexists H, B
      iframe Hh Hs Hc Hio Hi
      ipureintro; exact hB
    intro F'
    refine it_{R2} hlive (fun _ => ?_) (fun hc => absurd (by
      simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact hres) hc)
    refine {ARM}P_run3 (aX := aX) (s := s) (sret := sret) (inp := BitVec.ofNat 64 inp) hlive hsf hs'
      hs2 hs3 hx1 hx2 hx3 ?_ ?_ ?_ ?_
    · ix_reg; rw [hkeep2 8 (by decide) (by decide)]; subst hR1; ix_reg; try exact hregs.a2
    · ix_reg; rw [hkeep2 18 (by decide) (by decide)]; subst hR1; ix_reg; try exact hregs.a1
    · ix_reg; rw [hkeep2 2 (by decide) (by decide)]; exact e2
    intros
    apply swp_closeRM
    intro R3 Mt3 hR3 hMt3
    unfold F'
    iintro ⟨⟨#HE, #Hcode, #Hx, Hst, Hw, Hk⟩, Hms⟩
    iapply ev_rtErr (wpW _) (N := N) (L := L) (Room := Room) (inp := inp) HN hcl
      (jalx_{EJ} live (fun p hp => hlive _ (interp_code_{EJ} p hp))) interp_code_{EJ}
      (sret := sret) (s := s) (n := evalNeed (.var x) d) (p := q) (x := x)
      (fun hro hs => {FMTOK} hro hs 0#64) hfs.lt hsg
      (by have := hroom.room; unfold evalFrame at this; omega) hdj
      (R := R3) (M := Mt3)
      ⟨by subst hR3; ix_reg <;> rfl, by subst hR3; ix_reg <;> rfl, by subst hR3; ix_reg <;> rfl,
       by subst hR3; ix_reg; exact hfs.ptr, by subst hR3; ix_reg <;> rfl,
       by subst hR3; ix_reg; rw [hkeep2 2 (by decide) (by decide)]; exact e2⟩
    iframe HE Hcode Hx Hms Hst Hw Hk

#ix_piece {ARM}P_p3 from {ARM}P_p2 by
  -- found
  obtain ⟨v, hgv⟩ := Option.ne_none_iff_exists'.mp hnone
  unfold getOut
  rw [hgv]
  icases Hget with ⟨%hres, Hval⟩
  ihave ⟨%w0, %w1, %w2, #Hv, Hms⟩ := ms_joinSlot N (a := (R1 12).toNat)
    (S := frS (s.toNat - 1088) sret.toNat) (fun b hb => by
    rw [ho] at hb; simp only [frS, VsaIris.InExt] at hb ⊢; omega) $$ [Hms Hval]
  · iframe Hms Hval
  -- run 2: copy the found value into `sret`, the epilogue
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (wpW _) (F := iprop(codeRes ∗ roOn P m ∗ frameAt env aE.toNat ∗
      stackScratch (s + 18446744073709550528#64) (evalNeed (.var x) d - 1088) ∗
      world N L Room inp .uncounted st d ∗ □ valOf N v w0 w1 w2 ∗
      ((PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ (∃ st' v, ⌜EvalE st d env (.var x) st' v⌝ ∗
          evalPost N L Room inp .uncounted st' d (.var x) v sret s rv) -∗
          (wpW (vsaModel live)).W Φ) ∧
        (abortAt (evalCore N L Room inp) s (evalNeed (.var x) d) ∗ slot24 sret.toNat -∗
          (wpW (vsaModel live)).W Φ))))
  rotate_left
  · iframe Hdv Hms Hcode Hro Hfb Hst Hv Hk
    unfold world worldE
    iexists H, B
    iframe Hh Hs Hc Hio Hi
    ipureintro; exact hB
  intro F'
  -- `beqz a0`: found
  refine it_{R2} hlive (fun hc => by
    simp only [upd_apply, Nat.reduceEqDiff, ite_false] at hc; rw [hres] at hc; exact absurd hc (by decide))
    (fun hnz => ?_)
  refine {ARM}T_run2 (aX := aX) (s := s) (sret := sret) (ret := ret) (v8 := rv 8) (v9 := rv 9)
    (v18 := rv 18) (w0 := w0) (w1 := w1) (w2 := w2) hlive hsf hs' hs2 hs3 hal hq1 hq2 hq3
    (inExt_disj (by decide) (by decide) hdj) (toNat_add_field (by omega) (by decide))
    (toNat_add_field (by omega) (by decide)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · ix_reg; rw [hkeep2 9 (by decide) (by decide)]; exact e9
  · ix_reg; rw [hkeep2 2 (by decide) (by decide)]; exact e2
  · rw [hoff 240 (by decide), ho]; unfold slotWrite; ix_fwd
  · rw [hoff 248 (by decide), ho]; unfold slotWrite; ix_fwd
  · rw [hoff 256 (by decide), ho]; unfold slotWrite; ix_fwd
  · rw [hoff 1080 (by decide), ho]; unfold slotWrite; ix_fwd; rw [← hoff 1080 (by decide)]; exact hRA1
  · rw [hoff 1072 (by decide), ho]; unfold slotWrite; ix_fwd; rw [← hoff 1072 (by decide)]; exact hS01
  · rw [hoff 1064 (by decide), ho]; unfold slotWrite; ix_fwd; rw [← hoff 1064 (by decide)]; exact hS11
  · rw [hoff 1056 (by decide), ho]; unfold slotWrite; ix_fwd; rw [← hoff 1056 (by decide)]; exact hS21
  intros
  apply swp_closeM
  intro Mt3 hMt3
  unfold F'
  iintro ⟨⟨#Hcode, #Hro, #Hfb, Hst, Hw, #Hv, Hk⟩, Hms⟩

#ix_piece {ARM}P_p4 from {ARM}P_p3 by
  have eW0 : imgW (imgM Mt3) sret.toNat = w0 := by
    rw [← ldv_ld_imgW]; subst hMt3; ix_fwd
  have eW1 : imgW (imgM Mt3) (sret.toNat + 8) = w1 := by
    rw [← ldv_ld_imgW]; subst hMt3; ix_fwd
  have eW2 : imgW (imgM Mt3) (sret.toNat + 16) = w2 := by
    rw [← ldv_ld_imgW]; subst hMt3; ix_fwd
  ihave ⟨Hpc, Hra, Hregs, HS, Hval⟩ := ms_exit_sret N hdj $$ [Hms]
  · iframe Hms
    unfold valImg
    rw [eW0, eW1, eW2]
    iexact Hv
  ihave Hst := evalFrame_join hsg.le hneed' $$ [Hst HS]
  · iframe Hst HS
  ihave Hra := ptsto_eq (show _ = ret by ix_reg) $$ Hra
  ihave Hk := and_elim_l $$ Hk
  iapply Hk $$ Hpc Hra
  iexists st, v
  isplitl []
  · ipureintro; exact EvalE.var st d env x v hgv
  unfold evalPost
  iexists _
  iframe Hregs Hst Hval Hw
  ipureintro
  intro y hy
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · ix_reg; exact evalSP_restore s |>.trans hregs.sp.symm
  all_goals ix_keep [hkeep2, hk1]


#ix_chain caseP_{ARM} := [{ARM}P_p1, {ARM}P_p2, {ARM}P_p3, {ARM}P_p4]

end VsaIris.Interp
