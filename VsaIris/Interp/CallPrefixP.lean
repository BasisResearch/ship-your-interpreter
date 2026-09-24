import VsaIris.Interp.CallSeg
import VsaIris.Interp.CallErr

/-!
# The call arm's prefix, partial mode (lane E4)

`callPrefixP`: as `callPrefixT` (`CallPrefix.lean`), outcome-quantified: the
callee through the Löb hypothesis (`ms_callEvalP`), the argument loop through
E6's `evalArgsP_body`, and the too-many-arguments error (`interp.c:251`):
`runtime_error(in, line, "too many arguments (max 32)", 0, 0)` (E2's
`ms_rtErrEval`), which aborts. The continuation `CallK254P` receives the
derivations of the callee and the arguments and the arm's additive pair back.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Newlib
open Vsa.MemRepr Vsa.Sim Vsa.While
open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.RuntimeRepr


/-- A call node's budget leaves `runtime_error` room below the arm's frame. -/
theorem evalNeed_call_rtErr (f : Expr) (args : List Expr) (d : Nat) :
    1088 + RtErr.rtErrNeed ≤ evalNeed (.call f args) d := by
  have := evalNeed_call_fn f args d; have := Expr.stackNeed_ge f
  unfold evalNeed stackBudget at *; unfold RtErr.rtErrNeed snprintfNeed evalFrame at *; omega

/-- A call node's budget: its own frame, a child's frame, and the leaf
headroom (`3 * evalFrame`). -/
theorem evalNeed_call_ge (f : Expr) (args : List Expr) (d : Nat) :
    3264 ≤ evalNeed (.call f args) d := by
  have := evalNeed_call_fn f args d; have := Expr.stackNeed_ge f
  unfold evalNeed stackBudget at *; unfold evalFrame at *; omega

section Defs

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

/-- The continuation of the call prefix, partial mode: the state at the kind
dispatch with the callee's and the arguments' derivations, the result slot
and the arm's pair (return, abort) back. -/
def CallK254P (live : Nat → Prop) (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (inp : Nat)
    (Core : IProp GF) (Φ : Nat × String → IProp GF) (st : St) (d env : Nat) (f : Expr)
    (args : List Expr) (s aX sret ret : BitVec 64) (rv : Nat → BitVec 64) (n : Nat)
    (Kret : IProp GF) : IProp GF :=
  iprop(∀ (R : Nat → BitVec 64) (Mt : Mem) (w0 w1 w2 : BitVec 64) (st1 : St) (fv : Value)
      (st2 : St) (vs : List Value),
    ⌜EvalE st d env f st1 fv ∧ EvalArgs st1 d env args st2 vs ∧ args.length ≤ maxArgs⌝ -∗
    ⌜CallAt R Mt s aX sret (BitVec.ofNat 64 inp) ret rv w0 w1 w2 args.length⌝ -∗
    □ valOf N fv w0 w1 w2 -∗ argVals N (imgM Mt) (argsBase s) 0 vs -∗
    ms 0x80003254#64 R (InExt (s.toNat - 1088, 1088)) Mt -∗
    stackScratch (s + 18446744073709550528#64) (n - 1088) -∗
    world N L Room inp .uncounted st2 d -∗ slot24 sret.toNat -∗
    (Kret ∧ (iprop(abortAt Core s n ∗ slot24 sret.toNat) -∗ (wpW (vsaModel live)).W Φ)) -∗
    (wpW (vsaModel live)).W Φ)

end Defs

section CloP

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

/-- **The closure call from the kind dispatch, partial mode** (the call arm's
closure branch; proved by the closure tail). -/
def CallCloP (live : Nat → Prop) (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (inp : Nat)
    (Core : IProp GF) : Prop :=
  ∀ (Φ : Nat × String → IProp GF) (st : St) (d env : Nat) (f : Expr) (args : List Expr)
    (sret aE aX s ret w0 w1 w2 : BitVec 64) (rv R : Nat → BitVec 64) (Mt : Mem) (st1 st2 : St)
    (vs : List Value) (ca : Nat),
    EvalRegs rv sret (BitVec.ofNat 64 inp) aX aE s → StackGeom s (evalNeed (.call f args) d) →
    (Expr.call f args).bodiesBound perCallBudget = true → ret.toNat % 4 = 0 → SlotGeom sret →
    EvalE st d env f st1 (.closure ca) → EvalArgs st1 d env args st2 vs → args.length ≤ maxArgs →
    CallAt R Mt s aX sret (BitVec.ofNat 64 inp) ret rv w0 w1 w2 args.length →
    (evalSpecsP (vsaModel live) N L Room inp Core ∗ execSpecsP (vsaModel live) N L Room inp Core ∗
      errCtx inp ∗ codeRes ∗
      □ astEG aX.toNat (.call f args) ∗ □ frameAt env aE.toNat ∗ □ valOf N (.closure ca) w0 w1 w2 ∗
      argVals N (imgM Mt) (argsBase s) 0 vs ∗ ms 0x80003254#64 R (InExt (s.toNat - 1088, 1088)) Mt ∗
      stackScratch (s + 18446744073709550528#64) (evalNeed (.call f args) d - 1088) ∗
      world N L Room inp .uncounted st2 d ∗ slot24 sret.toNat ∗
      ((PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ (∃ st' v, ⌜EvalE st d env (.call f args) st' v⌝ ∗
          evalPost N L Room inp .uncounted st' d (.call f args) v sret s rv) -∗
          (wpW (vsaModel live)).W Φ) ∧
        (iprop(abortAt Core s (evalNeed (.call f args) d) ∗ slot24 sret.toNat) -∗
          (wpW (vsaModel live)).W Φ))
      ⊢ (wpW (vsaModel live)).W Φ)

end CloP

#ix_piece callPrefixP_p1 {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat} {Core : IProp GF}
    (hE : ErrEnv N L Room inp live Core)
    {st : St} {d env : Nat} {f : Expr} {args : List Expr}
    (ha : evalArgsP_body (GF := GF) live N L Room inp Core d env args)
    {Φ : Nat × String → IProp GF} {Kret : IProp GF} {sret aE aX s ret : BitVec 64}
    {rv : Nat → BitVec 64}
    (hregs : EvalRegs rv sret (BitVec.ofNat 64 inp) aX aE s)
    (hsg : StackGeom s (evalNeed (.call f args) d))
    (hbb : (Expr.call f args).bodiesBound perCallBudget = true) :
    evalSpecsP (vsaModel live) N L Room inp Core ∗ errCtx inp ∗
      PC ↦ᵣ evalEntryPC ∗ ra ↦ᵣ ret ∗ regFile rv ∗ codeRes ∗ □ astEG aX.toNat (.call f args) ∗
      □ frameAt env aE.toNat ∗ stackScratch s (evalNeed (.call f args) d) ∗
      world N L Room inp .uncounted st d ∗ slot24 sret.toNat ∗
      (Kret ∧ (iprop(abortAt Core s (evalNeed (.call f args) d) ∗ slot24 sret.toNat) -∗
        (wpW (vsaModel live)).W Φ)) ∗
      CallK254P live N L Room inp Core Φ st d env f args s aX sret ret rv
        (evalNeed (.call f args) d) Kret
    ⊢ (wpW (vsaModel live)).W Φ by
  iintro ⟨#IH, #HE, Hpc, Hra, Hregs, #Hcode, #Hast, #Hfb, Hst, Hw, Hslot, Hk, HK⟩
  unfold astEG
  icases Hast with ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩
  obtain ⟨aF, hn, hrf, haF⟩ := callNode_of_repr hrepr hgeo
  have hneed : 1088 ≤ evalNeed (.call f args) d := by
    have := Expr.stackNeed_ge (.call f args); unfold evalNeed stackBudget; unfold evalFrame at this; omega
  have hs := hsg.lo; have hs2 := hsg.hi; have hs3 := hsg.al; have hs4 := hsg.le
  unfold Vsa.Sim.LayoutInstance.stackSL at hs hs2
  simp only at hs hs2
  have hs' : 0x87800000 + 1088 ≤ s.toNat := by omega
  have hsF : s - 1088#64 = s + 18446744073709550528#64 := evalSP_eq s
  have hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088 := by
    rw [← hsF]; exact toNat_sub_frame (by simp only [BitVec.toNat_ofNat]; omega)
  have hfg : EvalFrameG s := ⟨hsf, hs', hs2, hs3⟩
  have gF := evalCallGeom (o := 96) hsg
    (by have := evalNeed_call_fn f args d; unfold evalFrame at this; omega) (by decide) (by decide)
  obtain ⟨hbf, hba⟩ := Expr.bodiesBound_call hbb
  have hFt : (BitVec.ofNat 64 aF).toNat = aF := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt haF]
  have hoff := evalSP_off (s := s) hsf (by omega)
  ihave ⟨Hst, HF⟩ := stackScratch_frame (f := 1088#64) hsg.le hneed $$ Hst
  rw [hsF, hsf, show (1088#64).toNat = 1088 from rfl]
  ihave ⟨%Mt0, Hms⟩ := ms_intro $$ [Hpc Hra Hregs HF]
  · iframe Hpc Hra Hregs; unfold blockOwn; iexact HF
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply callSegA hlive (wpW _) hregs hn hfg
  iframe Hdv Hms
  iintro %R1 %Mt1 %⟨hA, hra1⟩ Hms
  -- the callee, through the Löb hypothesis
  ihave Hf := evalSpecsP_at Core st d env f $$ IH
  iapply ms_callEvalP (N := N) (L := L) (Room := Room) (inp := inp) (i := 0x800031bc)
    (jalx_800031bc live (fun p hp => hlive _ (interp_code_800031bc p hp)))
    interp_code_800031bc (by decide) (Core := Core) (st := st) (d := d) (env := env) (e := f)
    (slot := s + 18446744073709550528#64 + 96#64) (aC := BitVec.ofNat 64 aF) (aE := aE)
    (s0 := s) (sret0 := sret) (m := evalNeed (.call f args) d - 1088)
    (n0 := evalNeed (.call f args) d) (Out := slot24 sret.toNat) (Kret := Kret) .rfl
    gF.child gF.fits gF.below (by omega) hsg.le gF.slotGeom hbf
  iframe Hf Hcode Hfb Hms Hst Hw Hslot Hk
  isplitl []
  · ipureintro
    refine ⟨hA.args, fun b hb => ?_⟩
    have g1 := gF.slot; have g2 := gF.sp; simp only [VsaIris.InExt, evalSP] at hb g1 g2 ⊢; omega
  isplitl []
  · imodintro; rw [hFt]; iapply astEG_of_view hrf hgeo $$ Hro
  iintro %R1' %w0 %w1 %w2 %st1 %fv %hEf %hkeep1 #Hv1 Hms Hst Hw Hslot Hk


#ix_piece callPrefixP_p2 from callPrefixP_p1 by
  -- the count test and its three exits
  have h8 : upd R1' 1 (BitVec.ofNat 64 (0x800031bc + 4)) 8 = aX := by
    ix_reg; rw [hkeep1 8 (by decide)]; exact hA.s0
  have h2 : upd R1' 1 (BitVec.ofNat 64 (0x800031bc + 4)) 2 = s + 18446744073709550528#64 := by
    ix_reg; rw [hkeep1 2 (by decide)]; exact hA.args.sp
  have henv : ldv .ld (slotWrite Mt1 (s + 18446744073709550528#64 + 96#64).toNat w0 w1 w2)
      (s.toNat - 1088) = aE := by
    rw [show s.toNat - 1088 = (s + 18446744073709550528#64 + 0#64).toNat by rw [BitVec.add_zero, hsf]]
    ix_fwd; rw [BitVec.add_zero, hsf]; exact hA.env
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply callSegB hlive (wpW _) hn hfg h8 h2 henv
  iframe Hdv Hms
  isplit
  rotate_left
  isplit
  rotate_left
  all_goals iintro %R2 %Mt2 %hB Hms


#ix_piece callPrefixP_p3 from callPrefixP_p2 by
  -- the argument loop (E6)
  obtain ⟨hpos, hle, hB⟩ := hB
  have hne : args ≠ [] := by intro h; subst h; simp at hpos
  ihave #Hast := astEG_of_view hrepr hgeo $$ Hro
  have hall : ∀ x ∈ args, evalNeed x d ≤ evalNeed (.call f args) d - 1088 ∧
      x.bodiesBound perCallBudget = true := fun x hx =>
    ⟨by have := evalNeed_call_arg (f := f) hx d; unfold evalFrame at this; omega,
     Expr.bodiesBoundList_mem hba hx⟩
  have kr : ∀ x ∈ calleeSaved, R2 x = R1 x := fun x hx => by
    rw [hB.keep x hx, upd_apply, if_neg ((by decide : ∀ y ∈ calleeSaved, y ≠ 1) x hx), hkeep1 x hx]
  have hhead : ArgsHead R2 s aX (BitVec.ofNat 64 inp) aE 0 args.length :=
    ⟨(kr 2 (by decide)).trans hA.args.sp, (kr 8 (by decide)).trans hA.s0,
      (kr 18 (by decide)).trans hA.s2, hB.a3, hB.a6, hB.a5⟩
  iapply ha Φ st1 0 f args [] aX aE s sret R2 Mt2 (evalNeed (.call f args) d - 1088)
    (evalNeed (.call f args) d) (slot24 sret.toNat) hne List.drop_zero.symm rfl hle hhead hfg
    (stackGeom_evalSP hsg hneed hsf) (by omega) hall .rfl
  iframe Hms Hcode Hast Hfb Hst Hw Hslot IH
  isplitl []
  · unfold argVals; iempintro
  isplit
  · simp only [List.nil_append]
    iintro %R' %Mt' %st2 %vs %hEa %⟨hk', h16, hU⟩ Hms Hargs Hst Hw Hslot
    unfold CallK254P
    iapply HK $$ %R' %Mt' %w0 %w1 %w2 %st1 %fv %st2 %vs %⟨hEf, hEa, by unfold maxArgs; omega⟩
      %(CallAt.of_seg hfg hA hkeep1 hB hU hk') Hv1 Hargs Hms Hst Hw Hslot Hk
  · iintro H
    ihave Hk := and_elim_r $$ Hk
    iapply Hk $$ H


#ix_piece callPrefixP_p2c from callPrefixP_p2 at 3 by
  -- no arguments: straight to the dispatch
  obtain ⟨hz, hB⟩ := hB
  have hnil : args = [] := List.eq_nil_of_length_eq_zero hz
  subst hnil
  unfold CallK254P
  iapply HK $$ %R2 %Mt2 %w0 %w1 %w2 %st1 %fv %st1 %([] : List Value) %⟨hEf, .nil _ _ _, by simp [maxArgs]⟩
    %(CallAt.of_seg hfg hA hkeep1 hB (Untouched.refl _ _ _) (fun _ _ => rfl)) Hv1 [] Hms Hst Hw
    Hslot Hk
  unfold argVals; iempintro

#ix_piece callPrefixP_p2b from callPrefixP_p2 at 2 by
  -- more than 32 arguments: `runtime_error`
  obtain ⟨hgt, hR2, hMt2⟩ := hB
  have h8' : R2 8 = aX := (hR2 8 (by decide) (by decide)).trans h8
  have h2' : R2 2 = s + 18446744073709550528#64 := (hR2 2 (by decide) (by decide)).trans h2
  have h18' : R2 18 = BitVec.ofNat 64 inp := by
    rw [hR2 18 (by decide) (by decide)]; ix_reg; rw [hkeep1 18 (by decide)]; exact hA.s2
  have hs'' := hs'
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF (wpW _) (F := iprop(errCtx inp ∗ codeRes ∗
      stackScratch (s + 18446744073709550528#64) (evalNeed (.call f args) d - 1088) ∗
      world N L Room inp .uncounted st1 d ∗ slot24 sret.toNat ∗
      (Kret ∧ (iprop(abortAt Core s (evalNeed (.call f args) d) ∗ slot24 sret.toNat) -∗
        (wpW (vsaModel live)).W Φ))))
  rotate_left
  · iframe Hdv Hms HE Hcode Hst Hw Hslot; iexact Hk
  intro F'
  refine Call_runTM hlive hsf hs'' hs2 hs3 hn.lo hn.hi hn.off h8' h2' ?_
  intro vl
  apply swp_closeRM
  intro R3 Mt3 hR3 hMt3
  unfold F'
  iintro ⟨⟨#HE, #Hcode, Hst, Hw, Hslot, Hk⟩, Hms⟩
  ihave #Himg := errCtx_img inp $$ HE
  ihave #Hrd := readable_rodata $$ Himg
  iapply ms_rtErrEval (wpW _) hE (jalx_80003fdc live (fun p hp => hlive _ (interp_code_80003fdc p hp)))
    interp_code_80003fdc (readable_rodata_fmt (fun hro => tooMany_fmt hro 0#64 0#64)) hsg
    (evalNeed_call_rtErr f args d) (R := R3) (line := vl)
  iframe Hcode HE Hrd Hms Hst Hw
  isplitl []
  · ipureintro
    subst hR3
    exact ⟨by ix_reg; exact h18', by ix_reg, by ix_reg, by ix_reg, by ix_reg, by ix_reg; exact h2'⟩
  iintro Hab
  ihave Hk := and_elim_r $$ Hk
  iapply Hk
  iframe Hab Hslot

#ix_chain callPrefixP_c := [callPrefixP_p1, callPrefixP_p2, callPrefixP_p3]


/-- **The call prefix, partial mode**: from `eval_expr`'s entry on a call node,
with the Löb hypothesis, the error context and the argument loop (E6), the
arm reaches the kind dispatch (`CallK254P`) or aborts (more than 32
arguments, or a child's abort). -/
theorem callPrefixP {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat} {Core : IProp GF}
    (hE : ErrEnv N L Room inp live Core)
    {st : St} {d env : Nat} {f : Expr} {args : List Expr}
    (ha : evalArgsP_body (GF := GF) live N L Room inp Core d env args)
    {Φ : Nat × String → IProp GF} {Kret : IProp GF} {sret aE aX s ret : BitVec 64}
    {rv : Nat → BitVec 64}
    (hregs : EvalRegs rv sret (BitVec.ofNat 64 inp) aX aE s)
    (hsg : StackGeom s (evalNeed (.call f args) d))
    (hbb : (Expr.call f args).bodiesBound perCallBudget = true) :
    evalSpecsP (vsaModel live) N L Room inp Core ∗ errCtx inp ∗
      PC ↦ᵣ evalEntryPC ∗ ra ↦ᵣ ret ∗ regFile rv ∗ codeRes ∗ □ astEG aX.toNat (.call f args) ∗
      □ frameAt env aE.toNat ∗ stackScratch s (evalNeed (.call f args) d) ∗
      world N L Room inp .uncounted st d ∗ slot24 sret.toNat ∗
      (Kret ∧ (iprop(abortAt Core s (evalNeed (.call f args) d) ∗ slot24 sret.toNat) -∗
        (wpW (vsaModel live)).W Φ)) ∗
      CallK254P live N L Room inp Core Φ st d env f args s aX sret ret rv
        (evalNeed (.call f args) d) Kret
    ⊢ (wpW (vsaModel live)).W Φ :=
  callPrefixP_c hlive hE ha hregs hsg hbb (callPrefixP_p2b hlive hE ha hregs hsg hbb)
    (callPrefixP_p2c hlive hE ha hregs hsg hbb)

end VsaIris.Interp
