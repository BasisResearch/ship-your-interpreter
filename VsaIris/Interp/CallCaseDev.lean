import VsaIris.Interp.CallNotCallable
import VsaIris.Interp.CallPrefixP

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim Vsa.While
open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.RuntimeRepr

theorem caseT_CallPrint {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {st st1 st2 : St} {d env : Nat} {f : Expr} {args : List Expr} {vs : List Value} {nf na : Nat}
    (hN : NativeEntries N) (hd : DispSupply (GF := GF) N)
    (Df : EvalECost st d env f st1 (.native .print) nf) (hlen : args.length ≤ maxArgs)
    (Da : EvalArgsCost st1 d env args st2 vs na)
    (hf : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env f st1 (.native .print) nf Df)
    (ha : evalArgsT_body (GF := GF) live N L Room inp st1 d env args st2 vs na)
    (hnp : ∀ sret args s vs st o,
      ⊢ nativePrintSpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) sret args s vs st o)
    (hroom : nativePrintNeed + 1088 ≤ evalNeed (.call f args) d) :
    ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env (.call f args)
        ⟨st2.store, st2.out ++ printArgs st2.store vs⟩ .null (nf + na + 0)
        (.call st d env f args st1 st2 _ (.native .print) vs .null nf na 0 Df hlen Da
          (.print st2 d vs)) := by
  have hspec : ⊢ NatOutSpecs (GF := GF) live N (twpW (vsaModel live)) nativePrintPC nativePrintNeed
      (fun st vs o => o ++ printArgs st vs) :=
    natOutSpecs_of N _ (fun a b c vs st o => by rw [← nativePrintSpec_eq]; exact hnp a b c vs st o)
  have hvl : vs.length = args.length := evalArgsCost_length Da
  unfold evalSpecT_body fnSpecW
  iintro %k %sret %aE %aX %s %rv !> %ret %Φ Hpc Hra ⟨%hal, Hpre⟩ Hk
  unfold evalPre
  icases Hpre with ⟨Hregs, %hregs, #Hcode, #Hast, #Hfb, Hst, %hsg, Hslot, %hslg, %hbb, Hw⟩
  have hneed : 1088 ≤ evalNeed (.call f args) d := by
    have := Expr.stackNeed_ge (.call f args); unfold evalNeed stackBudget; unfold evalFrame at this; omega
  rw [Nat.add_zero]
  ihave #Hsp := hspec
  iapply callPrefixT hlive Df hlen Da hf ha hregs hsg hbb hal
  iframe Hpc Hra Hregs Hcode Hast Hfb Hst Hw
  unfold CallK254T
  iintro %R %Mt %w0 %w1 %w2 %hcall #Hv Hav Hms Hst Hw
  rw [← hvl] at hcall
  iapply callNativeOut hlive (twpW (vsaModel live)) (nf := .print) (entry := nativePrintPC)
    (by show N.print = _; rw [hN.print]; rfl) (by decide) (by unfold maxArgs at hlen; omega) hsg hneed hroom hslg hal hd
    hregs.sp hcall
  iframe Hsp Hcode Hast Hv Hav Hms Hst Hw Hslot
  unfold CallExitK
  iintro %rv' %hkeep Hregs Hst Hval Hw Hpc Hra
  iapply Hk $$ Hpc Hra
  unfold evalPost
  iexists rv'
  iframe Hregs Hst Hval Hw
  ipureintro; exact hkeep


theorem caseT_CallAssert {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {st st1 st2 : St} {d env : Nat} {f : Expr} {args : List Expr} {vs : List Value} {nf na : Nat}
    {v m : Value} (hvm : vs = [v] ∨ vs = [v, m]) (htr : v.truthy = true)
    (hN : NativeEntries N) (hinp : Newlib.RtErr.InpGeom (BitVec.ofNat 64 inp)) (hinpLt : inp < 2 ^ 64)
    (Df : EvalECost st d env f st1 (.native .assert) nf) (hlen : args.length ≤ maxArgs)
    (Da : EvalArgsCost st1 d env args st2 vs na)
    (hf : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env f st1 (.native .assert) nf Df)
    (ha : evalArgsT_body (GF := GF) live N L Room inp st1 d env args st2 vs na)
    (hna : ∀ sret inp args s line vs ρ st d jb,
      ⊢ nativeAssertSpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) L Room sret inp args s
        line vs ρ st d jb) :
    ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env (.call f args) st2 .null (nf + na + 0)
        (.call st d env f args st1 st2 _ (.native .assert) vs .null nf na 0 Df hlen Da
          (.assertOk st2 d vs v m hvm htr)) := by
  have hvl : vs.length = args.length := evalArgsCost_length Da
  unfold evalSpecT_body fnSpecW
  iintro %k %sret %aE %aX %s %rv !> %ret %Φ Hpc Hra ⟨%hal, Hpre⟩ Hk
  unfold evalPre
  icases Hpre with ⟨Hregs, %hregs, #Hcode, #Hast, #Hfb, Hst, %hsg, Hslot, %hslg, %hbb, Hw⟩
  have hneed := evalNeed_call_ge f args d
  rw [Nat.add_zero]
  iapply callPrefixT hlive Df hlen Da hf ha hregs hsg hbb hal
  iframe Hpc Hra Hregs Hcode Hast Hfb Hst Hw
  unfold CallK254T
  iintro %R %Mt %w0 %w1 %w2 %hcall #Hv Hav Hms Hst Hw
  rw [← hvl] at hcall
  iapply callNativeAssert hlive (twpW (vsaModel live)) hna hN.assert hinp hinpLt
    (by unfold maxArgs at hlen; omega) hsg
    (by unfold nativeAssertNeed Newlib.RtErr.rtErrNeed Newlib.snprintfNeed; omega)
    hslg hal hregs.sp hcall
  iframe Hcode Hast Hv Hav Hms Hst Hw Hslot
  isplit
  · iintro %rv' %_ %hkeep Hregs Hst Hval Hw Hpc Hra
    iapply Hk $$ Hpc Hra
    unfold evalPost
    iexists rv'
    iframe Hregs Hst Hval Hw
    ipureintro; exact hkeep
  · iintro %hno
    exfalso; exact hno ⟨v, m, hvm, htr⟩


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
    (evalSpecsP (vsaModel live) N L Room inp Core ∗ errCtx inp ∗ codeRes ∗
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

theorem caseP_Call {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat} {Core : IProp GF}
    {st : St} {d env : Nat} {f : Expr} {args : List Expr}
    (hE : ErrEnv (GF := GF) N L Room inp live Core) (hN : NativeEntries N) (hd : DispSupply (GF := GF) N)
    (ha : evalArgsP_body (GF := GF) live N L Room inp Core d env args)
    (hvk : ⊢ ∀ p Mt v, valueKindNameSpec (GF := GF) (vsaModel live) (wpW (vsaModel live)) p Mt v)
    (hnp : ∀ sret args s vs st o,
      ⊢ nativePrintSpec (GF := GF) (vsaModel live) N (wpW (vsaModel live)) sret args s vs st o)
    (hnpl : ∀ sret args s vs st o,
      ⊢ nativePrintlnSpec (GF := GF) (vsaModel live) N (wpW (vsaModel live)) sret args s vs st o)
    (hna : ∀ sret inp args s line vs ρ st d jb,
      ⊢ nativeAssertSpec (GF := GF) (vsaModel live) N (wpW (vsaModel live)) L Room sret inp args s
        line vs ρ st d jb)
    (hroom : nativePrintlnNeed + 1088 ≤ evalNeed (.call f args) d)
    (hclo : CallCloP (GF := GF) live N L Room inp Core) :
    evalSpecsP (GF := GF) (vsaModel live) N L Room inp Core ∗ errCtx (GF := GF) inp ⊢
      evalSpecP_body (GF := GF) (vsaModel live) N L Room inp Core st d env (.call f args) := by
  have hsp1 : ⊢ NatOutSpecs (GF := GF) live N (wpW (vsaModel live)) nativePrintPC nativePrintNeed
      (fun st vs o => o ++ printArgs st vs) :=
    natOutSpecs_of N _ (fun a b c vs st o => by rw [← nativePrintSpec_eq]; exact hnp a b c vs st o)
  have hsp2 : ⊢ NatOutSpecs (GF := GF) live N (wpW (vsaModel live)) nativePrintlnPC nativePrintlnNeed
      (fun st vs o => o ++ printArgs st vs ++ "\n") :=
    natOutSpecs_of N _ (fun a b c vs st o => by rw [← nativePrintlnSpec_eq]; exact hnpl a b c vs st o)
  have hneed := evalNeed_call_ge f args d
  have hinpN : (BitVec.ofNat 64 inp).toNat = inp := Nat.mod_eq_of_lt hE.inpLt
  iintro ⟨#IH, #HE⟩
  unfold evalSpecP_body fnSpecAbort
  iintro %sret %aE %aX %s %rv !> %ret %Φ Hpc Hra ⟨%hal, Hpre⟩ Hk
  unfold evalPre
  icases Hpre with ⟨Hregs, %hregs, #Hcode, #Hast, #Hfb, Hst, %hsg, Hslot, %hslg, %hbb, Hw⟩
  iapply callPrefixP hlive hE ha hregs hsg hbb (Kret := iprop(PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗
    (∃ st' v, ⌜EvalE st d env (.call f args) st' v⌝ ∗
      evalPost N L Room inp .uncounted st' d (.call f args) v sret s rv) -∗ (wpW (vsaModel live)).W Φ))
  iframe IH HE Hpc Hra Hregs Hcode Hast Hfb Hst Hw Hslot Hk
  unfold CallK254P
  iintro %R %Mt %w0 %w1 %w2 %st1 %fv %st2 %vs %⟨hEf, hEa, hlen⟩ %hcall #Hv Hav Hms Hst Hw Hslot Hk
  have hvl : vs.length = args.length := evalArgs_length hEa
  rw [← hvl] at hcall
  by_cases hnc : NotCallable fv
  · iapply callNotCallable hlive (wpW (vsaModel live)) hE hvk hnc hsg
      (evalNeed_call_rtErr f args d) hcall
    iframe Hcode HE Hast Hv Hms Hst Hw
    iintro Hab
    ihave Hk := and_elim_r $$ Hk
    iapply Hk
    iframe Hab Hslot
  cases fv with
  | closure ca =>
    rw [hvl] at hcall
    iapply hclo Φ st d env f args sret aE aX s ret w0 w1 w2 rv R Mt st1 st2 vs ca hregs hsg hbb hal
      hslg hEf hEa hlen hcall
    iframe IH HE Hcode Hast Hfb Hv Hav Hms Hst Hw Hslot Hk
  | native nf =>
    cases nf with
    | print =>
      iapply callNativeOut hlive (wpW (vsaModel live)) (nf := .print) (entry := nativePrintPC)
        (out := fun st vs o => o ++ printArgs st vs) (need := nativePrintNeed)
        (by show N.print = _; rw [hN.print]; rfl) (by decide) (by unfold maxArgs at hlen; omega)
        hsg (by omega) (by unfold nativePrintlnNeed at hroom; omega) hslg hal hd hregs.sp hcall
      ihave #Hsp := hsp1
      isplitl []
      · iexact Hsp
      iframe Hcode Hast Hv Hav Hms Hst Hw Hslot
      unfold CallExitK
      iintro %rv' %hkeep Hregs Hst Hval Hw Hpc Hra
      ihave Hk := and_elim_l $$ Hk
      iapply Hk $$ Hpc Hra
      iexists _, .null
      isplitl []
      · ipureintro; exact .call _ _ _ _ _ _ _ _ _ _ _ hEf hlen hEa (.print _ _ _)
      unfold evalPost
      iexists rv'
      iframe Hregs Hst Hval Hw
      ipureintro; exact hkeep
    | println =>
      iapply callNativeOut hlive (wpW (vsaModel live)) (nf := .println) (entry := nativePrintlnPC)
        (out := fun st vs o => o ++ printArgs st vs ++ "\n") (need := nativePrintlnNeed)
        (by show N.println = _; rw [hN.println]; rfl) (by decide) (by unfold maxArgs at hlen; omega)
        hsg (by omega) hroom hslg hal hd hregs.sp hcall
      ihave #Hsp := hsp2
      isplitl []
      · iexact Hsp
      iframe Hcode Hast Hv Hav Hms Hst Hw Hslot
      unfold CallExitK
      iintro %rv' %hkeep Hregs Hst Hval Hw Hpc Hra
      ihave Hk := and_elim_l $$ Hk
      iapply Hk $$ Hpc Hra
      iexists _, .null
      isplitl []
      · ipureintro; exact .call _ _ _ _ _ _ _ _ _ _ _ hEf hlen hEa (.println _ _ _)
      unfold evalPost
      iexists rv'
      iframe Hregs Hst Hval Hw
      ipureintro; exact hkeep
    | assert =>
      iapply callNativeAssert hlive (wpW (vsaModel live)) hna hN.assert hE.inpGeom hE.inpLt
        (by unfold maxArgs at hlen; omega) hsg
        (by unfold nativeAssertNeed Newlib.RtErr.rtErrNeed Newlib.snprintfNeed; omega)
        hslg hal hregs.sp hcall
      iframe Hcode Hast Hv Hav Hms Hst Hw Hslot
      isplit
      · iintro %rv' %hok %hkeep Hregs Hst Hval Hw Hpc Hra
        ihave Hk := and_elim_l $$ Hk
        iapply Hk $$ Hpc Hra
        obtain ⟨v, m, hvm, htr⟩ := hok
        iexists _, .null
        isplitl []
        · ipureintro; exact .call _ _ _ _ _ _ _ _ _ _ _ hEf hlen hEa (.assertOk _ _ _ v m hvm htr)
        unfold evalPost
        iexists rv'
        iframe Hregs Hst Hval Hw
        ipureintro; exact hkeep
      · iintro %_ Hcore Hst Hslot
        have hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088 := by
          have hsF : s - 1088#64 = s + 18446744073709550528#64 := evalSP_eq s
          rw [← hsF]
          exact toNat_sub_frame (by
            have := hsg.le; simp only [BitVec.toNat_ofNat]; omega)
        ihave Hcore := hE.core (s + 18446744073709550528#64) nativeAssertNeed
          (by rw [hsf]; have := hsg.le; unfold nativeAssertNeed Newlib.RtErr.rtErrNeed Newlib.snprintfNeed; omega)
          (by rw [hsf]; have := hsg.lo; have := hsg.le; unfold Vsa.Sim.LayoutInstance.stackSL at *
              simp only at *; unfold nativeAssertNeed Newlib.RtErr.rtErrNeed Newlib.snprintfNeed; omega)
          (by rw [hsf]; have := hsg.hi; unfold Vsa.Sim.LayoutInstance.stackSL at *; simp only at *; omega)
          $$ Hcore
        ihave Hk := and_elim_r $$ Hk
        iapply Hk
        unfold abortAt
        iframe Hcore Hst Hslot
  | _ => exact absurd trivial hnc

end VsaIris.Interp
