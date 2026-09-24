import VsaIris.Interp.CallNativeSeg
import VsaIris.Interp.CallPrefixP

/-!
# `{ARM}`, total mode (family `callAssert`, INTERP_DESIGN.md §6)

`caseT_{ARM}`: `eval_expr` on `.call f args` whose callee evaluates to the
native `assert`, with one or two arguments the first truthy (`Call.assertOk`),
meets its total spec: the call prefix (`callPrefixT`) and the `assert` tail
(`callNativeAssert`), whose abort branch the derivation refutes
(`nativeAssertSpec` aborts with `¬ AssertOk vs`). Template:
`scripts/iris_arms/templates/callAssert_T.lean`.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim Vsa.While
open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.RuntimeRepr

theorem caseT_{ARM} {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
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

end VsaIris.Interp
