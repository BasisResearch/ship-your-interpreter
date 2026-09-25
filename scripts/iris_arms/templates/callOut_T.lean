import VsaIris.Interp.CallNativeSeg

/-!
# `{ARM}`, total mode (family `callOut`, INTERP_DESIGN.md §6)

`caseT_{ARM}`: `eval_expr` on `.call f args` whose callee evaluates to the
native `{NF}` meets its total, derivation-indexed spec: the call prefix
(`callPrefixT`: the callee, the count test, E6's argument loop) and the
printing native's tail (`callNativeOut`: `jalr` into the native, the console
grown by its text). Premises: the children's specs, the native's spec (H2),
the natives' entries, `DispSupply` and the native's stack room (see
`PROOF_CLOSURE_PLAN.md`, lane E4). Template:
`scripts/iris_arms/templates/callOut_T.lean`.
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
    (hN : NativeEntries N) (hd : DispSupply (GF := GF) N)
    (Df : EvalECost st d env f st1 (.native .{NF}) nf) (hlen : args.length ≤ maxArgs)
    (Da : EvalArgsCost st1 d env args st2 vs na)
    (hf : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env f st1 (.native .{NF}) nf Df)
    (ha : evalArgsT_body (GF := GF) live N L Room inp st1 d env args st2 vs na)
    (hnp : ∀ sret args s vs st o,
      ⊢ {SPEC} (GF := GF) (vsaModel live) N (twpW (vsaModel live)) sret args s vs st o)
    (hroom : {NEED} + 1088 ≤ evalNeed (.call f args) d) :
    ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env (.call f args)
        ⟨st2.store, {OUTV}⟩ .null (nf + na + 0)
        (.call st d env f args st1 st2 _ (.native .{NF}) vs .null nf na 0 Df hlen Da
          (.{NF} st2 d vs)) := by
  have hspec : ⊢ NatOutSpecs (GF := GF) live N (twpW (vsaModel live)) {PC} {NEED}
      ({OUT}) :=
    natOutSpecs_of N _ (fun a b c vs st o => by rw [← {SPEC}_eq]; exact hnp a b c vs st o)
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
  iapply callNativeOut hlive (twpW (vsaModel live)) (nf := .{NF}) (entry := {PC})
    (out := {OUT}) (need := {NEED})
    (by show N.{NF} = _; rw [hN.{NF}]; rfl) (by decide) (by unfold maxArgs at hlen; omega) hsg hneed
    hroom hslg hal hd hregs.sp hcall
  isplitl []
  · iexact Hsp
  iframe Hcode Hast Hv Hav Hms Hst Hw Hslot
  unfold CallExitK
  iintro %rv' %hkeep Hregs Hst Hval Hw Hpc Hra
  iapply Hk $$ Hpc Hra
  unfold evalPost
  iexists rv'
  iframe Hregs Hst Hval Hw
  ipureintro; exact hkeep

end VsaIris.Interp
