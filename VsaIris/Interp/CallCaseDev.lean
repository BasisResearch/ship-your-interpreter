import VsaIris.Interp.CallNativeOut

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

end VsaIris.Interp
