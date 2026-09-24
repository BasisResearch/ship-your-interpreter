import VsaIris.Interp.ExecIf

/-!
# `{ARM}`, total mode (family `execIfTrue`, lane E5)

`caseT_{ARM}`: `exec_stmt` on `.ifStmt c t eo` with a truthy condition
(`ExecSCost.ifTrue`) meets its dispatch-point spec: the prefix
(`ifPrefixT`: dispatch, the condition into `sp+56`, `value_truthy`) then the
then branch re-dispatched in the frame (`ifRouteThenT`).
Template: `scripts/iris_arms/templates/execIfTrue_T.lean`.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim
open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr

theorem caseT_{ARM} {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
    {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {st : St} {d env : Nat} {c : Expr} {t : Stmt} {eo : Option Stmt} {st' st'' : St} {v : Value}
    {status : Status} {nc nt : Nat}
    (Dc : EvalECost st d env c st' v nc) (hv : v.truthy = true)
    (Dt : ExecSCost st' d env t st'' status nt)
    (hc : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env c st' v nc Dc)
    (ht : ⊢ execDispT_body (GF := GF) (vsaModel live) N L Room inp st' d env t st'' status nt Dt)
    (hvt : ⊢ ∀ p w, valueTruthySpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) p w) :
    ⊢ execDispT_body (GF := GF) (vsaModel live) N L Room inp st d env (.ifStmt c t eo) st'' status
        (nc + nt) (.ifTrue st d env c t eo st' st'' v status nc nt Dc hv Dt) := by
  unfold execDispT_body
  iintro !> %Φ %k %aS %aE %aRet %s %R %Mt %ret %v8 %v9 %v18 %v19 Hpre HK
  unfold execDispPre
  icases Hpre with ⟨Hms, %hf, #Hcode, #Hast, #Hfb, Hst, Hslot, Hw⟩
  rw [show k + (nc + nt) = k + nt + nc by omega]
  iapply ifPrefixT hlive (k := k + nt) Dc hc hvt hf
    (fun P m R3 M3 hr => ifRouteThenT hlive Dt ht hf hr hv)
  iframe HK Hms Hcode Hast Hfb Hst Hslot Hw

end VsaIris.Interp
