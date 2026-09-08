import Vsa.Sim.rows.EnvDefineCall
import Vsa.Sim.rows.EvalChildArmVarInit
import Vsa.Sim.rows.ExecVarInitRow
import Vsa.Sim.EvalReturn

/-!
# `Field_hSVarInitClosed` — the initialised declaration on the layer

`var x = e;` dispatches the child (`stmtVarInitArm`, generic) and resumes
through the declaration tail (`envDefineTail_run`) from the child's COHERENT
return (`EvalReturn`, the `mEvalE` motive): the child's selected map pair
represents both its value and the store it survives with, so a closure the
initializer allocated (`var f = fn() {...};`) is bound at the pair its store
uses.  Two named premises remain, each shared with other fields:

* `EnvDefineContract` — the `env_define` callee (also `hSVarNull`,
  `hAssign`, `hCallClosure`);
* `VarInitPayloadOff` — a string payload lies outside the call buffer (the
  class of the value return's payload premise).
-/

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

/-- The initializer's string payload (if any) lies outside the call buffer
`[esp+16, esp+40)`.  Supplied by the ownership layer's payload location. -/
def VarInitPayloadOff (st st' : Vsa.While.St) (v : Value) : Prop :=
  ∀ (gC : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp : BitVec 64) (mC : Mem) (cfg : Config),
    EvalExitD gC N A SL φf φc st.store.frames.size st.store.closures.size st' v
      (sp - 176#64) stmtVarInitArm.retPC (stmtVarInitArm.sret (sp - 176#64)) mC cfg →
    PayloadOffWindow cfg.σ.mem (stmtVarInitArm.sret (sp - 176#64)).toNat
      ((sp - 176#64).toNat + 16) v

/-- The resume of the initialised declaration from the child's coherent return:
the selected pair `(φf', φc')` of `EvalReturn.repr` represents the value at the
sret and the store `st'.store` under every stack-region change. -/
theorem varInit_resume
    (hED : EnvDefineContract)
    {g gC : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st st' : Vsa.While.St} {d : Nat} {env : Addr} {x : String} {e : Expr} {v : Value}
    {sp r aInterp aStmt aEnv aRet aC : BitVec 64} {m0 mC : Mem}
    (hpay : VarInitPayloadOff st st' v)
    (hCarrier : stmtVarInitArm.Carrier (.varDecl x (some e)) e g N A SL φf φc st d env
      sp r aInterp aStmt aEnv aRet m0 gC aC mC)
    (hE : EvalE st d env e st' v) :
    Triple
      (EvalReturn gC N A SL φf φc st.store.frames.size st.store.closures.size st' v
        (sp - 176#64) stmtVarInitArm.retPC (stmtVarInitArm.sret (sp - 176#64)) mC
        (fun _ _ _ => True))
      (ExecExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        ⟨st'.store.define env x v, st'.out⟩ .normal sp r aRet m0) := by
  intro cfgX hRet
  have hExit := hRet.exit
  obtain ⟨_, _, _, _, _, hKit⟩ :=
    stmtVarInitArm.exitKit_at_exit stmtVarInitArm_cert hCarrier cfgX hExit
  -- the child's ONE selected pair: value and store survival at `(φf', φc')`.
  obtain ⟨φf', φc', hR⟩ := hRet.repr.selected
  have hpf : PhiExtends φf φf' st.store.frames.size := hR.frames
  have hpc : PhiExtends φc φc' st.store.closures.size := hR.closures
  have hSurv : ∀ m' : Mem, (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → cfgX.σ.mem[k]? = m'[k]?) →
      StoreRepr m' N A φf' φc' st'.store :=
    fun m' hag => hR.survives m' (fun k hk => hag k hk)
  have hv : ValueRepr cfgX.σ.mem N φc' (stmtVarInitArm.sret (sp - 176#64)).toNat v :=
    hR.values _ _ (List.mem_singleton_self _)
  have F := stmtVarInitArm.frameFacts_at_exit_of_store stmtVarInitArm_cert
    (stmtVarInitArm_sem x e) hCarrier hE cfgX hExit hpf hSurv hKit
  obtain ⟨h176, hesp, hsret, hroom, hSLhi, hal⟩ := hCarrier.geom stmtVarInitArm_cert
  have hoff : stmtVarInitArm.sretOff = 104 := rfl
  rw [hoff] at hsret
  have hsrc : (stmtVarInitArm.sret (sp - 176#64)).toNat = (sp - 176#64).toNat + 104 := by
    rw [hsret, hesp]
  have hRR := stmtVarInitArm.routeReady_of_exit stmtVarInitArm_cert hCarrier cfgX hExit
  rw [show stmtVarInitArm.retPC = 0x800040f0#64 from by decide] at hRR
  have hframe0 : ∀ a, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      (aRet.toNat ≤ a ∧ a < aRet.toNat + 24) ∨ cfgX.σ.mem[a]? = m0[a]? := by
    intro a hstk hA
    rcases hExit.1.memFrame a (by rw [hesp]; intro hs; exact hstk ⟨hs.1, by omega⟩) hA
      with hs | heq
    · exfalso
      rw [hsret] at hs
      exact hstk ⟨by omega, by omega⟩
    · exact Or.inr (heq.trans (hCarrier.mem_frame a hstk))
  exact envDefineTail_run hED F
    (fun _ h => by cases h with | varInit _ hp hc _ _ _ => exact ⟨_, hp, hc⟩)
    hRR hpf hpc (hsrc ▸ hv) (hsrc ▸ hpay gC N A SL φf φc sp mC cfgX hExit)
    (hCarrier.mem_extends.trans hExit.2.1) hframe0 hKit.out

/-- Supplier for the initialised-declaration residual, from the two named
premises.  The coherence of the child's value with its store is no premise: it
is the recursor motive's `EvalReturn.repr`. -/
theorem ScaffoldRows.field_hSVarInit (hED : EnvDefineContract)
    (hpay : ∀ st st' v, VarInitPayloadOff st st' v) :
    ∀ st st' d env x e v, Rows.VarInitResid st st' d env x e v :=
  fun st st' d env x e v =>
    Rows.varInitResid_of_resume
      (fun g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 gC aC mC hCarrier hE =>
        varInit_resume hED (hpay st st' v) hCarrier hE)

#print axioms varInit_resume
#print axioms ScaffoldRows.field_hSVarInit

end Vsa.Sim
