import Vsa.Sim.RuntimeIH
import Vsa.Sim.EnvGetReflected.EvalRuntimeEntry

open LeanRV64DExecutable Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While Vsa.Machine

namespace Vsa.Sim
open RuntimeOwnership EnvGetReflected

/-- Package the variable's actual return in the owned recursive data contract. -/
theorem EnvGetReflected.VarEvalResult.runtimeReturn
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {shared : Nat → Prop} {st : Vsa.While.St} {v : Value}
    {sp ret dst : BitVec 64} {m0 : Mem} {c : Config}
    (h : VarEvalResult g N A SL phiF phiC alloc shared st v sp ret dst m0 c)
    (hsp : sp.toNat ≤ SL.hi) (hslot : SL.lo ≤ dst.toNat ∧ dst.toNat + 24 ≤ SL.hi) :
    EvalRuntimeReturn g N A SL phiF phiC st.store.frames.size st.store.closures.size
      shared st v sp ret dst m0 c := by
  obtain ⟨exts, runtime⟩ := h.runtime
  have data : RuntimeResultAt N A SL shared st.store [(dst.toNat, v)] m0
      phiF phiC alloc exts shared c.σ.mem :=
    { runtime := runtime
      includes := fun _ hk => hk
      values := fun a w haw => by
        have heq := List.mem_singleton.mp haw
        cases heq
        exact h.owned
      agreement := fun k hk => (h.shared_agree hsp hslot k hk).symm }
  exact h.returned.exit.withReturnRepr
    (data.coherent (PhiExtends.refl _ _) (PhiExtends.refl _ _) (fun a w haw => by
      have heq := List.mem_singleton.mp haw
      cases heq
      exact h.value.repr))

/-- Variable lookup closes the owned evaluator data contract directly. -/
theorem evalRuntimeIH_var {st : Vsa.While.St} {d env : Nat} {query : String} {v : Value}
    (hget : st.store.get? env query = some v) : EvalRuntimeIH st d env (.var query) st v where
  run := by
    intro g N A SL phiF phiC alloc exts shared sp ret dst aEnv aExpr m0 before entry
    obtain ⟨after, steps, result⟩ := eval_var_owned entry hget
    exact ⟨after, steps,
      result.runtimeReturn entry.entry.stackOK.2.1 entry.entry.ground.sret_inSL⟩

#print axioms EnvGetReflected.VarEvalResult.runtimeReturn
#print axioms evalRuntimeIH_var

end Vsa.Sim
