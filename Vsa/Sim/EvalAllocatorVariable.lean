import Vsa.Sim.AllocatorIH
import Vsa.Sim.EnvGetReflected.EvalRuntimeEntry

open LeanRV64DExecutable Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While Vsa.Machine

namespace Vsa.Sim
open RuntimeOwnership EnvGetReflected

/-- Variable lookup preserves the entry extents and credits through its exact frame. -/
theorem EnvGetReflected.VarEvalResult.allocatorReturn
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop} {credits : Nat}
    {st : Vsa.While.St} {v : Value} {d env : Nat} {query : String}
    {sp ret dst aEnv aExpr : BitVec 64} {m0 : Mem} {before after : Config}
    (h : VarEvalResult g N A SL phiF phiC alloc shared st v sp ret dst m0 after)
    (entry : EvalAllocatorEntry g N M phiF phiC alloc exts shared credits
      st d env (.var query) sp ret dst aEnv aExpr m0 before)
    (L : AllocLedger A SL gpv headroom maxReq M) :
    EvalAllocatorReturn g N M phiF phiC st.store.frames.size st.store.closures.size
      shared credits st v sp ret dst m0 after := by
  have hsp := entry.entry.stackOK.2.1
  have hslot := entry.entry.ground.sret_inSL
  have hm : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) →
      before.σ.mem[k]? = after.σ.mem[k]? := by
    intro k hk
    rw [entry.entry.mem]
    exact (h.memory.agree k (by omega) (by omega)).symm
  have data : AllocatorResultAt M N shared credits st.store [(dst.toNat, v)] m0
      phiF phiC alloc exts shared after.σ.mem :=
    { allocator := entry.allocator.after_stack L hm
      includes := fun _ hk => hk
      values := fun a w haw => by
        have heq := List.mem_singleton.mp haw
        cases heq
        exact h.owned
      agreement := fun k hk => (h.shared_agree hsp hslot k hk).symm }
  exact
    { returned := h.returned.exit.withReturnRepr
        (data.coherent L (PhiExtends.refl _ _) (PhiExtends.refl _ _) (fun a w haw => by
          have heq := List.mem_singleton.mp haw
          cases heq
          exact h.value.repr))
      gp := (h.returned.exit.1.frame .x3 (by decide)).trans
        ((entry.entry.frame .x3 (by decide)).symm.trans entry.gp) }

/-- A successful variable lookup consumes no allocation credit. -/
theorem evalAllocatorIH_var {st : Vsa.While.St} {d env : Nat} {query : String} {v : Value}
    (hget : st.store.get? env query = some v) :
    EvalAllocatorIH st d env (.var query) st v 0 0 where
  run := by
    intro g N A SL gpv headroom maxReq M L _hrequest
      phiF phiC alloc exts shared reserve sp ret dst aEnv aExpr m0 before entry
    obtain ⟨after, steps, result⟩ := eval_var_owned (entry.runtime L) hget
    exact ⟨after, steps, by simpa only [Nat.zero_add] using result.allocatorReturn entry L⟩

#print axioms EnvGetReflected.VarEvalResult.allocatorReturn
#print axioms evalAllocatorIH_var

end Vsa.Sim
