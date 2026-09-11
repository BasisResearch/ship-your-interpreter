import Vsa.Sim.AllocatorIH

open LeanRV64DExecutable Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While Vsa.Machine Vsa.Logic

namespace Vsa.Sim
open RuntimeOwnership

/-- Recursive evaluator ownership at one run's native function addresses. -/
structure EvalAllocatorAt (N : NativeAddrs) (st : Vsa.While.St) (d env : Nat) (e : Expr)
    (st' : Vsa.While.St) (v : Value) (cost maxRequest : Nat) : Prop where
  run : ∀ (g : (R : Register) → Option (RegisterType R))
    (A : Arena) (SL : StackLayout) (gpv : BitVec 64)
    (headroom maxReq : Nat) (M : MallocContract A SL gpv headroom maxReq)
    (_L : AllocLedger A SL gpv headroom maxReq M), maxRequest ≤ maxReq →
    ∀ (phiF phiC : Addr → Nat) (alloc : Allocations) (exts : List Extent)
    (shared : Nat → Prop) (reserve : Nat)
    (sp ret dst aEnv aExpr : BitVec 64) (m0 : Mem),
    Triple (EvalAllocatorEntry g N M phiF phiC alloc exts shared (cost + reserve)
      st d env e sp ret dst aEnv aExpr m0)
      (EvalAllocatorReturn g N M phiF phiC st.store.frames.size st.store.closures.size
        shared reserve st' v sp ret dst m0)

/-- Specialize an address-independent child supplier to the current run. -/
def EvalAllocatorIH.at
    {st st' : Vsa.While.St} {d env : Nat} {e : Expr} {v : Value}
    {cost maxRequest : Nat}
    (ih : EvalAllocatorIH st d env e st' v cost maxRequest) (N : NativeAddrs) :
    EvalAllocatorAt N st d env e st' v cost maxRequest :=
  ⟨fun g => ih.run g N⟩

#print axioms EvalAllocatorIH.at

end Vsa.Sim
