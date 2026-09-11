import Vsa.Sim.AllocatorAt

open LeanRV64DExecutable Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While Vsa.Machine Vsa.Logic

namespace Vsa.Sim
open RuntimeOwnership

/-- Statement ownership and return status at one run's native addresses. -/
structure ExecAllocatorAt (N : NativeAddrs) (st : Vsa.While.St) (d env : Nat) (s : Stmt)
    (st' : Vsa.While.St) (status : Status) (cost maxRequest : Nat) : Prop where
  run : ∀ (g : (R : Register) → Option (RegisterType R))
    (A : Arena) (SL : StackLayout) (gpv : BitVec 64)
    (headroom maxReq : Nat) (M : MallocContract A SL gpv headroom maxReq)
    (_L : AllocLedger A SL gpv headroom maxReq M), maxRequest ≤ maxReq →
    ∀ (phiF phiC : Addr → Nat) (alloc : Allocations) (exts : List Extent)
    (shared : Nat → Prop) (reserve : Nat)
    (sp ret aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem),
    Triple (ExecAllocatorEntry g N M phiF phiC alloc exts shared (cost + reserve)
      st d env s sp ret aInterp aStmt aEnv aRet m0)
      (ExecAllocatorReturn g N M phiF phiC st.store.frames.size st.store.closures.size
        shared reserve st' status sp ret aRet m0)

/-- Specialize a statement supplier to the current run's native addresses. -/
def ExecAllocatorIH.at
    {st st' : Vsa.While.St} {d env : Nat} {s : Stmt} {status : Status}
    {cost maxRequest : Nat}
    (ih : ExecAllocatorIH st d env s st' status cost maxRequest) (N : NativeAddrs) :
    ExecAllocatorAt N st d env s st' status cost maxRequest :=
  ⟨fun g => ih.run g N⟩

#print axioms ExecAllocatorIH.at

end Vsa.Sim
