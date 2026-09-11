import Vsa.Sim.EqAllocator
import Vsa.Sim.LayoutInstance

open LeanRV64DExecutable Vsa Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc
open Vsa.Machine Vsa.Logic

namespace Vsa.Sim
open RuntimeOwnership

/-- The fixed binary assigns distinct addresses to its three native functions. -/
theorem LayoutInstance.InterpRunPhysicalFacts.native_injective
    {c : Config} {stmts count : Nat} {inp : BitVec 64} {N : NativeAddrs} {A : Arena}
    {phiF phiC : Addr → Nat} {aLeft : Nat}
    (physical : LayoutInstance.InterpRunPhysicalFacts c stmts count inp N A phiF phiC aLeft) :
    ∀ f h, N.addr f = N.addr h → f = h := by
  obtain ⟨printAddr, printlnAddr, assertAddr⟩ := physical.native_addrs
  intro f h
  cases f <;> cases h <;> simp [NativeAddrs.addr, printAddr, printlnAddr, assertAddr]

/-- Equality and inequality return with allocator ownership at the fixed binary boundary. -/
theorem evalEqAllocator_fixed (op : EqNeOp)
    {initial : Config} {stmts count : Nat} {inp : BitVec 64}
    {initialF initialC : Addr → Nat} {initialArena : Arena} {aLeft : Nat}
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop}
    {st middle final : Vsa.While.St} {d env : Nat} {el er : Expr} {vl vr : Value}
    {costL costR maxRequest reserve : Nat} {sp ret dst node interp : BitVec 64} {m0 : Mem}
    (physical : LayoutInstance.InterpRunPhysicalFacts initial stmts count inp N initialArena
      initialF initialC aLeft)
    (L : AllocLedger A SL gpv headroom maxReq M) (request : maxRequest ≤ maxReq)
    (leftSem : EvalE st d env el middle vl) (rightSem : EvalE middle d env er final vr)
    (bounded : StoreClosuresBounded st.store)
    (leftIH : EvalAllocatorIH st d env el middle vl costL maxRequest)
    (rightIH : EvalAllocatorIH middle d env er final vr costR maxRequest) :
    Triple (EvalAllocatorEntry g N M phiF phiC alloc exts shared
      (costL + (costR + reserve)) st d env (.binary op.operator el er)
      sp ret dst interp node m0)
      (EvalAllocatorReturn g N M phiF phiC st.store.frames.size st.store.closures.size
        shared reserve final (.bool (op.result vl vr)) sp ret dst m0) :=
  evalEqAllocator op L request physical.native_injective leftSem rightSem bounded leftIH rightIH

#print axioms LayoutInstance.InterpRunPhysicalFacts.native_injective
#print axioms evalEqAllocator_fixed

end Vsa.Sim
