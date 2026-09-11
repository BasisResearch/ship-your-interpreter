import Vsa.Sim.RuntimeAllocatorState
import Vsa.Sim.AllocLedger

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- Retain the runtime store and debit one credit for the actual fresh allocation. -/
theorem MallocReturnAt.runtime
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {g : (R : Register) → Option (RegisterType R)} {exts : List Extent} {n : Nat}
    {sp r : BitVec 64} {m : Mem} {out : Array String} {N : NativeAddrs}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {shared : Nat → Prop}
    {store : Store} {p credits : Nat} {after : Config}
    (h : MallocReturnAt A SL gpv headroom maxReq M g exts n sp r m out N phiF phiC alloc
      shared InitialReadableByte (InitialWriteByte SL) store credits p after)
    (entry : RuntimeAllocatorState M N phiF phiC alloc exts shared (credits + 1) store m)
    (request : n ≤ maxReq) :
    RuntimeAllocatorState M N phiF phiC alloc ((p, n) :: exts) shared credits store after.σ.mem := by
  have off := h.ownedOff.mono (fresh' := []) (by simp)
  exact
    { heap := h.owned, repr := h.store
      arrays := entry.arrays.transport entry.heap.store h.agree off.alloc off.shared
      geometry := entry.geometry, parents := entry.parents, ainv := h.ainv
      budget := h.budget, reserve := h.reserve }

#print axioms MallocReturnAt.runtime

end Vsa.Sim
