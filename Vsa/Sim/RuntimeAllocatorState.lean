import Vsa.Sim.RuntimeOwnershipDataTransport
import Vsa.Sim.AllocRuns
import Vsa.Sim.AllocCapacity
import Vsa.Sim.AllocReserveTransport

open LeanRV64DExecutable Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While

namespace Vsa.Sim
open RuntimeOwnership

/-- The runtime and allocator invariant share one live extent list and memory. -/
structure RuntimeAllocatorState {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} (M : MallocContract A SL gpv headroom maxReq)
    (N : NativeAddrs) (phiF phiC : Addr → Nat) (alloc : Allocations)
    (exts : List Extent) (shared : Nat → Prop) (credits : Nat) (s : Store) (m : Mem) : Prop where
  heap : HeapOwned A exts m phiF phiC alloc shared InitialReadableByte (InitialWriteByte SL) s
  repr : StoreRepr m N A phiF phiC s
  arrays : StoreArraysReady m phiF s
  geometry : SharedReadGeom shared SL
  parents : StoreParents s
  ainv : AInvAt M gpv m exts
  budget : ResourceBudget A maxReq exts credits
  reserve : AllocationReserve A m exts maxReq credits

variable {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
  {M : MallocContract A SL gpv headroom maxReq} {N : NativeAddrs}
  {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
  {shared : Nat → Prop} {credits : Nat} {s : Store} {m m' : Mem}

/-- Project lookup and recursive data using the run-global allocator geometry. -/
theorem RuntimeAllocatorState.runtime
    (h : RuntimeAllocatorState M N phiF phiC alloc exts shared credits s m)
    (L : AllocLedger A SL gpv headroom maxReq M) :
    StoreRuntimeData N A SL phiF phiC alloc exts shared s m :=
  { owned := h.heap.store, repr := h.repr, arrays := h.arrays, ledger := h.heap.ledger
    geometry := h.geometry, arenaLo := L.arena_ram.1, arenaHi := L.arena_ram.2
    arenaHtif := by have := L.arena_htif; omega
    arenaStack := L.arena_stack, parents := h.parents }

/-- Stack writes preserve reservations, allocator-private state, and allocation credit. -/
theorem RuntimeAllocatorState.after_stack
    (h : RuntimeAllocatorState M N phiF phiC alloc exts shared credits s m)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (hm : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → m[k]? = m'[k]?) :
    RuntimeAllocatorState M N phiF phiC alloc exts shared credits s m' := by
  have data := h.runtime L
  have reached := data.after_stack hm
  exact
    { heap := h.heap.transport hm
        (fun _ _ _ hp _ hk => data.allocated_off_stack hp hk)
        (fun _ hk => data.shared_off_stack hk)
      repr := reached.repr
      arrays := reached.arrays
      geometry := h.geometry
      parents := h.parents
      ainv := L.ainvAt_transport_offStack (Nat.le_refl SL.hi) h.ainv hm
      budget := h.budget
      reserve := h.reserve.after_stack hm (by
        intro k hk
        rcases L.globals_stack with above | below <;> omega) L.arena_stack }

/-- A weaker remaining allocation budget retains the same runtime state. -/
theorem RuntimeAllocatorState.credit_mono
    (h : RuntimeAllocatorState M N phiF phiC alloc exts shared credits s m)
    {remaining : Nat} (hle : remaining ≤ credits) :
    RuntimeAllocatorState M N phiF phiC alloc exts shared remaining s m :=
  { h with budget := h.budget.mono hle, reserve := h.reserve.mono hle }

#print axioms RuntimeAllocatorState.runtime
#print axioms RuntimeAllocatorState.after_stack
#print axioms RuntimeAllocatorState.credit_mono

end Vsa.Sim
