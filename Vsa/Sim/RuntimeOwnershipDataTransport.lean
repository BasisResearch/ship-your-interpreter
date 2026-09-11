import Vsa.Sim.RuntimeOwnershipData
import Vsa.Sim.RuntimeOwnershipTransport

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

namespace Vsa.Sim.RuntimeOwnership

variable {N : NativeAddrs} {A : Arena} {SL : StackLayout}
  {phiF phiC : Vsa.While.Addr → Nat} {alloc : Allocations}
  {exts : List Extent} {shared : Nat → Prop} {s : Vsa.While.Store} {m m' : Mem}

/-- Runtime allocations avoid the whole stack at every recursive entry. -/
theorem StoreRuntimeData.allocated_off_stack
    (D : StoreRuntimeData N A SL phiF phiC alloc exts shared s m)
    {role : Role} {p n k : Nat} (hp : Allocated alloc role p n)
    (hk : ExtentByte (p, n) k) : ¬ (SL.lo ≤ k ∧ k < SL.hi) := by
  have hb := (D.ledger.arena.1 _ (D.ledger.live role p n hp)).2
  have hs := D.arenaStack
  change A.lo ≤ p ∧ p + n ≤ A.hi at hb
  change p ≤ k ∧ k < p + n at hk
  omega

/-- Shared runtime reads avoid the whole stack. -/
theorem StoreRuntimeData.shared_off_stack
    (D : StoreRuntimeData N A SL phiF phiC alloc exts shared s m)
    {k : Nat} (hk : shared k) : ¬ (SL.lo ≤ k ∧ k < SL.hi) := by
  have := D.geometry.stack k hk
  omega

/-- Stack writes preserve query-independent ownership and array readiness. -/
theorem StoreRuntimeData.after_stack
    (D : StoreRuntimeData N A SL phiF phiC alloc exts shared s m)
    (hm : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → m[k]? = m'[k]?) :
    StoreRuntimeData N A SL phiF phiC alloc exts shared s m' := by
  have ha := fun role p n (hp : Allocated alloc role p n) k
    (hk : ExtentByte (p, n) k) => D.allocated_off_stack hp hk
  have hs := fun k (hk : shared k) => D.shared_off_stack hk
  exact
    { D with
      owned := D.owned.transport hm ha hs
      repr := D.owned.repr_transport D.repr hm ha hs
      arrays := D.arrays.transport D.owned hm ha hs }

#print axioms StoreRuntimeData.allocated_off_stack
#print axioms StoreRuntimeData.shared_off_stack
#print axioms StoreRuntimeData.after_stack

end Vsa.Sim.RuntimeOwnership
