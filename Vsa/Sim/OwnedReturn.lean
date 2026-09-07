import Vsa.Sim.CoherentReturn
import Vsa.Sim.RuntimeOwnershipUpdate

open LeanRV64DExecutable Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Machine

namespace Vsa.Sim

/-- Construct a coherent return from the reached allocation ledger.
Allocation and shared-byte exclusion supply store survival for later writes. -/
theorem ReturnRepr.of_heapOwned
    {N : NativeAddrs} {A : Arena} {exts : List Extent}
    {entryF entryC resultF resultC : Addr → Nat} {nf nc : Nat}
    {store : Store} {results : List (Nat × Value)} {m : Mem}
    {alloc : RuntimeOwnership.Allocations} {shared readable privateWrites writes : Nat → Prop}
    (howned : RuntimeOwnership.HeapOwned A exts m resultF resultC alloc
      shared readable privateWrites store)
    (hstore : StoreRepr m N A resultF resultC store)
    (hframes : PhiExtends entryF resultF nf) (hclosures : PhiExtends entryC resultC nc)
    (hvalues : ∀ a v, (a, v) ∈ results → ValueRepr m N resultC a v)
    (halloc : ∀ role p n, RuntimeOwnership.Allocated alloc role p n →
      ∀ k, RuntimeOwnership.ExtentByte (p, n) k → ¬ writes k)
    (hshared : ∀ k, shared k → ¬ writes k) :
    ReturnRepr N A entryF entryC resultF resultC nf nc store results
      (fun f c m => RuntimeOwnership.HeapOwned A exts m f c alloc
        shared readable privateWrites store) writes m where
  frames := hframes
  closures := hclosures
  values := hvalues
  owned := howned
  survives := fun _ hag => howned.store.repr_transport hstore hag halloc hshared

/-- The completed existing-name update supplies the shared return contract.
The helper returns no value. Its semantic store and ledger use the same maps. -/
theorem EnvDefineOwnedReturnPost.coherent
    {saved : (R : Register) → Option (RegisterType R)} {sp : BitVec 64}
    {m0 : Mem} {N : NativeAddrs} {A : Arena} {exts : List Extent}
    {phiF phiC : Addr → Nat} {alloc : RuntimeOwnership.Allocations}
    {shared readable privateWrites writes : Nat → Prop} {store : Store}
    {target : Addr} {name : String} {v : Value} {after : Config}
    (h : EnvDefineOwnedReturnPost saved sp m0 N A exts phiF phiC alloc
      shared readable privateWrites store target name v after)
    (halloc : ∀ role p n, RuntimeOwnership.Allocated alloc role p n →
      ∀ k, RuntimeOwnership.ExtentByte (p, n) k → ¬ writes k)
    (hshared : ∀ k, shared k → ¬ writes k) :
    ReturnRepr N A phiF phiC phiF phiC store.frames.size store.closures.size
      (store.define target name v) []
      (fun f c m => RuntimeOwnership.HeapOwned A exts m f c alloc
        shared readable privateWrites (store.define target name v)) writes after.σ.mem :=
  .of_heapOwned h.owned h.advance.toStoreRepr (PhiExtends.refl _ _) (PhiExtends.refl _ _)
    (fun _ _ h => False.elim (List.not_mem_nil h)) halloc hshared

#print axioms ReturnRepr.of_heapOwned
#print axioms EnvDefineOwnedReturnPost.coherent

end Vsa.Sim
