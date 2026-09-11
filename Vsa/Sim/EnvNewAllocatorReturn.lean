import Vsa.Sim.EnvNewRetained
import Vsa.Sim.RuntimeAllocatorState
import Vsa.Sim.RuntimeOwnershipEnvNew
import Vsa.Sim.RuntimeOwnershipFramePush

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- The actual env_new allocation consumes one credit and extends the owned store. -/
theorem EnvNewAllocationPost.runtime
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits : Nat} {st : Vsa.While.St} {env : Addr}
    {esp aEnv r p savedS0 : BitVec 64} {m : Mem} {allocated after : Config}
    (h : EnvNewAllocationPost N M phiF phiC exts st env esp aEnv r p savedS0 m credits allocated after)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (entry : RuntimeAllocatorState M N phiF phiC alloc exts shared (credits + 1) st.store m)
    (envValid : EnvValid st env) (gp : after.σ.regs.get? Register.x3 = some gpv) :
    RuntimeAllocatorState M N (pushFrameMap phiF st.store.frames.size p.toNat) phiC
      (alloc.insert (.frame st.store.frames.size) p.toNat 32) ((p.toNat, 32) :: exts)
      shared credits (st.store.allocFrame (some env)).1 after.σ.mem := by
  have off := entry.heap.ownedOff
    (fun k hlo hhi => Or.inr ⟨hlo, hhi⟩)
    (AllocLedger.privDisjoint_of_ainvAt entry.ainv after.σ gp)
    (fun k hk hnot => absurd (L.priv_arena k hk) hnot) L.arena_stack h.block.freshExtents
  have owned := entry.heap.store.transport h.agreement off.alloc off.shared
  have arrays := entry.arrays.transport entry.heap.store h.agreement off.alloc off.shared
  have address := pushFrameMap_fresh phiF st.store.frames.size p.toNat
  have freshOwned := frameOwned_of_envNewSuccess (shared := shared) (parent := some env)
    h.initialized address
    (Allocations.insert_same (alloc := alloc) (role := .frame st.store.frames.size))
  have reads := envNewInitializedReads_of_success h.initialized
  refine
    { heap :=
        { ledger := entry.heap.ledger.insert (by decide) h.block.arena h.block.fresh
          immutable := entry.heap.immutable.insert entry.heap.reserved h.block.arena h.block.fresh
          reserved := entry.heap.reserved.mono (fun e he => List.mem_cons_of_mem _ he)
          store := owned.pushFrame (pushFrameMap_extends phiF _ _) freshOwned }
      repr := h.fresh.store
      arrays := arrays.pushFrame (pushFrameMap_extends phiF _ _) address reads.names reads.values
      geometry := entry.geometry
      parents := entry.parents.allocFrame _ _ (by
        intro parent same
        have eq : parent = env := Option.some.inj same.symm
        subst parent
        exact envValid)
      ainv := h.invariant
      budget := h.budget, reserve := h.reserve }

/-- The original shared bytes survive the actual allocation and initialization. -/
theorem EnvNewAllocationPost.shared_agree
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {resultCredits entryCredits : Nat} {st : Vsa.While.St} {env : Addr}
    {esp aEnv r p savedS0 : BitVec 64} {m : Mem} {allocated after : Config}
    (h : EnvNewAllocationPost N M phiF phiC exts st env esp aEnv r p savedS0 m resultCredits allocated after)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (entry : RuntimeAllocatorState M N phiF phiC alloc exts shared entryCredits st.store m)
    (gp : after.σ.regs.get? Register.x3 = some gpv) : AgreeP shared m after.σ.mem := by
  have off := entry.heap.ownedOff
    (fun k hlo hhi => Or.inr ⟨hlo, hhi⟩)
    (AllocLedger.privDisjoint_of_ainvAt entry.ainv after.σ gp)
    (fun k hk hnot => absurd (L.priv_arena k hk) hnot) L.arena_stack h.block.freshExtents
  exact fun k hk => h.agreement k (off.shared k hk)

#print axioms EnvNewAllocationPost.runtime
#print axioms EnvNewAllocationPost.shared_agree

end Vsa.Sim
