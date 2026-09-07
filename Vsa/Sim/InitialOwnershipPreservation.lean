import Vsa.Sim.RuntimeOwnershipTransport
import Vsa.Sim.AstOwnershipPreservation
import Vsa.Sim.InterpRunPrefixPreservation

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Machine Vsa.While Vsa.Alloc

namespace Vsa.Sim

/-- The initial represented store and program at a reached prefix state.
All ownership fields retain the same initial ledger and shared byte domain. -/
structure ReadyRuntimeFacts (c : Config) (stmts count : Nat) (p : Program)
    (N : NativeAddrs) (A : Arena) (phiF phiC : Addr → Nat)
    (D : RuntimeOwnership.InitialOwnershipData) : Prop where
  heap : RuntimeOwnership.HeapOwned A D.exts c.σ.mem phiF phiC D.allocations D.shared
    RuntimeOwnership.InitialReadableByte
    (RuntimeOwnership.InitialWriteByte LayoutInstance.stackSL) initSt.store
  arrays : RuntimeOwnership.StoreArraysReady c.σ.mem phiF initSt.store
  program : ProgramReprWithin c.σ.mem D.shared stmts count p
  store : StoreRepr c.σ.mem N A phiF phiC initSt.store

/-- Restrict actual prefix preservation to the shared and allocated bytes.
The source program witness supplies the concrete AST transported to the endpoint. -/
theorem ReadyPrefixFacts.runtime_owned
    {c0 c1 : Config} {stmts count : Nat} {inp : BitVec 64} {p : Program}
    {N : NativeAddrs} {A : Arena} {phiF phiC : Addr → Nat} {aLeft : Nat}
    {D : RuntimeOwnership.InitialOwnershipData}
    (L : ReadyPrefixFacts inp c0 c1)
    (F : LayoutInstance.InterpRunReadyFacts c0 stmts count inp N A phiF phiC aLeft)
    (hp : ProgramRepr c0.σ.mem stmts count p)
    (O : RuntimeOwnership.InitialOwned c0.σ.mem A LayoutInstance.stackSL
      phiF phiC stmts count D) :
    ReadyRuntimeFacts c1 stmts count p N A phiF phiC D := by
  let P := fun k => ¬ RuntimeOwnership.InitialWriteByte LayoutInstance.stackSL k
  have hag : AgreeP P c0.σ.mem c1.σ.mem :=
    L.agree_protected (fun _ hk hw =>
      hk (F.prologue_mutable (interpRunPrefixWriteFootprint_broad hw)))
  have ha : ∀ role q n, RuntimeOwnership.Allocated D.allocations role q n →
      ∀ k, RuntimeOwnership.ExtentByte (q, n) k → P k :=
    fun role q n hq _ hk => O.extent_outsideWrites (O.heap.ledger.live role q n hq) hk
  have hs : ∀ k, D.shared k → P k := O.heap.immutable.outsideWrites
  exact ⟨O.heap.transport hag ha hs, O.arrays.transport O.heap.store hag ha hs,
    (O.program p hp).transport (fun k hk => hag k (hs k hk)),
    O.heap.store.repr_transport F.store hag ha hs⟩

/-- Actual first-return endpoint with its initial and preserved runtime ownership. -/
structure OwnedSetjmpFacts (inp : BitVec 64) (before after : Config) (spNew : BitVec 64)
    (stmts count : Nat) (p : Program) (N : NativeAddrs) (A : Arena)
    (phiF phiC : Addr → Nat) (D : RuntimeOwnership.InitialOwnershipData) : Prop extends
    ReadySetjmpFacts inp before before after spNew,
    ReadyRuntimeFacts after stmts count p N A phiF phiC D where
  initial : RuntimeOwnership.InitialOwned before.σ.mem A LayoutInstance.stackSL
    phiF phiC stmts count D

/-- The live boundary produces a real prefix execution retaining its exact ownership data. -/
theorem readySetjmp_owned
    {c : Config} {stmts count : Nat} {inp : BitVec 64} {p : Program}
    {N : NativeAddrs} {A : Arena} {phiF phiC : Addr → Nat} {aLeft : Nat}
    (F : LayoutInstance.InterpRunReadyFacts c stmts count inp N A phiF phiC aLeft)
    (hp : ProgramRepr c.σ.mem stmts count p) :
    ∃ after spNew D, OwnedSetjmpFacts inp c after spNew stmts count p N A phiF phiC D := by
  obtain ⟨D, O⟩ := F.ownership
  obtain ⟨after, spNew, J⟩ := readySetjmp_of_ready F
  exact ⟨after, spNew, D, J, J.preservation.runtime_owned F hp O, O⟩

#print axioms ReadyPrefixFacts.runtime_owned
#print axioms readySetjmp_owned

end Vsa.Sim
