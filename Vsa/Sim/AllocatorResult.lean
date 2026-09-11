import Vsa.Sim.RuntimeAllocatorState
import Vsa.Sim.RuntimeResult

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While

namespace Vsa.Sim
open RuntimeOwnership

/-- The returned heap and allocator use the producer's same maps, extents, and memory. -/
structure AllocatorResultAt {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} (M : MallocContract A SL gpv headroom maxReq)
    (N : NativeAddrs) (entryShared : Nat → Prop) (credits : Nat)
    (store : Store) (results : List (Nat × Value)) (m0 : Mem)
    (phiF phiC : Addr → Nat) (alloc : Allocations) (exts : List Extent)
    (shared : Nat → Prop) (m : Mem) : Prop where
  allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared credits store m
  includes : ∀ k, entryShared k → shared k
  values : ∀ a v, (a, v) ∈ results → ValueOwned m shared a v
  agreement : AgreeP entryShared m0 m

/-- Allocation witnesses are selected together at the actual return memory. -/
structure AllocatorResult {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} (M : MallocContract A SL gpv headroom maxReq)
    (N : NativeAddrs) (entryShared : Nat → Prop) (credits : Nat)
    (store : Store) (results : List (Nat × Value)) (m0 : Mem)
    (phiF phiC : Addr → Nat) (m : Mem) : Prop where
  selected : ∃ alloc exts shared,
    AllocatorResultAt M N entryShared credits store results m0 phiF phiC alloc exts shared m

variable {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
  {M : MallocContract A SL gpv headroom maxReq} {N : NativeAddrs}
  {entryShared shared : Nat → Prop} {credits : Nat} {store : Store}
  {results results' : List (Nat × Value)} {m0 m1 m : Mem}
  {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}

theorem AllocatorResultAt.runtime
    (h : AllocatorResultAt M N entryShared credits store results m0
      phiF phiC alloc exts shared m) (L : AllocLedger A SL gpv headroom maxReq M) :
    RuntimeResultAt N A SL entryShared store results m0 phiF phiC alloc exts shared m :=
  ⟨h.allocator.runtime L, h.includes, h.values, h.agreement⟩

/-- Store survival and allocator ownership retain one selected representation pair. -/
theorem AllocatorResultAt.coherent
    (h : AllocatorResultAt M N entryShared credits store results m0
      phiF phiC alloc exts shared m) (L : AllocLedger A SL gpv headroom maxReq M)
    {entryF entryC : Addr → Nat} {nf nc : Nat}
    (hf : PhiExtends entryF phiF nf) (hc : PhiExtends entryC phiC nc)
    (hv : ∀ a v, (a, v) ∈ results → ValueRepr m N phiC a v) :
    ReturnRepr N A entryF entryC phiF phiC nf nc store results
      (AllocatorResult M N entryShared credits store results m0)
      (fun k => SL.lo ≤ k ∧ k < SL.hi) m where
  frames := hf
  closures := hc
  values := hv
  owned := ⟨alloc, exts, shared, h⟩
  survives := ((h.runtime L).coherent hf hc hv).survives

/-- Compose a child return after growth of the caller's shared domain. -/
theorem AllocatorResult.rebase_shared
    (h : AllocatorResult M N entryShared credits store results m0 phiF phiC m)
    {priorShared : Nat → Prop} (included : ∀ k, priorShared k → entryShared k)
    (subset : ∀ av, av ∈ results' → av ∈ results)
    (before : AgreeP priorShared m1 m0) :
    AllocatorResult M N priorShared credits store results' m1 phiF phiC m := by
  obtain ⟨alloc, exts, shared, data⟩ := h.selected
  exact ⟨alloc, exts, shared,
    { allocator := data.allocator
      includes := fun k hk => data.includes k (included k hk)
      values := fun a v hv => data.values a v (subset (a, v) hv)
      agreement := fun k hk => (before k hk).trans (data.agreement k (included k hk)) }⟩

/-- Discard unused result slots and compose the caller's preceding shared frame. -/
theorem AllocatorResult.rebase
    (h : AllocatorResult M N entryShared credits store results m0 phiF phiC m)
    (subset : ∀ av, av ∈ results' → av ∈ results)
    (before : AgreeP entryShared m1 m0) :
    AllocatorResult M N entryShared credits store results' m1 phiF phiC m :=
  h.rebase_shared (fun _ hk => hk) subset before

theorem AllocatorResult.shared_agree
    (h : AllocatorResult M N entryShared credits store results m0 phiF phiC m) :
    AgreeP entryShared m0 m := by
  obtain ⟨_, _, _, data⟩ := h.selected
  exact data.agreement

theorem AllocatorResult.runtime
    (h : AllocatorResult M N entryShared credits store results m0 phiF phiC m)
    (L : AllocLedger A SL gpv headroom maxReq M) :
    RuntimeResult N A SL entryShared store results m0 phiF phiC m := by
  obtain ⟨alloc, exts, shared, data⟩ := h.selected
  exact ⟨alloc, exts, shared, data.runtime L⟩

#print axioms AllocatorResultAt.runtime
#print axioms AllocatorResultAt.coherent
#print axioms AllocatorResult.rebase
#print axioms AllocatorResult.rebase_shared
#print axioms AllocatorResult.shared_agree
#print axioms AllocatorResult.runtime

end Vsa.Sim
