import Vsa.Sim.NativeNameAudit.ControlLoaded
import Vsa.Sim.AllocCapacity
import Vsa.Sim.RuntimeAllocatorState

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc Vsa.Machine

namespace Vsa.Sim.InitialResourceGap
open RuntimeOwnership LayoutInstance OutputAliasLoaded
open NativeNameAudit

/-- Additional disjoint payload extents allowed by the data-only boundary. -/
def extra : List Extent := (List.range 64).map fun i => (0x81000300 + 49 * i, 49)

def extents : List Extent := extra ++ Control.exts

def data : InitialOwnershipData := ⟨extents, Control.alloc, Control.shared⟩

theorem included (e : Extent) (he : e ∈ Control.exts) : e ∈ extents :=
  List.mem_append_right extra he

theorem extra_bounds (e : Extent) (he : e ∈ extra) :
    0x81000300 ≤ e.1 ∧ e.1 + e.2 ≤ 0x81001000 ∧ 0 < e.2 := by
  obtain ⟨i, hi, eq⟩ := List.mem_map.mp he
  have bound := List.mem_range.mp hi
  cases eq
  omega

theorem heapArena : HeapArena Control.heapArena extents := by
  refine ⟨?_, List.pairwise_append.mpr ⟨?_, Control.ledger.arena.2, ?_⟩⟩
  · intro e he
    rcases List.mem_append.mp he with added | old
    · have h := extra_bounds e added
      exact ⟨h.2.2, by
        change 0x8001c170 ≤ e.1 ∧ e.1 + e.2 ≤ 0x87800000
        omega⟩
    · exact Control.ledger.arena.1 e old
  · unfold ExtDisjoint
    decide
  · intro a ha b hb
    have lo := extra_bounds a ha
    have old : ∀ e ∈ Control.exts, e.1 + e.2 ≤ 0x81000300 ∨ 0x81001000 ≤ e.1 := by decide
    rcases old b hb with hb' | hb'
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)

/-- The heap control's chunks cover the extra extents; arrays stay exact. -/
theorem heap : DlHeap.HeapAt Control.heapMem extents (ReallocExtent Control.alloc)
    Control.heapTop Control.heapBrk Control.heapChunks (fun _ => []) :=
  { Control.heapAt with
    live := by
      intro e he
      rcases List.mem_append.mp he with added | old
      · have h := extra_bounds e added
        exact ⟨⟨0x81000240, 0xfffdb0, true⟩, by simp [Control.heapChunks], rfl,
          by dsimp only; omega, by dsimp only; omega⟩
      · exact Control.heapAt.live e old
    exact := by
      intro e he hr
      rcases List.mem_append.mp he with added | old
      · have h := extra_bounds e added
        obtain ⟨fa, hr⟩ := hr
        rcases Control.realloc_extent hr with rfl | rfl <;> simp at h
      · exact Control.heapAt.exact e old hr }

/-- The oversized ledger is admitted at the pinned heap arena. -/
theorem initialOwned : InitialOwned Control.heapMem Control.heapArena stackSL phif phic
    0x82000000 2 data := by
  have old := Control.initialOwned
  exact
    { heapLower := old.heapLower
      heapUpper := old.heapUpper
      heap :=
        { ledger :=
            { arena := heapArena
              live := fun role p n hp => included _ (Control.ledger.live role p n hp)
              separated := Control.ledger.separated }
          immutable := old.heap.immutable
          reserved := old.heap.reserved.mono included
          store := old.heap.store }
      arrays := old.arrays
      program := old.program
      allocator := ⟨Control.heapTop, Control.heapBrk, Control.heapChunks, fun _ => [],
        heap, Control.heapCapacity⟩
      arenaHeap := old.arenaHeap }

theorem ready : InterpRunReadyFacts Control.heapConfig 0x82000000 2 fixedInp
    Nfixed Control.heapArena phif phic 0 :=
  { Control.readyFacts with ownership := ⟨data, by
      show InitialOwned (physicalConfig Control.heapMem).σ.mem Control.heapArena stackSL phif phic
        0x82000000 2 data
      rw [physicalConfig_mem]
      exact initialOwned⟩ }

/-- Payload disjointness does not imply room for the allocator's physical chunks. -/
theorem no_zero_credit : ¬ ResourceBudget arena 32 data.exts 0 := by
  unfold ResourceBudget
  decide

/-- The same snapshot also has the original, affordable ownership witness. -/
theorem original_zero_credit : ResourceBudget arena 32 Control.ownershipData.exts 0 := by
  unfold ResourceBudget
  decide

/-- This ledger exceeds capacity independently of future request parameters. -/
theorem no_credit (maxReq credits : Nat) :
    ¬ ResourceBudget arena maxReq data.exts credits := by
  have total : physTotal data.exts = 4800 := by decide
  intro h
  change physTotal data.exts + credits * physSize maxReq ≤ 4096 at h
  rw [total] at h
  omega

/-- No allocator state at this arena can preserve the admitted extent list. -/
theorem no_allocator_state {gpv : BitVec 64} {headroom maxReq credits : Nat}
    {M : MallocContract arena stackSL gpv headroom maxReq}
    {N : NativeAddrs} {phiF phiC : Addr → Nat} {alloc : Allocations}
    {shared : Nat → Prop} {store : Store} {m : Mem} :
    ¬ RuntimeAllocatorState M N phiF phiC alloc data.exts shared credits store m :=
  fun h => no_credit maxReq credits h.budget

/-- The pinned boundary excludes the 4 KiB arena, whatever the ledger. -/
theorem small_arena_excluded {m : Mem} {stmts count : Nat} {D : InitialOwnershipData} :
    ¬ InitialOwned m arena stackSL phif phic stmts count D :=
  fun h => absurd h.arenaHeap.1 (by decide)

/-- At the pinned arena the same oversized ledger leaves room for a million
maximal requests. -/
theorem heap_credit : ResourceBudget Control.heapArena 32 data.exts 1000000 := by
  unfold ResourceBudget
  decide

#print axioms included
#print axioms extra_bounds
#print axioms heapArena
#print axioms heap
#print axioms initialOwned
#print axioms ready
#print axioms no_zero_credit
#print axioms original_zero_credit
#print axioms no_credit
#print axioms no_allocator_state
#print axioms small_arena_excluded
#print axioms heap_credit

end Vsa.Sim.InitialResourceGap
