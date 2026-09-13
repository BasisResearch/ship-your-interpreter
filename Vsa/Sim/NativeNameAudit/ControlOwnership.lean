import Vsa.Sim.NativeNameAudit.ControlHeapAllocator

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim.NativeNameAudit.Control
open RuntimeOwnership Vsa.Sim.OutputAliasLoaded Vsa.Sim.LayoutInstance

theorem frameOwned : FrameOwned heapMem phif alloc shared 0 globalFrame where
  record := by simp [Allocated, alloc, Allocations.insert, phif]
  arrays := by
    refine ⟨⟨8, 0x81000040, 0x81000100⟩,
      heapStoreFacts.capacity, heapStoreFacts.names, heapStoreFacts.values, by decide,
      ?_, ?_, ?_⟩
    · right
      exact ⟨by decide, by simp [Allocated, alloc, Allocations.insert]⟩
    · right
      exact ⟨by decide, by simp [Allocated, alloc, Allocations.insert]⟩
    · intro i hi
      change i < 3 at hi
      have hc : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases hc with rfl | rfl | rfl
      · exact ⟨0x81000200, heapStoreFacts.names0,
          by simp [Allocated, alloc, Allocations.insert, globalFrame]; decide, printShared⟩
      · exact ⟨0x81000210, heapStoreFacts.names1,
          by simp [Allocated, alloc, Allocations.insert, globalFrame]; decide, printlnShared⟩
      · exact ⟨0x81000220, heapStoreFacts.names2,
          by simp [Allocated, alloc, Allocations.insert, globalFrame]; decide, assertShared⟩
  values := by
    intro pv hp i hi
    have he := Option.some.inj (hp.symm.trans heapStoreFacts.values)
    subst pv
    change i < 3 at hi
    have hc : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hc with rfl | rfl | rfl
    · exact ⟨0x81000200, heapStoreFacts.name0, printShared⟩
    · exact ⟨0x81000210, heapStoreFacts.name1, printlnShared⟩
    · exact ⟨0x81000220, heapStoreFacts.name2, assertShared⟩

theorem storeOwned : StoreOwned heapMem phif phic alloc shared initSt.store where
  frames := by
    intro fa hf
    change fa < 1 at hf
    have he : fa = 0 := by omega
    subst fa
    exact frameOwned
  closures := by
    intro ca hc
    change ca < 0 at hc
    omega
  valueClosures := by
    constructor
    intro fa hf i hi
    change fa < 1 at hf
    have he : fa = 0 := by omega
    subst fa
    change i < 3 at hi
    have hc : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hc with rfl | rfl | rfl <;> trivial
  capturedEnvs := by
    intro ca hc
    change ca < 0 at hc
    omega
  closureAsts := by
    intro ca hc
    change ca < 0 at hc
    omega

def ownershipData : InitialOwnershipData := ⟨exts, alloc, shared⟩

theorem initialOwned : InitialOwned heapMem arena stackSL phif phic 0x82000000 2
    ownershipData where
  heapLower := by decide
  heapUpper := by decide
  heap := ⟨ledger, immutable, reserved, storeOwned⟩
  arrays := heapArraysReady
  program := fun p hp => (heap_program_owned p hp).mono
    (fun _ hk => Or.inr (Or.inr (Or.inr hk)))
  allocator := heapAllocator

#print axioms frameOwned
#print axioms storeOwned
#print axioms initialOwned

end Vsa.Sim.NativeNameAudit.Control
