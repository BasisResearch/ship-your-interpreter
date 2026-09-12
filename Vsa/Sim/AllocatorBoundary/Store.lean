import Vsa.Sim.NativeNameAudit.ControlOwnership

namespace Vsa.Sim.AllocatorBoundary
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc RuntimeOwnership
open Vsa.Sim.OutputAliasLoaded Vsa.Sim.LayoutInstance Vsa.Sim.NativeNameAudit
open Control (alloc shared)

/-- The fixed native store's ownership follows from its actual read view. -/
theorem frameOwned {m : Mem} (view : StoreView m) : FrameOwned m phif alloc shared 0 globalFrame where
  record := by simp [Allocated, alloc, Allocations.insert, phif]
  arrays := by
    refine ⟨⟨8, 0x81000040, 0x81000080⟩,
      view.capacity, view.names, view.values, by decide, ?_, ?_, ?_⟩
    · right
      exact ⟨by decide, by simp [Allocated, alloc, Allocations.insert]⟩
    · right
      exact ⟨by decide, by simp [Allocated, alloc, Allocations.insert]⟩
    · intro i hi
      change i < 3 at hi
      have hc : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases hc with rfl | rfl | rfl
      · exact ⟨0x81000200, view.names0,
          by simp [Allocated, alloc, Allocations.insert, globalFrame]; decide, ⟨view.printName, Control.printShared.bytes⟩⟩
      · exact ⟨0x81000210, view.names1,
          by simp [Allocated, alloc, Allocations.insert, globalFrame]; decide, ⟨view.printlnName, Control.printlnShared.bytes⟩⟩
      · exact ⟨0x81000220, view.names2,
          by simp [Allocated, alloc, Allocations.insert, globalFrame]; decide, ⟨view.assertName, Control.assertShared.bytes⟩⟩
  values := by
    intro pv hp i hi
    have he := Option.some.inj (hp.symm.trans view.values)
    subst pv
    change i < 3 at hi
    have hc : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hc with rfl | rfl | rfl
    · exact ⟨0x81000200, view.name0, ⟨view.printName, Control.printShared.bytes⟩⟩
    · exact ⟨0x81000210, view.name1, ⟨view.printlnName, Control.printlnShared.bytes⟩⟩
    · exact ⟨0x81000220, view.name2, ⟨view.assertName, Control.assertShared.bytes⟩⟩

theorem storeOwned {m : Mem} (view : StoreView m) : StoreOwned m phif phic alloc shared initSt.store where
  frames := by
    intro fa hf
    change fa < 1 at hf
    have he : fa = 0 := by omega
    subst fa
    exact frameOwned view
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

#print axioms frameOwned
#print axioms storeOwned
end Vsa.Sim.AllocatorBoundary
