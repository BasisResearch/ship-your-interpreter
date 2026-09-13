import Vsa.Sim.NativeNameAudit.ControlOwnership

namespace Vsa.Sim.NativeNameAudit.Control
open Vsa.Sim.OutputAliasLoaded Vsa.Sim.LayoutInstance

/-- A concrete dense snapshot with a consistent dlmalloc heap inhabits the live
ownership boundary. -/
theorem readyFacts : InterpRunReadyFacts heapConfig 0x82000000 2 fixedInp
    Nfixed arena phif phic 0 where
  toInterpRunPhysicalFacts := heapPhysicalFacts
  ownership := ⟨ownershipData, by
    show RuntimeOwnership.InitialOwned (physicalConfig heapMem).σ.mem arena stackSL phif phic
      0x82000000 2 ownershipData
    rw [physicalConfig_mem]
    exact initialOwned⟩

theorem loaded : Vsa.Refine.Loaded interpRunLayout nativeNameProgram heapConfig := by
  refine ⟨0x82000000, 2, ?_, fixedInp, Nfixed, arena, phif, phic, 0, readyFacts⟩
  show Vsa.MemRepr.ProgramRepr (physicalConfig heapMem).σ.mem 0x82000000 2 nativeNameProgram
  rw [physicalConfig_mem]
  exact heapAstReads.programWithin.erase

#print axioms readyFacts
#print axioms loaded

end Vsa.Sim.NativeNameAudit.Control
