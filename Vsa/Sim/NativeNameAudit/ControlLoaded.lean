import Vsa.Sim.NativeNameAudit.ControlBootHeap

namespace Vsa.Sim.NativeNameAudit.Control
open Vsa.Sim.OutputAliasLoaded Vsa.Sim.LayoutInstance

/-- A concrete dense snapshot with a consistent dlmalloc heap inhabits the live
ownership boundary, including the boundary heap facts (`bootHeap`). -/
theorem readyFacts : InterpRunReadyFacts heapConfig 0x82000000 2 fixedInp
    Nfixed heapArena phif phic 0 where
  toInterpRunPhysicalFacts := heapPhysicalFactsAt
  boot := ⟨ownershipData, heapTop, heapBrk, heapChunks, fun _ => [], bootFrame, by
    show BootHeap (physicalConfigS0 heapMem).σ.mem heapArena phif phic 0x82000000 2 ownershipData
      heapTop heapBrk heapChunks (fun _ => []) bootFrame
    rw [physicalConfigS0_mem]
    exact bootHeap⟩
  stack_admissible := by
    intro p hp
    change Vsa.MemRepr.ProgramRepr (physicalConfigS0 heapMem).σ.mem 0x82000000 2 p at hp
    rw [physicalConfigS0_mem] at hp
    rw [heapAstReads.program_unique hp]
    exact ProgramStackFits.of_check (by decide)
  gprs := physicalS0_gprs heapMem
  s0_impure := physicalRegsS0_x8

theorem loaded : Vsa.Refine.Loaded interpRunLayout nativeNameProgram heapConfig := by
  refine ⟨0x82000000, 2, ?_, fixedInp, Nfixed, heapArena, phif, phic, 0, readyFacts⟩
  show Vsa.MemRepr.ProgramRepr (physicalConfigS0 heapMem).σ.mem 0x82000000 2 nativeNameProgram
  rw [physicalConfigS0_mem]
  exact heapAstReads.programWithin.erase

#print axioms readyFacts
#print axioms loaded

end Vsa.Sim.NativeNameAudit.Control
