import Vsa.Sim.NativeNameAudit.ControlBootHeap
import Vsa.Densify.Transport

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

/-- The control memory is dense on RAM: the snapshot holds every RAM byte and
the heap log only inserts. -/
theorem heapConfig_dense : ∀ a, Vsa.Densify.ramBase ≤ a → a < Vsa.Densify.ramBase + Vsa.Densify.ramSize →
    (heapConfig.σ.mem[a]?).isSome := by
  intro a hlo hhi
  unfold Vsa.Densify.ramBase at hlo
  unfold Vsa.Densify.ramBase Vsa.Densify.ramSize at hhi
  have hs : snapshotMem[a]? = some (snapshotByte a) := by
    rw [snapshot_lookup, if_pos ⟨hlo, by omega⟩]
  show ((physicalConfigS0 heapMem).σ.mem[a]?).isSome
  rw [physicalConfigS0_mem]
  obtain ⟨b', hb'⟩ : ∃ b', heapMem[a]? = some b' := memExtends_writeLog snapshotMem fullLog a _ hs
  rw [hb']
  rfl

/-- **The control witness of the final theorem's hypothesis**: the dense
control configuration is its own fill-with-zero. -/
theorem loaded_fill :
    Vsa.Refine.Loaded interpRunLayout nativeNameProgram (Vsa.Densify.fillZero heapConfig) := by
  have e := Vsa.Densify.fillZero_eq_of_dense heapConfig_dense
  rw [e]
  exact loaded

#print axioms readyFacts
#print axioms loaded
#print axioms loaded_fill

end Vsa.Sim.NativeNameAudit.Control
