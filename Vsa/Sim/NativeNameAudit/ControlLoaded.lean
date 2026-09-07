import Vsa.Sim.NativeNameAudit.ControlOwnership

namespace Vsa.Sim.NativeNameAudit.Control
open Vsa.Sim.OutputAliasLoaded Vsa.Sim.LayoutInstance

/-- A concrete dense snapshot inhabits the live ownership boundary. -/
theorem readyFacts : InterpRunReadyFacts config 0x82000000 2 fixedInp
    Nfixed arena phif phic 0 where
  toInterpRunPhysicalFacts := physicalFacts
  ownership := ⟨ownershipData, initialOwned⟩

theorem loaded : Vsa.Refine.Loaded interpRunLayout nativeNameProgram config :=
  ⟨0x82000000, 2, programWithin.erase,
    fixedInp, Nfixed, arena, phif, phic, 0, readyFacts⟩

#print axioms readyFacts
#print axioms loaded

end Vsa.Sim.NativeNameAudit.Control
