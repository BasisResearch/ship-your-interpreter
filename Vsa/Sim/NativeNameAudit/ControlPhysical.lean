import Vsa.Sim.NativeNameAudit.ControlMemory
import Vsa.Sim.InitialSnapshotFacts

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc Vsa.Machine

namespace Vsa.Sim.NativeNameAudit.Control
open Vsa.Sim.OutputAliasLoaded Vsa.Sim.LayoutInstance

local macro "control_read" : tactic =>
  `(tactic| (simp only [read32, read64, readLE, lookup]; decide))

theorem memoryFacts : SnapshotMemoryFacts mem where
  mainRa := by control_read
  text := nativeName_text.transport (fun _ _ hhi => unchanged (Or.inl (by omega)))
  rodata := nativeName_rodata.transport (fun _ _ hhi => unchanged (Or.inl (by omega)))
  statics := by
    simpa (disch := decide) only [Code.ImageStaticsLoaded, Code.imgLldFmt,
      Code.imgDecPointStr, Code.imgParseSlotD, Code.imgParseSlotL, Code.imgFnSlot,
      Code.imgDecPointPtr, Code.imgMbCurMax, Code.imgImpurePtr, unchanged]
      using nativeName_statics
  console := ConsoleStream.of_agree (by
    intro k hk
    apply unchanged
    left
    unfold ConsoleFoot consoleImpurePtrAddr consoleReent consoleStdout consoleBuf at hk
    omega) nativeName_console
  exitRuntime := nativeName_exitRuntime.transport (by
    intro k hk
    obtain ⟨r, hr, hlo, hhi⟩ := hk
    have hb : ∀ r ∈ exitRuntimeExtraRegions, r.1 + r.2 ≤ 0x81000048 := by decide
    exact (unchanged (Or.inl (by have := hb r hr; omega))).symm)
  globals := by control_read
  depth := by control_read
  stackBytes := by
    intro k hlo hhi
    rw [unchanged (Or.inr (by change 0x87800000 ≤ k at hlo; omega))]
    exact nativeName_stackBytes k hlo hhi
  store := view.store
  storeSurvives := by
    intro m' hag
    exact (view.transport (fun k hk => hag k (storePage_outside_prefix hk))).store

theorem physicalFacts : InterpRunPhysicalFacts config 0x82000000 2 fixedInp
    Nfixed arena phif phic 0 := memoryFacts.physicalFacts

#print axioms memoryFacts
#print axioms physicalFacts

end Vsa.Sim.NativeNameAudit.Control
