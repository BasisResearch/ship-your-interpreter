import VsaIris.Interp.World
import Vsa.Sim.NativeNameAudit.ControlLoaded

/-!
# Vacuity of the boundary world (package A0)

`world_of_boundary`'s hypotheses hold together at the control program of
`Vsa/Sim/NativeNameAudit/Control*`: its checked `Loaded interpRunLayout
nativeNameProgram heapConfig` gives the `Boot` bundle (`ctlBoot`), including
the boundary heap facts (`Control.bootHeap`) from which `BootGap` follows
(`ctl_bootGap`). Both regimes start: the counted one at 2^20
credits, the uncounted one unconditionally.
-/

set_option autoImplicit false

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProofMode
open VsaIris VsaIris.VsaHeap
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr Vsa.Sim Vsa.Sim.DlHeap
open Vsa.Sim.NativeNameAudit Vsa.Sim.NativeNameAudit.Control
open Vsa.Sim.OutputAliasLoaded Vsa.Sim.LayoutInstance

/-- The control's boundary bundle, with every witness concrete. -/
def ctlBoot : Boot heapConfig nativeNameProgram where
  stmts := 0x82000000
  count := 2
  inp := fixedInp
  N := Nfixed
  A := heapArena
  φf := phif
  φc := phic
  aLeft := 0
  D := ownershipData
  top := heapTop
  brkv := heapBrk
  chunks := heapChunks
  bins := fun _ => []
  repr := by
    show ProgramRepr (physicalConfig heapMem).σ.mem 0x82000000 2 nativeNameProgram
    rw [physicalConfig_mem]
    exact heapAstReads.programWithin.erase
  ready := readyFacts
  owned := by
    show RuntimeOwnership.InitialOwned (physicalConfig heapMem).σ.mem heapArena stackSL phif phic
      0x82000000 2 ownershipData
    rw [physicalConfig_mem]
    exact initialOwned
  alloc := by
    show InitialAllocatorAt (physicalConfig heapMem).σ.mem exts (RuntimeOwnership.ReallocExtent alloc) 0x82000000 2
      heapTop heapBrk heapChunks fun _ => []
    rw [physicalConfig_mem]
    exact ⟨heapAt, heapCapacity⟩
  frame := bootFrame
  heapFacts := by
    show BootHeapFacts (physicalConfig heapMem).σ.mem Control.shared (phif 0) heapTop heapBrk
      heapChunks bootFrame
    rw [physicalConfig_mem]
    exact bootHeapFacts

/-- **The boundary gap holds at the control**, derived from its `Loaded`
facts (`Control.bootHeap`). -/
theorem ctl_bootGap : BootGap ctlBoot ctlBoot.G := ctlBoot.gap

/-- The counted regime at 2^20 credits: the control's top chunk leaves room. -/
theorem ctl_regime_counted : RegimeOK ctlBoot.top (.counted (2 ^ 20)) := by
  show 2 * 2 ^ 20 + extendSlack ≤ heapEnd - heapTop
  decide

section Iris

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

/-- **`world_of_boundary` applies at the control, in either regime.** -/
theorem ctl_world (ρ : Regime) (hρ : RegimeOK ctlBoot.top ρ) :
    ([∗map] k ↦ v ∈ ctlBoot.bytes ctlBoot.G, iprop(k ↦ₘ v)) ∗
      consoleOwn (GF := GF) (Vsa.Machine.output heapConfig.σ) ⊢
      |==> ∃ γf γc : GName, (letI : InterpGS GF := ⟨γf, γc⟩; bootRes ctlBoot ρ) :=
  world_of_boundary ctlBoot ρ hρ

theorem ctl_world_counted :
    ([∗map] k ↦ v ∈ ctlBoot.bytes ctlBoot.G, iprop(k ↦ₘ v)) ∗
      consoleOwn (GF := GF) (Vsa.Machine.output heapConfig.σ) ⊢
      |==> ∃ γf γc : GName,
        (letI : InterpGS GF := ⟨γf, γc⟩; bootRes ctlBoot (.counted (2 ^ 20))) :=
  ctl_world _ ctl_regime_counted

theorem ctl_world_uncounted :
    ([∗map] k ↦ v ∈ ctlBoot.bytes ctlBoot.G, iprop(k ↦ₘ v)) ∗
      consoleOwn (GF := GF) (Vsa.Machine.output heapConfig.σ) ⊢
      |==> ∃ γf γc : GName, (letI : InterpGS GF := ⟨γf, γc⟩; bootRes ctlBoot .uncounted) :=
  ctl_world _ (regimeOK_uncounted _)

end Iris

#print axioms ctl_bootGap
#print axioms ctl_world_counted
#print axioms ctl_world_uncounted

end VsaIris.Interp
