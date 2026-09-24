import VsaIris.Interp.World
import Vsa.Sim.NativeNameAudit.ControlLoaded

/-!
# Vacuity of the boundary world (package A0)

`world_of_boundary`'s hypotheses hold together at the control program of
`Vsa/Sim/NativeNameAudit/Control*`: its checked `Loaded interpRunLayout
nativeNameProgram heapConfig` gives the `Boot` bundle (`ctlBoot`), and the
named boundary gap `BootGap` (the three frame chunks, `top_room`, the
page-aligned break, the 32-bit `binblocks` word, the `stderr` pointer) is
checked against its memory. Both regimes start: the counted one at 2^20
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

/-- The global frame's blocks as whole chunk payloads (`Env` 0x38, names 0x48,
values 0xc8: the chunks at `0x80fffff0`, `0x81000030`, `0x810000f0`). -/
def ctlChunkGeom : FrameGeom where
  e := 0x81000000
  cap := 8
  pn := 0x81000040
  pv := 0x81000100
  par := 0
  sblk := (0x81000000, 0x38)
  nblk := (0x81000040, 0x48)
  vblk := (0x81000100, 0xc8)

theorem ctlChunkGeom_blocks : ctlChunkGeom.blocks =
    [(0x81000000, 0x38), (0x81000040, 0x48), (0x81000100, 0xc8)] := rfl

theorem ctl_room : ctlBoot.top + 16 ≤ ctlBoot.brkv := by
  show heapTop + 16 ≤ heapBrk
  decide

theorem ctl_frameChunks_mem :
    FrameChunks heapMem heapChunks Control.shared 0x81000000 ctlChunkGeom where
  env := rfl
  cap := heapStoreFacts.capacity
  names := heapStoreFacts.names
  vals := heapStoreFacts.values
  par := rfl
  sblk := by decide
  arrays := fun _ => by decide
  live := by decide
  nodup := by decide
  unshared := by
    rintro k ⟨b, hb, hk⟩
    rw [ctlChunkGeom_blocks] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    unfold Control.shared AstPage
    unfold InExt at hk
    rcases hb with rfl | rfl | rfl <;> (dsimp only at hk; omega)

theorem ctl_frameChunks :
    FrameChunks heapConfig.σ.mem ctlBoot.chunks ctlBoot.D.shared (ctlBoot.φf 0) ctlChunkGeom := by
  show FrameChunks (physicalConfig heapMem).σ.mem heapChunks Control.shared (phif 0) ctlChunkGeom
  rw [physicalConfig_mem, show phif 0 = 0x81000000 from rfl]
  exact ctl_frameChunks_mem

/-- `_impure_data._stderr` at the control (INTERP_DESIGN.md Q6), read off the
snapshot through both logs. -/
theorem ctl_stderr_mem : read64 heapMem Stdio.stderrPtrAddr = some exitStderr := by
  refine read64_heap ?_ fun j hj => unchanged_low ?_
  · simp only [Stdio.stderrPtrAddr, consoleReent, exitStderr, read64, readLE, lookup]
    decide
  · unfold Stdio.stderrPtrAddr consoleReent; omega

theorem ctl_stderr : read64 heapConfig.σ.mem Stdio.stderrPtrAddr = some exitStderr := by
  show read64 (physicalConfig heapMem).σ.mem _ = _
  rw [physicalConfig_mem]
  exact ctl_stderr_mem

/-- `binblocks` at the control: empty bins, the word is zero. -/
theorem ctl_binblocks_mem : read64 heapMem binblocksAddr = some 0 := by
  refine read64_heap ?_ fun j hj => unchanged_low ?_
  · simp only [binblocksAddr, avAddr, read64, readLE, lookup]
    decide
  · unfold binblocksAddr avAddr; omega

theorem ctl_binblocks :
    ∀ bb, read64 heapConfig.σ.mem binblocksAddr = some bb → bb < 2 ^ 32 := by
  show ∀ bb, read64 (physicalConfig heapMem).σ.mem binblocksAddr = some bb → bb < 2 ^ 32
  rw [physicalConfig_mem, ctl_binblocks_mem]
  intro bb h
  obtain rfl := Option.some.inj h
  decide

/-- **The boundary gap holds at the control.** -/
theorem ctl_bootGap : BootGap ctlBoot ctlChunkGeom where
  top_room := ctl_room
  brk_page := by show heapBrk % 4096 = 0; decide
  binblocks := ctl_binblocks
  frame := ctl_frameChunks
  stderr := ctl_stderr

/-- The counted regime at 2^20 credits: the control's top chunk leaves room. -/
theorem ctl_regime_counted : RegimeOK ctlBoot.top (.counted (2 ^ 20)) := by
  show 2 * 2 ^ 20 + extendSlack ≤ heapEnd - heapTop
  decide

section Iris

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

/-- **`world_of_boundary` applies at the control, in either regime.** -/
theorem ctl_world (ρ : Regime) (hρ : RegimeOK ctlBoot.top ρ) :
    ([∗map] k ↦ v ∈ ctlBoot.bytes ctlChunkGeom, iprop(k ↦ₘ v)) ∗
      consoleOwn (GF := GF) (Vsa.Machine.output heapConfig.σ) ⊢
      |==> ∃ γf γc : GName, (letI : InterpGS GF := ⟨γf, γc⟩; bootRes ctlBoot ρ) :=
  world_of_boundary ctlBoot ctl_bootGap ρ hρ

theorem ctl_world_counted :
    ([∗map] k ↦ v ∈ ctlBoot.bytes ctlChunkGeom, iprop(k ↦ₘ v)) ∗
      consoleOwn (GF := GF) (Vsa.Machine.output heapConfig.σ) ⊢
      |==> ∃ γf γc : GName,
        (letI : InterpGS GF := ⟨γf, γc⟩; bootRes ctlBoot (.counted (2 ^ 20))) :=
  ctl_world _ ctl_regime_counted

theorem ctl_world_uncounted :
    ([∗map] k ↦ v ∈ ctlBoot.bytes ctlChunkGeom, iprop(k ↦ₘ v)) ∗
      consoleOwn (GF := GF) (Vsa.Machine.output heapConfig.σ) ⊢
      |==> ∃ γf γc : GName, (letI : InterpGS GF := ⟨γf, γc⟩; bootRes ctlBoot .uncounted) :=
  ctl_world _ (regimeOK_uncounted _)

end Iris

#print axioms ctl_bootGap
#print axioms ctl_world_counted
#print axioms ctl_world_uncounted

end VsaIris.Interp
