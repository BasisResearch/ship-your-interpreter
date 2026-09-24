import Vsa.Sim.NativeNameAudit.ControlOwnership

/-!
# The control's boundary heap facts (`LayoutInstance.BootHeap`)

The global frame's `Env` struct, names array and values array are the payloads
of the in-use chunks at `0x80fffff0`, `0x81000030` and `0x810000f0`; the break
`0x82001000` is page-aligned; `binblocks` is zero; and the snapshot carries the
ELF's `_impure_data._stderr = &__sf[2]`. Each fact is one kernel `decide` or a
read through the heap log.
-/

open Vsa.MemRepr Vsa.While

namespace Vsa.Sim.NativeNameAudit.Control
open RuntimeOwnership Vsa.Sim.DlHeap Vsa.Sim.OutputAliasLoaded Vsa.Sim.LayoutInstance

/-- The global frame's blocks as whole chunk payloads (`Env` 0x38, names 0x48,
values 0xc8). -/
def bootFrame : BootFrame where
  cap := 8
  pn := 0x81000040
  pv := 0x81000100
  sblk := (0x81000000, 0x38)
  nblk := (0x81000040, 0x48)
  vblk := (0x81000100, 0xc8)

theorem bootFrame_blocks : bootFrame.blocks =
    [(0x81000000, 0x38), (0x81000040, 0x48), (0x81000100, 0xc8)] := rfl

theorem bootFrameChunks : BootFrameChunks heapMem heapChunks shared 0x81000000 bootFrame where
  cap := heapStoreFacts.capacity
  names := heapStoreFacts.names
  vals := heapStoreFacts.values
  sblk := by decide
  arrays := fun _ => by decide
  live := by decide
  nodup := by decide
  unshared := by
    intro b hb k hlo hhi
    rw [bootFrame_blocks] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    unfold shared AstPage
    rcases hb with rfl | rfl | rfl <;> (dsimp only at hlo hhi; omega)
  cap_canon := rfl

/-- `_impure_data._stderr`, read off the snapshot through both logs. -/
theorem stderr_mem : read64 heapMem impureStderrAddr = some exitStderr := by
  refine read64_heap ?_ fun j hj => unchanged_low ?_
  · simp only [impureStderrAddr, consoleReent, exitStderr, read64, readLE, lookup]
    decide
  · unfold impureStderrAddr consoleReent; omega

/-- `binblocks`: empty bins, the word is zero. -/
theorem binblocks_mem : read64 heapMem binblocksAddr = some 0 := by
  refine read64_heap ?_ fun j hj => unchanged_low ?_
  · simp only [binblocksAddr, avAddr, read64, readLE, lookup]
    decide
  · unfold binblocksAddr avAddr; omega

/-- The shared bytes (three native names and the AST page) are RAM above the
HTIF words and below the stack. -/
theorem sharedGeom : SharedGeom shared stackSL where
  ram := by intro k hk; unfold shared AstPage at hk; omega
  htif := by intro k hk; unfold shared AstPage at hk; rw [tohostAddr_val]; omega
  stack := by intro k hk; unfold shared AstPage at hk; left; show k < 0x87800000; omega

theorem bootHeapFacts :
    BootHeapFacts heapMem shared 0x81000000 heapTop heapBrk heapChunks bootFrame where
  top_room := by decide
  brk_page := by decide
  binblocks := by
    intro bb h
    rw [binblocks_mem] at h
    obtain rfl := Option.some.inj h
    decide
  frame := bootFrameChunks
  stderr := stderr_mem
  shared_geom := sharedGeom


theorem bootHeap : BootHeap heapMem heapArena phif phic 0x82000000 2 ownershipData
    heapTop heapBrk heapChunks (fun _ => []) bootFrame where
  owned := initialOwned
  alloc := ⟨heapAt, heapCapacity⟩
  facts := bootHeapFacts

#print axioms bootHeap

end Vsa.Sim.NativeNameAudit.Control
