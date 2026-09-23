import VsaIris.Vsa.HeapRoom
import VsaIris.Vsa.AllocCode
import VsaIris.Vsa.MallocConsumer

/-!
# `IrisHoles.alloc`: the allocator's runs at the binary

`AllocHoles` is the exact allocator assumption of the Iris route: the
first-order runs of the binary's `malloc`, `free` and `realloc`, in both
regimes (INTERP_DESIGN §3), over

* the page-aligned heap shape `vsaLayoutP` and, counted, the capacity
  `vsaRoomB` with the charge `vsaChg` (`Vsa/HeapRoom.lean`);
* the allocator's code `allocText` (`AllocCode.lean`), for any `live` set
  holding it;
* the caller's stack discipline `SpOKA` with `allocHeadroom` bytes of
  scratch;
* the owned registers `allocRegs vsaClob vsaSaved`.

Each field is proved by lane H4, which then deletes the field and its
`VsaIris/HOLES.md` row. `allocSpecs` turns the fields into the Iris specs
that callers use, for every `MachWP` (`twpW` for `term_sim`, `wpW` for
`stuck_sim`): the runs are first-order, so the specs are WP-agnostic.
-/

namespace VsaIris.VsaHeap

open VsaIris.Inst VsaIris.Sym VsaIris.MallocFast

/-- Stack scratch for the allocator's deepest call chain: `_realloc_r` (64
bytes) over `_malloc_r` (96), over `_free_r` (32) from `malloc_extend_top`,
`_malloc_trim_r` (48) and `_sbrk_r`/`_sbrk` (32), rounded up. -/
def allocHeadroom : Nat := 512

/-- The caller's stack pointer for an allocator call: 16-aligned, in 32-bit
RAM, with `allocHeadroom` bytes above the HTIF words. -/
structure SpOKA (s : BitVec 64) : Prop where
  lo : Vsa.Sim.tohostAddr + 16 + allocHeadroom ≤ s.toNat
  hi : s.toNat ≤ 0x100000000
  align : s.toNat % 16 = 0

/-- The code bytes of the allocator are `live`. -/
abbrev AllocLive (live : Nat → Prop) : Prop := ∀ p ∈ allocText, live p.1

/-- **The allocator's runs at the binary** (`IrisHoles.alloc`). -/
structure AllocHoles : Prop where
  /-- Counted `malloc`: a charged request from a heap with credits returns a
  fresh block. -/
  mallocChgRun : ∀ live, AllocLive live →
    MallocChgRun (vsaModel live) vsaLayoutP vsaRoomB vsaChg SpOKA mallocEntryBV gpV vsaClob
      vsaSaved allocHeadroom allocText
  /-- Uncounted `malloc`: NULL with the heap unchanged, or a fresh block. -/
  mallocLocalRun : ∀ live, AllocLive live →
    MallocLocalRun (vsaModel live) vsaLayoutP SpOKA mallocEntryBV gpV vsaClob vsaSaved
      allocHeadroom allocText
  /-- Counted `free`: the block returns to the heap, every credit kept. -/
  freeChgRun : ∀ live, AllocLive live →
    FreeRoomRun (vsaModel live) vsaLayoutP vsaRoomB vsaRoomB SpOKA freeEntryBV gpV vsaClob
      vsaSaved allocHeadroom allocText
  /-- Uncounted `free`. -/
  freeLocalRun : ∀ live, AllocLive live →
    FreeLocalRun (vsaModel live) vsaLayoutP SpOKA freeEntryBV gpV vsaClob vsaSaved
      allocHeadroom allocText
  /-- Counted `realloc` (grow): a fresh block holding the old contents. -/
  reallocChgRun : ∀ live, AllocLive live →
    ReallocChgRun (vsaModel live) vsaLayoutP vsaRoomB vsaChg SpOKA reallocEntryBV gpV vsaClob
      vsaSaved allocHeadroom allocText
  /-- Uncounted `realloc` (grow): NULL with the block kept, or a fresh copy. -/
  reallocLocalRun : ∀ live, AllocLive live →
    ReallocLocalRun (vsaModel live) vsaLayoutP SpOKA reallocEntryBV gpV vsaClob vsaSaved
      allocHeadroom allocText

/-- The allocator's Iris specs from its runs: both regimes of `malloc`,
`free` and `realloc`, at the binary. -/
structure AllocSpecs (live : Nat → Prop) : Prop where
  counted : DlMallocChgImpl (vsaModel live) vsaLayoutP vsaRoomB vsaChg SpOKA mallocEntryBV gpV
    vsaClob vsaSaved allocHeadroom allocText
  uncounted : DlMallocImpl (vsaModel live) vsaLayoutP SpOKA mallocEntryBV freeEntryBV gpV vsaClob
    vsaSaved allocHeadroom allocText
  freeCounted : DlFreeRoomImpl (vsaModel live) vsaLayoutP vsaRoomB vsaRoomB SpOKA freeEntryBV gpV
    vsaClob vsaSaved allocHeadroom allocText
  reallocUncounted : DlReallocImpl (vsaModel live) vsaLayoutP SpOKA reallocEntryBV gpV vsaClob
    vsaSaved allocHeadroom allocText

theorem allocSpecs (h : AllocHoles) (live : Nat → Prop) (hl : AllocLive live) :
    AllocSpecs live where
  counted := dlMallocChgImpl_of_run (h.mallocChgRun live hl) shapeLocal_vsaLayoutP
    roomLocal_vsaRoomB vsaAllocRegs_nodup
  uncounted := dlMallocImpl_of_localRuns (h.mallocLocalRun live hl) (h.freeLocalRun live hl)
    shapeLocal_vsaLayoutP vsaAllocRegs_nodup
  freeCounted := dlFreeRoomImpl_of_run (h.freeChgRun live hl) shapeLocal_vsaLayoutP
    roomLocal_vsaRoomB vsaAllocRegs_nodup
  reallocUncounted := dlReallocImpl_of_localRun (h.reallocLocalRun live hl) shapeLocal_vsaLayoutP
    vsaAllocRegs_nodup (by decide)

end VsaIris.VsaHeap
