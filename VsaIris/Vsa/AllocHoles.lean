import VsaIris.Vsa.AllocBase
import VsaIris.Vsa.MallocRunAll

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

`malloc`'s runs in both regimes are proved (`mallocChgRun_proved`,
`mallocLocalRun_proved`, `MallocRunAll.lean`); the fields left are `free`'s
and `realloc`'s. `allocSpecs` turns runs into the Iris specs
that callers use, for every `MachWP` (`twpW` for `term_sim`, `wpW` for
`stuck_sim`): the runs are first-order, so the specs are WP-agnostic.
-/

namespace VsaIris.VsaHeap

open VsaIris.Inst VsaIris.Sym VsaIris.MallocFast

/-- **The allocator's runs at the binary** (`IrisHoles.alloc`). -/
structure AllocHoles : Prop where
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
  counted := dlMallocChgImpl_of_run (mallocChgRun_proved live hl) shapeLocal_vsaLayoutP
    roomLocal_vsaRoomB vsaAllocRegs_nodup
  uncounted := dlMallocImpl_of_localRuns (mallocLocalRun_proved live hl) (h.freeLocalRun live hl)
    shapeLocal_vsaLayoutP vsaAllocRegs_nodup
  freeCounted := dlFreeRoomImpl_of_run (h.freeChgRun live hl) shapeLocal_vsaLayoutP
    roomLocal_vsaRoomB vsaAllocRegs_nodup
  reallocUncounted := dlReallocImpl_of_localRun (h.reallocLocalRun live hl) shapeLocal_vsaLayoutP
    vsaAllocRegs_nodup (by decide)

end VsaIris.VsaHeap
