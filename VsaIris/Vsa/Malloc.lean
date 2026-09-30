import VsaIris.MallocRun
import VsaIris.Vsa.Instance
import VsaIris.Vsa.HeapShape
import Vsa.AllocResource

/-!
# The Iris allocator spec at the fixed binary

`vsaDlMallocImpl` is `DlMallocImpl` for VSA's machine (`Inst.vsaModel`) and
heap (`vsaLayout`), from the two first-order runs of `MallocRun.lean`. It
fixes what the generic construction leaves open:

* the heap shape is local (`shapeLocal_vsaLayout`, from
  `BlockHeapAt.transport`);
* the registers the allocator owns during a call: the caller-saved
  temporaries and argument registers (`vsaClob`) and the callee-saved
  registers `_malloc_r`, `_free_r`, `_malloc_trim_r` and `_sbrk_r` spill and
  restore (`vsaSaved`: `s0 s1 s2 s3`). Both lists are read off
  `experiments/disasm.txt`, transitively through every callee (`__errno`,
  `_sbrk`, the lock hooks);
* the entries `malloc` (`0x80004790`) and `free` (`0x8000479c`),
  `Vsa.Alloc.mallocEntry`/`freeEntry`.

`shape_iff_state` reads the owned image's shape off an actual VSA
configuration: under `VsaOk` with the footprint present, the Iris shape is
`BlockHeap` of the configuration's memory. This is the form in which a proof
of `_malloc_r`'s local run consumes and produces it.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst

/-- Caller-saved registers the allocator may leave changed: `t0-t2`,
`a1-a7`, `t3-t6` (`a0` and `ra` are owned separately). -/
def vsaClob : List Nat := [5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31]

/-- Callee-saved registers the allocator spills and restores. -/
def vsaSaved : List Nat := [8, 9, 18, 19]

theorem vsaAllocRegs_nodup : (allocRegs vsaClob vsaSaved).Nodup := by
  unfold allocRegs vsaClob vsaSaved PC ra a0 sp
  decide

def mallocEntryBV : BitVec 64 := BitVec.ofNat 64 Vsa.Alloc.mallocEntry
def freeEntryBV : BitVec 64 := BitVec.ofNat 64 Vsa.Alloc.freeEntry

/-! ## Capacity -/

/-- The free top chunk can serve `k` more requests of at most `maxReq` bytes.

This is VSA's `TopChunkReserve` with its live-extent clause corrected. dlmalloc's
usable size is the chunk size minus 8, so a live block may extend into the
`prev_size` word of the chunk after it, which after a top split is the top
chunk. Only the top's header word must stay off live blocks. VSA's clause
(the whole top chunk off every live extent) fails after `malloc(24)`
(`vsa_reserve_fails_after_split`). -/
structure TopReserve (m : Mem) (exts : List (Nat × Nat)) (maxReq k top bytes : Nat) : Prop where
  request_fits : physSize maxReq < 2 ^ 31
  top_pointer : read64 m topAddr = some top
  size_header : read64 m (top + 8) = some (bytes + 1)
  top_aligned : top % 16 = 0
  size_aligned : bytes % 16 = 0
  arena_lo : heapStart ≤ top
  arena_hi : top + bytes ≤ heapEnd
  capacity : k * physSize maxReq + 32 ≤ bytes
  disjoint : ∀ e ∈ exts, e.1 + e.2 ≤ top + 8 ∨ top + bytes ≤ e.1

/-- Room for `k` more requests (none needed when `k = 0`). -/
def Reserve (m : Mem) (exts : List (Nat × Nat)) (maxReq k : Nat) : Prop :=
  0 < k → ∃ top bytes, TopReserve m exts maxReq k top bytes

theorem Reserve.zero (m : Mem) (exts : List (Nat × Nat)) (maxReq : Nat) :
    Reserve m exts maxReq 0 := fun h => absurd h (Nat.lt_irrefl 0)

end VsaIris.VsaHeap
