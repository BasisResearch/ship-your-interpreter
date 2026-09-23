import VsaIris.MallocRun
import VsaIris.Vsa.Instance
import VsaIris.Vsa.HeapShape
import Vsa.Alloc
import Vsa.Sim.AllocReserveTransport

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

/-- The heap shape reads only the allocator's footprint. -/
theorem shapeLocal_vsaLayout : ShapeLocal vsaLayout := by
  rintro H img img' h ⟨m, hm, hs⟩
  exact ⟨m, fun a ha => (hm a ha).trans (by rw [h a ha]), hs⟩

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

/-- **The allocator spec at the fixed binary**, from the two local runs. -/
theorem vsaDlMallocImpl (live : Nat → Prop) {SpOK : BitVec 64 → Prop} (gpv : BitVec 64)
    (headroom : Nat) (text : List (Nat × BitVec 8))
    (hm : MallocLocalRun (vsaModel live) vsaLayout SpOK mallocEntryBV gpv vsaClob vsaSaved headroom text)
    (hf : FreeLocalRun (vsaModel live) vsaLayout SpOK freeEntryBV gpv vsaClob vsaSaved headroom text) :
    DlMallocImpl (vsaModel live) vsaLayout SpOK mallocEntryBV freeEntryBV gpv vsaClob vsaSaved
      headroom text :=
  dlMallocImpl_of_localRuns hm hf shapeLocal_vsaLayout vsaAllocRegs_nodup

/-- The owned image's heap shape, read off an actual configuration: when the
footprint is present, the Iris shape of the total byte read is VSA's
`BlockHeap` of the memory. -/
theorem shape_iff_state {live : Nat → Prop} {c : Vsa.Machine.Config} {H : List (Nat × Nat)}
    (hok : VsaOk live c) (hlive : ∀ a, vsaFoot H a → live a) :
    vsaLayout.Shape ((vsaModel live).mem c) H ↔ BlockHeap c.σ.mem H :=
  imgShape_iff (imgOn_of_getD (fun a ha => hok.live a (hlive a ha)) (fun _ _ => rfl))

/-! ## Capacity -/

/-- The fixed binary's arena, as VSA's ledger states it (`Control.heapArena`). -/
def vsaArena : Vsa.RuntimeRepr.Arena := ⟨heapStart, heapEnd⟩

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

/-- VSA's reserve implies the corrected one. -/
theorem reserve_of_allocationReserve {m : Mem} {exts : List (Nat × Nat)} {maxReq k : Nat}
    (h : AllocationReserve vsaArena m exts maxReq k) : Reserve m exts maxReq k := by
  intro hk
  obtain ⟨top, bytes, r⟩ := h.available hk
  have ha := r.chunk.arena
  unfold vsaArena Vsa.RuntimeRepr.Arena.contains at ha
  refine ⟨top, bytes, r.chunk.request_fits, r.chunk.top_pointer, r.chunk.size_header,
    r.chunk.top_aligned, r.chunk.size_aligned, ha.1, ha.2, r.capacity, fun e he => ?_⟩
  rcases r.chunk.disjoint e he with d | d
  · right; exact d
  · left; omega

/-- **VSA's reserve clause fails after `malloc(24)`.** Whatever the memory,
once `av->top` reads `top + 32` (the top split of a 32-byte chunk at `top`)
and the ledger holds the returned `(top + 16, 24)`, no `AllocationReserve`
with a credit left holds: the block ends at `top + 40`, inside the new top
chunk. So `MallocReturnAt.reserve` cannot be met by the binary's allocator for
such requests. -/
theorem vsa_reserve_fails_after_split (A : Vsa.RuntimeRepr.Arena) (m : Mem)
    (exts : List (Nat × Nat)) (maxReq k top : Nat) (hk : 0 < k)
    (htop : read64 m 0x8001ad20 = some (top + 32)) :
    ¬ AllocationReserve A m ((top + 16, 24) :: exts) maxReq k := by
  intro h
  obtain ⟨top', bytes, r⟩ := h.available hk
  have tp := r.chunk.top_pointer
  rw [htop] at tp
  cases tp
  rcases r.chunk.disjoint _ List.mem_cons_self with d | d <;> simp only at d <;> omega

/-- The corrected reserve reads only the allocator's footprint. -/
theorem Reserve.transport_foot {m m' : Mem} {H : List (Nat × Nat)} {maxReq k : Nat}
    (h : Reserve m H maxReq k) (hag : AgreeP (vsaFoot H) m m') : Reserve m' H maxReq k := by
  intro hk
  obtain ⟨top, bytes, r⟩ := h hk
  have hP := physSize_min maxReq
  have hk1 : physSize maxReq ≤ k * physSize maxReq := Nat.le_mul_of_pos_left _ hk
  have cap := r.capacity
  have lo := r.arena_lo
  have hi := r.arena_hi
  unfold heapStart at lo
  unfold heapEnd at hi
  refine ⟨top, bytes, { r with
    top_pointer := (read64_agreeP hag fun j hj => .inl (.inl ⟨by unfold topAddr avAddr; omega,
      by unfold topAddr avAddr; omega⟩)).symm.trans r.top_pointer
    size_header := (read64_agreeP hag fun j hj => .inr ⟨by unfold heapStart; omega,
      by unfold heapEnd; omega, fun e he hin => by
        unfold InExt at hin
        rcases r.disjoint e he with d | d <;> omega⟩).symm.trans r.size_header }⟩

/-- VSA's capacity, read off the allocator's image: the corrected reserve. -/
def vsaRoom (maxReq : Nat) : RoomPred := fun img H k =>
  ∃ m, ImgOn (vsaFoot H) img m ∧ Reserve m H maxReq k

theorem roomLocal_vsa (maxReq : Nat) : RoomLocal vsaLayout (vsaRoom maxReq) := by
  rintro H img img' k h ⟨m, hm, hr⟩
  exact ⟨m, fun a ha => (hm a ha).trans (by rw [h a ha]), hr⟩

/-- The capacity of the owned image holds at any memory carrying it. -/
theorem reserve_of_room {img : Nat → BitVec 8} {H : List (Nat × Nat)} {maxReq k : Nat}
    {m1 : Mem} (hroom : vsaRoom maxReq img H k) (him : ImgOn (vsaFoot H) img m1) :
    Reserve m1 H maxReq k := by
  obtain ⟨m, hm, hr⟩ := hroom
  exact Reserve.transport_foot hr fun a ha => (hm a ha).trans (him a ha).symm

/-- **The allocator under capacity at the fixed binary.** -/
theorem vsaDlMallocRoomImpl (live : Nat → Prop) (maxReq : Nat) (SpOK : BitVec 64 → Prop)
    (gpv : BitVec 64) (headroom : Nat) (text : List (Nat × BitVec 8))
    (hrun : MallocRoomRun (vsaModel live) vsaLayout (vsaRoom maxReq) maxReq SpOK mallocEntryBV gpv
      vsaClob vsaSaved headroom text) :
    DlMallocRoomImpl (vsaModel live) vsaLayout (vsaRoom maxReq) maxReq SpOK mallocEntryBV gpv
      vsaClob vsaSaved headroom text :=
  dlMallocRoomImpl_of_run hrun shapeLocal_vsaLayout (roomLocal_vsa maxReq) vsaAllocRegs_nodup

end VsaIris.VsaHeap
