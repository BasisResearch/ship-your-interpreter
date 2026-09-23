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
theorem vsaDlMallocImpl (live : Nat → Prop) (gpv : BitVec 64) (headroom : Nat)
    (text : List (Nat × BitVec 8))
    (hm : MallocLocalRun (vsaModel live) vsaLayout mallocEntryBV gpv vsaClob vsaSaved headroom text)
    (hf : FreeLocalRun (vsaModel live) vsaLayout freeEntryBV gpv vsaClob vsaSaved headroom text) :
    DlMallocImpl (vsaModel live) vsaLayout mallocEntryBV freeEntryBV gpv vsaClob vsaSaved
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

/-- VSA's capacity, read off the allocator's image: `AllocationReserve`
(a free top chunk with room for `k` requests of at most `maxReq` bytes). -/
def vsaRoom (maxReq : Nat) : RoomPred := fun img H k =>
  ∃ m, ImgOn (vsaFoot H) img m ∧ AllocationReserve vsaArena m H maxReq k

theorem roomLocal_vsa (maxReq : Nat) : RoomLocal vsaLayout (vsaRoom maxReq) := by
  rintro H img img' k h ⟨m, hm, hr⟩
  exact ⟨m, fun a ha => (hm a ha).trans (by rw [h a ha]), hr⟩

/-- `AllocationReserve` reads only the allocator's footprint: the top pointer
and the free top chunk's header. -/
theorem AllocationReserve.transport_foot {m m' : Mem} {H : List (Nat × Nat)} {maxReq k : Nat}
    (h : AllocationReserve vsaArena m H maxReq k) (hag : AgreeP (vsaFoot H) m m') :
    AllocationReserve vsaArena m' H maxReq k := by
  apply h.transport_bytes hag
  · intro j hj
    exact .inl (.inl ⟨by omega, by omega⟩)
  · intro top bytes reserve j hj
    obtain ⟨h1, h2, h3⟩ := reserve.header_geometry hj
    exact .inr ⟨h1, h2, fun e he hin => h3 e he hin⟩

/-- The capacity of the owned image holds at any memory carrying it. -/
theorem reserve_of_room {img : Nat → BitVec 8} {H : List (Nat × Nat)} {maxReq k : Nat}
    {m1 : Mem} (hroom : vsaRoom maxReq img H k) (him : ImgOn (vsaFoot H) img m1) :
    AllocationReserve vsaArena m1 H maxReq k := by
  obtain ⟨m, hm, hr⟩ := hroom
  exact AllocationReserve.transport_foot hr fun a ha => (hm a ha).trans (him a ha).symm

/-- **The allocator under capacity at the fixed binary.** -/
theorem vsaDlMallocRoomImpl (live : Nat → Prop) (maxReq : Nat) (gpv : BitVec 64)
    (headroom : Nat) (text : List (Nat × BitVec 8))
    (hrun : MallocRoomRun (vsaModel live) vsaLayout (vsaRoom maxReq) maxReq mallocEntryBV gpv
      vsaClob vsaSaved headroom text) :
    DlMallocRoomImpl (vsaModel live) vsaLayout (vsaRoom maxReq) maxReq mallocEntryBV gpv
      vsaClob vsaSaved headroom text :=
  dlMallocRoomImpl_of_run hrun shapeLocal_vsaLayout (roomLocal_vsa maxReq) vsaAllocRegs_nodup

end VsaIris.VsaHeap
