import VsaIris.MallocChg
import VsaIris.Vsa.Malloc
import Vsa.While.Cost

/-!
# The counted heap at the fixed binary

The counted regime's resources for the binary's allocator:

* `vsaLayoutP`: `vsaLayout` whose shape also fixes a page-aligned break
  (`PHeapAt`). `malloc_extend_top` extends the top in place only from a
  page-aligned end (`0x80004f70`). Otherwise it can return NULL whatever the
  room (`0x80004f94`), or fencepost the old top, which `ChunkWalk` cannot
  describe. Every path keeps the break page-aligned. The shape also bounds
  the `binblocks` word to 32 bits. `PROOF_CLOSURE_PLAN.md` §2 and
  INTERP_DESIGN Q5 record the boundary facts these need.
* `vsaRoomB`: `k` credits back `2 k + extendSlack` bytes between the top chunk
  and `__heap_end`. That is `InitialAllocatorAt.capacity` with the
  derivation's cost as the credits (`roomB_of_initial`). Top extension draws
  on this room through `sbrk`, so the top chunk itself may be small.
* `vsaChg`: a request of `n` bytes is charged at least `roundUp16 n` credits,
  the cost model's unit (`Vsa/While/Cost.lean`). Its chunk
  (`physSize n ≤ 2 · roundUp16 n`, `physSize_le_chg`) then fits the room it
  spends.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap

/-- The block-heap shape with a page-aligned break and a `binblocks` word of
32 bits, one per block of four bins: `_malloc_r`'s block search shifts a
mask up to the next set bit, and a bit above 31 would index past bin 127. -/
structure PHeapAt (m : Mem) (H : List (Nat × Nat)) (top brkv : Nat) (chunks : List Chunk)
    (bins : Nat → List Nat) : Prop where
  heap : BlockHeapAt m H top brkv chunks bins
  brk_page : brkv % 4096 = 0
  bb_lt : ∀ bb, read64 m binblocksAddr = some bb → bb < 2 ^ 32

/-- The live blocks start at distinct addresses. `free` releases the chunk
below its argument, so no other live block may start there. -/
abbrev Starts (H : List (Nat × Nat)) : Prop := (H.map Prod.fst).Nodup

theorem Starts.cons {H : List (Nat × Nat)} {p n : Nat} (hst : Starts H)
    (hf : ∀ e ∈ H, e.1 ≠ p) : Starts ((p, n) :: H) := by
  refine List.nodup_cons.2 ⟨fun hm => ?_, hst⟩
  obtain ⟨e, he, heq⟩ := List.mem_map.1 hm
  exact hf e he heq

/-- The owned image has the page-aligned block-heap shape, over live blocks
with distinct starts. -/
def pShape (img : Nat → BitVec 8) (H : List (Nat × Nat)) : Prop :=
  Starts H ∧ ∃ m top brkv chunks bins, ImgOn (vsaFoot H) img m ∧ PHeapAt m H top brkv chunks bins

/-- **The binary's dlmalloc layout, with a page-aligned break.** -/
def vsaLayoutP : DlLayout where
  global := allocGlobal
  lo := heapStart
  hi := heapEnd
  global_off_arena := allocGlobal_off_arena
  Shape := pShape

theorem heapFoot_vsaLayoutP (H : List (Nat × Nat)) : heapFoot vsaLayoutP H = vsaFoot H := rfl

theorem shapeLocal_vsaLayoutP : ShapeLocal vsaLayoutP := by
  rintro H img img' h ⟨hst, m, top, brkv, chunks, bins, hm, hs⟩
  exact ⟨hst, m, top, brkv, chunks, bins, fun a ha => (hm a ha).trans (by rw [h a ha]), hs⟩

/-- The page-aligned shape is the plain shape plus the alignment. -/
theorem pShape_imgShape {img : Nat → BitVec 8} {H : List (Nat × Nat)} (h : pShape img H) :
    imgShape img H := by
  obtain ⟨_, m, top, brkv, chunks, bins, hm, hs⟩ := h
  exact ⟨m, hm, top, brkv, chunks, bins, hs.heap⟩

/-- **The counted capacity**: `k` credits back `2 k + extendSlack` bytes
between the top chunk and the heap end. -/
def vsaRoomB : RoomPred := fun img H k =>
  Starts H ∧ ∃ m top brkv chunks bins, ImgOn (vsaFoot H) img m ∧ PHeapAt m H top brkv chunks bins ∧
    2 * k + extendSlack ≤ heapEnd - top

theorem roomLocal_vsaRoomB : RoomLocal vsaLayoutP vsaRoomB := by
  rintro H img img' k h ⟨hst, m, top, brkv, chunks, bins, hm, hs, hk⟩
  exact ⟨hst, m, top, brkv, chunks, bins, fun a ha => (hm a ha).trans (by rw [h a ha]), hs, hk⟩

theorem roomMono_vsaRoomB : RoomMono vsaRoomB := by
  rintro img H k j ⟨hst, m, top, brkv, chunks, bins, hm, hs, hk⟩
  exact ⟨hst, m, top, brkv, chunks, bins, hm, hs, by omega⟩

/-- A heap with capacity has the shape. -/
theorem vsaRoomB_shape {img : Nat → BitVec 8} {H : List (Nat × Nat)} {k : Nat}
    (h : vsaRoomB img H k) : vsaLayoutP.Shape img H := by
  obtain ⟨hst, m, top, brkv, chunks, bins, hm, hs, _⟩ := h
  exact ⟨hst, m, top, brkv, chunks, bins, hm, hs⟩

/-- **The charge**: a request of `n ≥ 1` bytes costs at least its rounded
size in credits. -/
def vsaChg : ChgRel := fun n c => 1 ≤ n ∧ Vsa.While.roundUp16 n ≤ c

/-- The chunk a charged request takes fits the room its credits back. -/
theorem physSize_le_chg {n c : Nat} (h : vsaChg n c) : physSize n ≤ 2 * c := by
  obtain ⟨h1, h2⟩ := h
  unfold Vsa.While.roundUp16 at h2
  unfold physSize
  omega

/-- A charged request's chunk exceeds its charge by at most one granule. -/
theorem physSize_le_chg16 {n c : Nat} (h : vsaChg n c) : physSize n ≤ c + 16 := by
  obtain ⟨h1, h2⟩ := h
  unfold Vsa.While.roundUp16 at h2
  unfold physSize
  omega

/-- A walk's chunks are in increasing address order. -/
theorem walk_addr_sorted {m : Mem} {p top : Nat} {cs : List Chunk} (h : ChunkWalk m p top cs) :
    cs.Pairwise (fun a b => a.addr < b.addr) := by
  induction h with
  | top => exact .nil
  | chunk _ _ hmin _ _ rest ih =>
    refine List.pairwise_cons.2 ⟨fun c hc => ?_, ih⟩
    have := (rest.chunk_bounds c hc).1
    simp only at this ⊢
    omega

/-- The in-use chunk payloads of a walk start at distinct addresses. -/
theorem starts_inuseBlocks {m : Mem} {p top : Nat} {cs : List Chunk} (h : ChunkWalk m p top cs) :
    Starts (inuseBlocks cs) := by
  have hs : ((inuseBlocks cs).map Prod.fst).Pairwise (· < ·) := by
    unfold inuseBlocks
    rw [List.map_filterMap]
    refine (walk_addr_sorted h).filterMap _ fun a b hab a' ha' b' hb' => ?_
    by_cases hu : a.inuse <;> by_cases hv : b.inuse <;> simp [hu, hv] at ha' hb'
    subst ha' hb'; omega
  exact hs.imp (fun h => Nat.ne_of_lt h)

/-- **The counted heap from VSA's boundary allocator.** An `InitialAllocatorAt`
with a page-aligned break, a 32-bit `binblocks` word and room for the top's
header gives the counted
heap over the in-use chunk payloads, with the derivation's cost `n` as the
credits. -/
theorem roomB_of_initial {m : Mem} {exts : List (Nat × Nat)} {reallocs : Nat × Nat → Prop}
    {stmts count top brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat}
    (h : InitialAllocatorAt m exts reallocs stmts count top brkv chunks bins)
    (hroom : top + 16 ≤ brkv) (hpage : brkv % 4096 = 0)
    (hbb : ∀ bb, read64 m binblocksAddr = some bb → bb < 2 ^ 32)
    {img : Nat → BitVec 8} (him : ImgOn (vsaFoot (inuseBlocks chunks)) img m)
    {p : Vsa.While.Program} (hp : Vsa.MemRepr.ProgramRepr m stmts count p)
    {st' : Vsa.While.St} {n : Nat} (hcost : Vsa.While.ExecSeqCost Vsa.While.initSt 0 0 p st' .normal n) :
    vsaRoomB img (inuseBlocks chunks) n :=
  ⟨starts_inuseBlocks h.heap.walk, m, top, brkv, chunks, bins, him, ⟨(blockHeapAt_of_heapAt h.heap hroom).1, hpage, hbb⟩,
    h.capacity p hp st' n hcost⟩

end VsaIris.VsaHeap
