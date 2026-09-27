import VsaIris.MallocChg
import VsaIris.Vsa.Malloc
import Vsa.While.Cost

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap

structure PHeapAt (m : Mem) (H : List (Nat × Nat)) (top brkv : Nat) (chunks : List Chunk)
    (bins : Nat → List Nat) : Prop where
  heap : BlockHeapAt m H top brkv chunks bins
  brk_page : brkv % 4096 = 0
  bb_lt : ∀ bb, read64 m binblocksAddr = some bb → bb < 2 ^ 32

abbrev Starts (H : List (Nat × Nat)) : Prop := (H.map Prod.fst).Nodup

theorem Starts.cons {H : List (Nat × Nat)} {p n : Nat} (hst : Starts H)
    (hf : ∀ e ∈ H, e.1 ≠ p) : Starts ((p, n) :: H) := by
  refine List.nodup_cons.2 ⟨fun hm => ?_, hst⟩
  obtain ⟨e, he, heq⟩ := List.mem_map.1 hm
  exact hf e he heq

def pShape (img : Nat → BitVec 8) (H : List (Nat × Nat)) : Prop :=
  Starts H ∧ ∃ m top brkv chunks bins, ImgOn (vsaFoot H) img m ∧ PHeapAt m H top brkv chunks bins

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

def vsaRoomB : RoomPred := fun img H k =>
  Starts H ∧ ∃ m top brkv chunks bins, ImgOn (vsaFoot H) img m ∧ PHeapAt m H top brkv chunks bins ∧
    2 * k + extendSlack ≤ heapEnd - top

theorem roomLocal_vsaRoomB : RoomLocal vsaLayoutP vsaRoomB := by
  rintro H img img' k h ⟨hst, m, top, brkv, chunks, bins, hm, hs, hk⟩
  exact ⟨hst, m, top, brkv, chunks, bins, fun a ha => (hm a ha).trans (by rw [h a ha]), hs, hk⟩

def vsaChg : ChgRel := fun n c => 1 ≤ n ∧ Vsa.While.roundUp16 n ≤ c

theorem physSize_le_chg {n c : Nat} (h : vsaChg n c) : physSize n ≤ 2 * c := by
  obtain ⟨h1, h2⟩ := h
  unfold Vsa.While.roundUp16 at h2
  unfold physSize
  omega

theorem physSize_le_chg16 {n c : Nat} (h : vsaChg n c) : physSize n ≤ c + 16 := by
  obtain ⟨h1, h2⟩ := h
  unfold Vsa.While.roundUp16 at h2
  unfold physSize
  omega

theorem walk_addr_sorted {m : Mem} {p top : Nat} {cs : List Chunk} (h : ChunkWalk m p top cs) :
    cs.Pairwise (fun a b => a.addr < b.addr) := by
  induction h with
  | top => exact .nil
  | chunk _ _ hmin _ _ rest ih =>
    refine List.pairwise_cons.2 ⟨fun c hc => ?_, ih⟩
    have := (rest.chunk_bounds c hc).1
    simp only at this ⊢
    omega

theorem starts_inuseBlocks {m : Mem} {p top : Nat} {cs : List Chunk} (h : ChunkWalk m p top cs) :
    Starts (inuseBlocks cs) := by
  have hs : ((inuseBlocks cs).map Prod.fst).Pairwise (· < ·) := by
    unfold inuseBlocks
    rw [List.map_filterMap]
    refine (walk_addr_sorted h).filterMap _ fun a b hab a' ha' b' hb' => ?_
    by_cases hu : a.inuse <;> by_cases hv : b.inuse <;> simp [hu, hv] at ha' hb'
    subst ha' hb'; omega
  exact hs.imp (fun h => Nat.ne_of_lt h)

end VsaIris.VsaHeap
