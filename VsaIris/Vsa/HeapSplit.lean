import VsaIris.Vsa.HeapTake
import VsaIris.Vsa.MallocFastHeap
import VsaIris.Vsa.HeapWin

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.MallocFast

def SplitW (top nb : Nat) (a : Nat) : Prop :=
  (top + 8 ≤ a ∧ a < top + 16) ∨ (topAddr ≤ a ∧ a < topAddr + 8) ∨
    (top + nb + 8 ≤ a ∧ a < top + nb + 16)

theorem PHeapAt.topSplit {m m' : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} (h : PHeapAt m H top brkv chunks bins)
    {nb n : Nat} (hnb16 : nb % 16 = 0) (hnb32 : 32 ≤ nb) (hn8 : n + 8 ≤ nb)
    (hroom : top + nb + 32 ≤ brkv)
    (hvic : read64 m' (top + 8) = some (nb + 1))
    (htopw : read64 m' topAddr = some (top + nb))
    (hrem : read64 m' (top + nb + 8) = some (brkv - top - nb + 1))
    (hag : ∀ a, vsaFoot H a → ¬ SplitW top nb a → m'[a]? = m[a]?) :
    PHeapAt m' ((top + 16, n) :: H) (top + nb) brkv (chunks ++ [⟨top, nb, true⟩]) bins := by
  obtain ⟨B, hpage, hbbl⟩ := h
  have hH := B.heap
  have hlo := hH.walk.le
  have hcb := hH.walk.chunk_bounds
  have hbrk := hH.brk_le
  obtain ⟨hal, htop16⟩ := hH.aligned
  unfold heapStart at hlo
  have hG : ∀ w, allocGlobal w → SplitW top nb w → topAddr ≤ w ∧ w < topAddr + 8 := by
    intro w hg hu; unfold allocGlobal InRange at hg; unfold SplitW at hu; omega
  obtain ⟨gS, gB, gP, gM, gI, gBb, -⟩ := hH.keep_globals hag hG
  obtain ⟨kBins, kFoot⟩ := B.keep_free hag hG fun c hc _ w hw => by
    have := hcb c hc; unfold SplitW topAddr avAddr at hw; unfold heapStart at this; omega
  have Kc : ∀ c ∈ chunks, read64 m' (c.addr + 8) = read64 m (c.addr + 8) := fun c hc =>
    B.keep_hdr hag (.inr ⟨c, hc, rfl⟩) fun w hw => by
      have := hcb c hc; unfold SplitW topAddr avAddr at hw; unfold heapStart at this; omega
  have hcs : chunkSize (nb + 1) = nb := by unfold chunkSize; omega
  have hpi : prevInuse (brkv - top - nb + 1) = true := by
    unfold prevInuse; rw [beq_iff_eq]; omega
  have hwnew : ChunkWalk m' top (top + nb) [⟨top, nb, true⟩] := by
    have w := ChunkWalk.chunk (m := m') (top := top + nb) (cs := []) (h := nb + 1)
      (h' := brkv - top - nb + 1) hvic (by omega) (by rw [hcs]; omega) (by rw [hcs]; omega)
      (by rw [hcs]; exact hrem) (by rw [hcs]; exact .top)
    rwa [hcs, hpi] at w
  have hwalk : ChunkWalk m' heapStart (top + nb) (chunks ++ [⟨top, nb, true⟩]) := by
    refine hH.walk.extend Kc (fun h1 hh1 => ⟨nb + 1, hvic, ?_⟩) hwnew
    rw [hH.top_header] at hh1
    cases hh1
    have := hH.top_size
    unfold prevInuse
    rw [show (nb + 1) % 2 = 1 by omega, show (brkv - top + 1) % 2 = 1 by omega]
  have hinuse : ∀ c ∈ chunks ++ [(⟨top, nb, true⟩ : Chunk)], c.inuse = false → c ∈ chunks := by
    intro c hc hf
    rcases List.mem_append.mp hc with hc | hc
    · exact hc
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc; cases hf
  have hnew : (⟨top, nb, true⟩ : Chunk) ∈ chunks ++ [⟨top, nb, true⟩] :=
    List.mem_append_right _ List.mem_cons_self
  obtain ⟨fB, fF⟩ := hH.free_to (fun c hc _ => List.mem_append_left _ hc) hinuse
  refine ⟨⟨{ sbrk_base := gS, brk := gB, brk_le := hbrk, top_ptr := htopw
             top_le := by omega, top_size := by omega
             top_header := by
               rw [show brkv - (top + nb) + 1 = brkv - top - nb + 1 by omega]; exact hrem
             top_pad := gP, max_sbrked := gM, mallinfo := gI, first_prev := ?_
             walk := hwalk, coalesced := ?_, footer := fun c hc hf => kFoot c (hinuse c hc hf) hf
             bins_list := kBins, bins_nodup := hH.bins_nodup
             bin_free := fB, free_binned := fF, remainder := hH.remainder
             binblocks_present := gBb ▸ hH.binblocks_present
             binblocks := fun bb hbb => hH.binblocks bb (gBb ▸ hbb)
             live := ?_, exact := ?_ }, by omega⟩, hpage, fun bb hbb => hbbl bb (gBb ▸ hbb)⟩
  · rcases hH.walk.head_or_top with he | ⟨c, hc, hca⟩
    · rw [show heapStart = top from he, hvic]
      simp only [Option.any, beq_iff_eq]; omega
    · rw [show heapStart = c.addr from hca.symm, Kc c hc, hca]
      exact hH.first_prev
  · intro i hi
    simp only [List.length_append, List.length_cons, List.length_nil] at hi
    by_cases hlt : i + 1 < chunks.length
    · rw [List.getElem_append_left (by omega), List.getElem_append_left (by omega)]
      exact hH.coalesced i hlt
    · refine .inr ?_
      rw [List.getElem_append_right (by omega)]
      simp
  · intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨⟨top, nb, true⟩, hnew, rfl, by simp, by simp; omega⟩
    · obtain ⟨c, hc, hu, h1, h2⟩ := hH.live e he
      exact ⟨c, List.mem_append_left _ hc, hu, h1, h2⟩
  · intro e he _
    rcases List.mem_cons.mp he with rfl | he'
    · exact ⟨⟨top, nb, true⟩, hnew, rfl, rfl, by simp; omega⟩
    · obtain ⟨c, hc, hu, h1, h2⟩ := hH.exact e he' he'
      exact ⟨c, List.mem_append_left _ hc, hu, h1, h2⟩

theorem PHeapAt.topSplit_fresh {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} (h : PHeapAt m H top brkv chunks bins)
    {nb n : Nat} (hn8 : n + 8 ≤ nb) (hroom : top + nb + 32 ≤ brkv) :
    FreshAt H (top + 16) n ∧ (top + 16) % 16 = 0 := by
  have hH := h.heap.heap
  have hbrk := hH.brk_le
  have hlo := hH.walk.le
  have htop16 := hH.aligned.2
  refine ⟨⟨⟨by unfold heapStart at hlo; omega, by show heapStart ≤ _; omega,
    by show _ ≤ heapEnd; omega, fun e he a ha hea => ?_⟩, fun e he heq => ?_⟩, by omega⟩
  rotate_right
  · obtain ⟨c1, hc1, _, h1, _⟩ := hH.exact e he he
    have := (hH.walk.chunk_bounds c1 hc1)
    omega
  obtain ⟨c1, hc1, _, h1, h2⟩ := hH.live e he
  have hb1 := hH.walk.chunk_bounds c1 hc1
  unfold InExt at ha hea
  simp only at ha
  omega

end VsaIris.VsaHeap
