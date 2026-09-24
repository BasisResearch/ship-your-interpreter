import VsaIris.Vsa.HeapTake
import VsaIris.Vsa.MallocFastHeap

/-!
# The top split

`_malloc_r` serves a request no bin can fill by cutting `nb` bytes off the top
chunk (`0x80004bf0`): the victim's header becomes `nb | PREV_INUSE`, `av->top`
advances by `nb`, and the new top's header records the remaining size. Three
words change; everything else the heap shape reads is untouched.

`PHeapAt.topSplit` proves the resulting shape: the walk gains one in-use chunk
at its end (`ChunkWalk.extend`), the bins are unchanged, and the block
`(top + 16, n)` is live. `PHeapAt.topSplit_fresh` gives its freshness, as
`PHeapAt.take_fresh` does for a bin hit.

The same three words serve `malloc_extend_top`'s in-place growth, so the
statement takes the post-state's reads abstractly rather than a fixed write
log: a caller supplies them from its own store chain.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.MallocFast

/-- The three words a top split writes: the victim's header, `av->top`, and
the new top's header. -/
def SplitW (top nb : Nat) (a : Nat) : Prop :=
  (top + 8 ≤ a ∧ a < top + 16) ∨ (topAddr ≤ a ∧ a < topAddr + 8) ∨
    (top + nb + 8 ≤ a ∧ a < top + nb + 16)

/-- An aligned footprint word that is none of the three written words is kept. -/
theorem split_keep {m m' : Mem} {H : List (Nat × Nat)} {top nb a : Nat}
    (hag : ∀ b, vsaFoot H b → ¬ SplitW top nb b → m'[b]? = m[b]?)
    (hfoot : ∀ k, k < 8 → vsaFoot H (a + k)) (ha : a % 8 = 0) (ht : top % 8 = 0)
    (hnb : nb % 8 = 0) (h1 : a ≠ top + 8) (h2 : a ≠ topAddr) (h3 : a ≠ top + nb + 8) :
    read64 m' a = read64 m a := by
  refine read64_keep fun k hk => hag _ (hfoot k hk) ?_
  unfold topAddr avAddr at h2
  unfold SplitW topAddr avAddr
  omega

/-- **The top split.** Cutting `nb` bytes off the top chunk, leaving at least
`MINSIZE` above, gives the page-aligned heap with one more in-use chunk and
the block `(top + 16, n)` live. -/
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
  have hnew : (⟨top, nb, true⟩ : Chunk) ∈ chunks ++ [⟨top, nb, true⟩] :=
    List.mem_append_right _ List.mem_cons_self
  -- every global the shape reads is kept
  have Kg : ∀ a, ∀ _ : ∀ k, k < 8 → allocGlobal (a + k), a % 8 = 0 → a ≠ topAddr →
      a + 8 ≤ heapStart → read64 m' a = read64 m a := by
    intro a hg ha hne hs
    unfold heapStart at hs hlo
    exact split_keep hag (fun k hk => .inl (hg k hk)) ha (by omega) (by omega)
      (by omega) hne (by omega)
  have Kc : ∀ c ∈ chunks, read64 m' (c.addr + 8) = read64 m (c.addr + 8) := by
    intro c hc
    have hb := hcb c hc
    have := hal c hc
    unfold heapStart at hlo hb
    exact split_keep hag (foot_header B (.inr ⟨c, hc, rfl⟩)) (by omega) (by omega)
      (by omega) (by omega) (by unfold topAddr avAddr; omega) (by omega)
  have Kf : ∀ c ∈ chunks, c.inuse = false →
      read64 m' (c.addr + 16) = read64 m (c.addr + 16) ∧
      read64 m' (c.addr + 24) = read64 m (c.addr + 24) ∧
      read64 m' (c.addr + c.size) = read64 m (c.addr + c.size) := by
    intro c hc hf
    obtain ⟨hl, hft⟩ := foot_free B hc hf
    have hb := hcb c hc
    have hca := hal c hc
    have hsz := (walk_sizes hH.walk c hc).1
    unfold heapStart at hlo hb
    refine ⟨split_keep hag (fun k hk => hl k (by omega)) (by omega) (by omega) (by omega)
        (by omega) (by unfold topAddr avAddr; omega) (by omega),
      split_keep hag (fun k hk => ?_) (by omega) (by omega) (by omega)
        (by omega) (by unfold topAddr avAddr; omega) (by omega),
      split_keep hag hft (by omega) (by omega) (by omega)
        (by omega) (by unfold topAddr avAddr; omega) (by omega)⟩
    have := hl (k + 8) (by omega)
    rwa [show c.addr + 16 + (k + 8) = c.addr + 24 + k by omega] at this
  have Kbin : ∀ i, 0 < i → i < numBins →
      read64 m' (binAt i + 16) = read64 m (binAt i + 16) ∧
      read64 m' (binAt i + 24) = read64 m (binAt i + 24) := by
    intro i h0 h1
    have hg := binAt_geo i h1
    have hgl : ∀ x, binAt i ≤ x → x + 8 ≤ binAt i + 32 → ∀ k, k < 8 → allocGlobal (x + k) :=
      fun x h2 h3 k hk => .inl ⟨by omega, by omega⟩
    exact ⟨Kg _ (hgl _ (by omega) (by omega)) (by omega)
        (by unfold topAddr binAt avAddr; omega) (by unfold heapStart; omega),
      Kg _ (hgl _ (by omega) (by omega)) (by omega)
        (by unfold topAddr binAt avAddr; omega) (by unfold heapStart; omega)⟩
  have Kbb : read64 m' binblocksAddr = read64 m binblocksAddr :=
    Kg _ (fun k hk => .inl ⟨by unfold binblocksAddr avAddr; omega,
      by unfold binblocksAddr avAddr; omega⟩) (by unfold binblocksAddr avAddr; omega)
      (by unfold topAddr binblocksAddr avAddr; omega)
      (by unfold binblocksAddr avAddr heapStart; omega)
  -- the new chunk
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
  refine ⟨⟨{ sbrk_base := ?_, brk := ?_, brk_le := hbrk, top_ptr := htopw
             top_le := by omega, top_size := by omega
             top_header := by
               rw [show brkv - (top + nb) + 1 = brkv - top - nb + 1 by omega]; exact hrem
             top_pad := ?_, max_sbrked := ?_, mallinfo := ?_, first_prev := ?_
             walk := hwalk, coalesced := ?_, footer := ?_
             bins_list := ?_, bins_nodup := hH.bins_nodup
             bin_free := ?_, free_binned := ?_, remainder := hH.remainder
             binblocks_present := by rw [Kbb]; exact hH.binblocks_present
             binblocks := fun bb hbb => hH.binblocks bb (by rw [← Kbb]; exact hbb)
             live := ?_, exact := ?_ }, by omega⟩, hpage,
    fun bb hbb => hbbl bb (by rw [← Kbb]; exact hbb)⟩
  · rw [Kg _ (fun k hk => .inr (.inr (.inl ⟨by unfold sbrkBaseAddr; omega,
      by unfold sbrkBaseAddr; omega⟩))) (by unfold sbrkBaseAddr; omega)
      (by unfold topAddr avAddr sbrkBaseAddr; omega) (by unfold sbrkBaseAddr heapStart; omega)]
    exact hH.sbrk_base
  · rw [Kg _ (fun k hk => .inr (.inr (.inr (.inl ⟨by unfold brkAddr; omega,
      by unfold brkAddr; omega⟩)))) (by unfold brkAddr; omega)
      (by unfold topAddr avAddr brkAddr; omega) (by unfold brkAddr heapStart; omega)]
    exact hH.brk
  · rw [Kg _ (fun k hk => .inr (.inr (.inr (.inl ⟨by unfold topPadAddr; omega,
      by unfold topPadAddr; omega⟩)))) (by unfold topPadAddr; omega)
      (by unfold topAddr avAddr topPadAddr; omega) (by unfold topPadAddr heapStart; omega)]
    exact hH.top_pad
  · rw [Kg _ (fun k hk => .inr (.inr (.inr (.inl ⟨by unfold maxSbrkedAddr; omega,
      by unfold maxSbrkedAddr; omega⟩)))) (by unfold maxSbrkedAddr; omega)
      (by unfold topAddr avAddr maxSbrkedAddr; omega)
      (by unfold maxSbrkedAddr heapStart; omega)]
    exact hH.max_sbrked
  · rw [Kg _ (fun k hk => .inr (.inr (.inr (.inr (.inr ⟨by unfold mallinfoAddr; omega,
      by unfold mallinfoAddr; omega⟩))))) (by unfold mallinfoAddr; omega)
      (by unfold topAddr avAddr mallinfoAddr; omega) (by unfold mallinfoAddr heapStart; omega)]
    exact hH.mallinfo
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
  · intro c hc hf
    have hcm := hinuse c hc hf
    obtain ⟨_, _, hft⟩ := Kf c hcm hf
    rw [hft]; exact hH.footer c hcm hf
  · intro i h0 h1
    obtain ⟨first, hfirst, hchain⟩ := hH.bins_list i h0 h1
    refine ⟨first, by rw [(Kbin i h0 h1).1]; exact hfirst,
      hchain.transport_links (Kbin i h0 h1).2.symm ?_⟩
    intro x hx
    obtain ⟨c, hc, rfl, hf, _⟩ := hH.bin_free i x h0 h1 hx
    exact ⟨(Kf c hc hf).2.1.symm, (Kf c hc hf).1.symm⟩
  · intro i q h0 h1 hq
    obtain ⟨c, hc, h2, h3, h4⟩ := hH.bin_free i q h0 h1 hq
    exact ⟨c, List.mem_append_left _ hc, h2, h3, h4⟩
  · intro c hc hf
    obtain ⟨i, h0, h1, h2, h3⟩ := hH.free_binned c (hinuse c hc hf) hf
    exact ⟨i, h0, h1, h2, h3⟩
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

/-- **The block the top split hands out is fresh**: inside the arena,
16-aligned, and disjoint from every live extent. -/
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
