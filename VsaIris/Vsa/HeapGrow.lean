import VsaIris.Vsa.HeapSplit

/-!
# Growing the top in place

`malloc_extend_top` (`_malloc_r`, `0x80004a48`) asks `sbrk` for more memory.
From a page-aligned, contiguous break the new memory starts exactly at the old
break, so the top chunk grows in place (`0x80004f70`): `brk.0` advances, the
top's header records the larger size, and the statistics words
(`__malloc_current_mallinfo`, `__malloc_max_sbrked_mem`,
`__malloc_max_total_mem`) and `errno` change. The walk, the bins and every
chunk below the top are untouched.

`PHeapAt.topGrow` proves the page-aligned heap at the larger break. The
post-state's reads are taken abstractly, as `PHeapAt.topSplit` takes them, so
the caller supplies them from its own store chain.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.MallocFast

/-- The words an in-place top growth writes: the top's header, `brk.0` with
the two high-water marks after it, the `mallinfo` arena word, and the two
error words `sbrk` may set. -/
def GrowW (top : Nat) (a : Nat) : Prop :=
  (top + 8 ≤ a ∧ a < top + 16) ∨ (brkAddr ≤ a ∧ a < topPadAddr) ∨
    (mallinfoAddr ≤ a ∧ a < mallinfoAddr + 8) ∨ (0x8001ba08 ≤ a ∧ a < 0x8001ba0c) ∨
    (0x8001b538 ≤ a ∧ a < 0x8001b53c)

/-- An aligned footprint word below the top's header, or a global the growth
does not write, is kept. -/
theorem grow_keep {m m' : Mem} {H : List (Nat × Nat)} {top a : Nat}
    (hag : ∀ b, vsaFoot H b → ¬ GrowW top b → m'[b]? = m[b]?)
    (hfoot : ∀ k, k < 8 → vsaFoot H (a + k)) (hw : ∀ k, k < 8 → ¬ GrowW top (a + k)) :
    read64 m' a = read64 m a :=
  read64_keep fun k hk => hag _ (hfoot k hk) (hw k hk)

/-- **The top resized in place.** Another page-aligned break within the arena
leaving the top its header, with the top's header recording the new size and
the statistics words present, gives the page-aligned heap at the new break. -/
theorem PHeapAt.topResize {m m' : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} (h : PHeapAt m H top brkv chunks bins)
    {brk' : Nat} (htr : top + 16 ≤ brk') (hend : brk' ≤ heapEnd) (hpage : brk' % 4096 = 0)
    (hbrk : read64 m' brkAddr = some brk')
    (htop : read64 m' (top + 8) = some (brk' - top + 1))
    (hmi : (read64 m' mallinfoAddr).isSome) (hmax : (read64 m' maxSbrkedAddr).isSome)
    (hag : ∀ a, vsaFoot H a → ¬ GrowW top a → m'[a]? = m[a]?) :
    PHeapAt m' H top brk' chunks bins := by
  obtain ⟨B, _, hbbl⟩ := h
  have hH := B.heap
  have hlo := hH.walk.le
  have hcb := hH.walk.chunk_bounds
  have hbrk0 := hH.brk_le
  have htle := hH.top_le
  obtain ⟨hal, htop16⟩ := hH.aligned
  unfold heapStart at hlo
  -- every allocator global the growth does not write is kept
  have Kg : ∀ a, (∀ k, k < 8 → allocGlobal (a + k)) → (a + 8 ≤ brkAddr ∨ topPadAddr ≤ a) →
      (a + 8 ≤ mallinfoAddr ∨ mallinfoAddr + 8 ≤ a) → a + 8 ≤ 0x8001ba08 ∨ 0x8001ba0c ≤ a →
      a + 8 ≤ 0x8001b538 ∨ 0x8001b53c ≤ a →
      a + 8 ≤ heapStart → read64 m' a = read64 m a := by
    intro a hg h1 h2 h3 h4 hs
    unfold heapStart at hs
    exact grow_keep hag (fun k hk => .inl (hg k hk)) fun k hk => by
      unfold GrowW brkAddr topPadAddr mallinfoAddr at *; omega
  -- every arena word below the top's header is kept
  have Ka : ∀ a, (∀ k, k < 8 → vsaFoot H (a + k)) → 0x8001c170 ≤ a → a + 8 ≤ top + 8 →
      read64 m' a = read64 m a := by
    intro a hf h1 h2
    exact grow_keep hag hf fun k hk => by
      unfold GrowW brkAddr topPadAddr mallinfoAddr; omega
  have Kc : ∀ c ∈ chunks, read64 m' (c.addr + 8) = read64 m (c.addr + 8) := by
    intro c hc
    have hb := hcb c hc
    exact Ka _ (foot_header B (.inr ⟨c, hc, rfl⟩)) (by unfold heapStart at hb; omega) (by omega)
  have Kf : ∀ c ∈ chunks, c.inuse = false →
      read64 m' (c.addr + 16) = read64 m (c.addr + 16) ∧
      read64 m' (c.addr + 24) = read64 m (c.addr + 24) ∧
      read64 m' (c.addr + c.size) = read64 m (c.addr + c.size) := by
    intro c hc hf
    obtain ⟨hl, hft⟩ := foot_free B hc hf
    have hb := hcb c hc
    unfold heapStart at hb
    refine ⟨Ka _ (fun k hk => hl k (by omega)) (by omega) (by omega),
      Ka _ (fun k hk => ?_) (by omega) (by omega), Ka _ hft (by omega) (by omega)⟩
    have := hl (k + 8) (by omega)
    rwa [show c.addr + 16 + (k + 8) = c.addr + 24 + k by omega] at this
  have Kbin : ∀ i, 0 < i → i < numBins →
      read64 m' (binAt i + 16) = read64 m (binAt i + 16) ∧
      read64 m' (binAt i + 24) = read64 m (binAt i + 24) := by
    intro i _ h1
    have hg := binAt_geo i h1
    have hgl : ∀ x, binAt i ≤ x → x + 8 ≤ binAt i + 32 → ∀ k, k < 8 → allocGlobal (x + k) :=
      fun x h2 h3 k hk => .inl ⟨by omega, by omega⟩
    exact ⟨Kg _ (hgl _ (by omega) (by omega)) (by unfold brkAddr; omega)
        (by unfold mallinfoAddr; omega) (by omega) (by omega) (by unfold heapStart; omega),
      Kg _ (hgl _ (by omega) (by omega)) (by unfold brkAddr; omega)
        (by unfold mallinfoAddr; omega) (by omega) (by omega) (by unfold heapStart; omega)⟩
  have Kav : ∀ a, 0x8001ad10 ≤ a → a + 8 ≤ 0x8001b520 → read64 m' a = read64 m a :=
    fun a h1 h2 => Kg _ (fun k hk => .inl ⟨by omega, by omega⟩) (by unfold brkAddr; omega)
      (by unfold mallinfoAddr; omega) (by omega) (by omega) (by unfold heapStart; omega)
  have Kbb : read64 m' binblocksAddr = read64 m binblocksAddr :=
    Kav _ (by unfold binblocksAddr avAddr; omega) (by unfold binblocksAddr avAddr; omega)
  have hpi : ∀ h1, read64 m (top + 8) = some h1 →
      ∃ h2, read64 m' (top + 8) = some h2 ∧ prevInuse h2 = prevInuse h1 := by
    intro h1 hh1
    rw [hH.top_header] at hh1
    cases hh1
    refine ⟨_, htop, ?_⟩
    have := hH.top_size
    unfold prevInuse
    rw [show (brk' - top + 1) % 2 = 1 by omega, show (brkv - top + 1) % 2 = 1 by omega]
  have hwalk : ChunkWalk m' heapStart top chunks := by
    have w := hH.walk.extend (m' := m') Kc hpi (.top (p := top))
    rwa [List.append_nil] at w
  refine ⟨⟨{ sbrk_base := ?_, brk := hbrk, brk_le := hend
             top_ptr := by
               rw [Kav _ (by unfold topAddr avAddr; omega) (by unfold topAddr avAddr; omega)]
               exact hH.top_ptr
             top_le := by omega, top_size := by omega, top_header := htop
             top_pad := ?_, max_sbrked := hmax, mallinfo := hmi, first_prev := ?_
             walk := hwalk, coalesced := hH.coalesced
             footer := fun c hc hf => by rw [(Kf c hc hf).2.2]; exact hH.footer c hc hf
             bins_list := ?_, bins_nodup := hH.bins_nodup
             bin_free := hH.bin_free, free_binned := hH.free_binned, remainder := hH.remainder
             binblocks_present := by rw [Kbb]; exact hH.binblocks_present
             binblocks := fun bb hbb => hH.binblocks bb (by rw [← Kbb]; exact hbb)
             live := hH.live, exact := hH.exact }, by have := B.top_room; omega⟩, hpage,
    fun bb hbb => hbbl bb (by rw [← Kbb]; exact hbb)⟩
  · rw [Kg _ (fun k hk => .inr (.inr (.inl ⟨by unfold sbrkBaseAddr; omega,
      by unfold sbrkBaseAddr; omega⟩))) (by unfold sbrkBaseAddr brkAddr; omega)
      (by unfold sbrkBaseAddr mallinfoAddr; omega) (by unfold sbrkBaseAddr; omega)
      (by unfold sbrkBaseAddr; omega) (by unfold sbrkBaseAddr heapStart; omega)]
    exact hH.sbrk_base
  · rw [Kg _ (fun k hk => .inr (.inr (.inr (.inl ⟨by unfold topPadAddr; omega,
      by unfold topPadAddr; omega⟩)))) (by unfold topPadAddr; omega)
      (by unfold topPadAddr mallinfoAddr; omega) (by unfold topPadAddr; omega)
      (by unfold topPadAddr; omega) (by unfold topPadAddr heapStart; omega)]
    exact hH.top_pad
  · rcases hH.walk.head_or_top with he | ⟨c, hc, hca⟩
    · rw [show heapStart = top from he, htop]
      simp only [Option.any, beq_iff_eq]
      have := hH.top_size
      omega
    · rw [show heapStart = c.addr from hca.symm, Kc c hc, hca]
      exact hH.first_prev
  · intro i h0 h1
    obtain ⟨first, hfirst, hchain⟩ := hH.bins_list i h0 h1
    refine ⟨first, by rw [(Kbin i h0 h1).1]; exact hfirst,
      hchain.transport_links (Kbin i h0 h1).2.symm ?_⟩
    intro x hx
    obtain ⟨c, hc, rfl, hf, _⟩ := hH.bin_free i x h0 h1 hx
    exact ⟨(Kf c hc hf).2.1.symm, (Kf c hc hf).1.symm⟩

/-- **The top grows in place**: `topResize` at a larger break. -/
theorem PHeapAt.topGrow {m m' : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} (h : PHeapAt m H top brkv chunks bins)
    {brk' : Nat} (hle : brkv ≤ brk') (hend : brk' ≤ heapEnd) (hpage : brk' % 4096 = 0)
    (hbrk : read64 m' brkAddr = some brk')
    (htop : read64 m' (top + 8) = some (brk' - top + 1))
    (hmi : (read64 m' mallinfoAddr).isSome) (hmax : (read64 m' maxSbrkedAddr).isSome)
    (hag : ∀ a, vsaFoot H a → ¬ GrowW top a → m'[a]? = m[a]?) :
    PHeapAt m' H top brk' chunks bins :=
  h.topResize (by have := h.heap.top_room; omega) hend hpage hbrk htop hmi hmax hag

end VsaIris.VsaHeap
