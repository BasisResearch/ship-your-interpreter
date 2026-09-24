import VsaIris.Vsa.HeapTake

/-!
# Clearing a block's bit

`_malloc_r`'s block search clears the `binblocks` bit of a block of four bins
it found empty (`0x80004e54`). `BlockHeapAt.transport_read_bb` transports the
shape through memories that agree on everything it reads but the bitmap, with
the bitmap's facts supplied; `PHeapAt.clearBlock` is the clear.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.MallocFast

private theorem rd {H : List (Nat × Nat)} {m m' : Mem}
    (hag : AgreeP (fun a => vsaRead H a ∧ ¬ (binblocksAddr ≤ a ∧ a < binblocksAddr + 8)) m m')
    {a : Nat} (hf : ∀ k, k < 8 → vsaFoot H (a + k)) (hn : NotErr a)
    (hb : a + 8 ≤ binblocksAddr ∨ binblocksAddr + 8 ≤ a) : read64 m a = read64 m' a :=
  read64_agreeP hag fun k hk => ⟨⟨hf k hk, by unfold InRange NotErr at *; omega,
    by unfold InRange NotErr at *; omega⟩, by omega⟩

private theorem gr {H : List (Nat × Nat)} {a : Nat}
    (hg : ∀ k, k < 8 → allocGlobal (a + k)) : ∀ k, k < 8 → vsaFoot H (a + k) :=
  fun k hk => .inl (hg k hk)

theorem BlockHeapAt.transport_read_bb {m m' : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat}
    (h : BlockHeapAt m H top brkv chunks bins)
    (hag : AgreeP (fun a => vsaRead H a ∧ ¬ (binblocksAddr ≤ a ∧ a < binblocksAddr + 8)) m m')
    (hbbp : (read64 m' binblocksAddr).isSome)
    (hbbk : ∀ bb, read64 m' binblocksAddr = some bb →
      ∀ i, 1 < i → i < numBins → bins i ≠ [] → bb / 2 ^ (i / 4) % 2 = 1) :
    BlockHeapAt m' H top brkv chunks bins := by
  have hH := h.heap
  have hlo : heapStart ≤ top := hH.walk.le
  have hcb := hH.walk.chunk_bounds
  have G : ∀ a lo hi, InRange lo hi a → (lo = 0x8001ad10 ∧ hi = 0x8001b520 ∨
      lo = 0x8001b960 ∧ hi = 0x8001b970 ∨ lo = 0x8001b990 ∧ hi = 0x8001b9b0 ∨
      lo = 0x8001ba18 ∧ hi = 0x8001ba68) → allocGlobal a := by
    intro a lo hi hr hlh
    unfold allocGlobal
    rcases hlh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .inl hr
    · exact .inr (.inr (.inl hr))
    · exact .inr (.inr (.inr (.inl hr)))
    · exact .inr (.inr (.inr (.inr (.inr hr))))
  have gAv : ∀ a, 0x8001ad10 ≤ a → a + 8 ≤ 0x8001b520 →
      (a + 8 ≤ binblocksAddr ∨ binblocksAddr + 8 ≤ a) → read64 m a = read64 m' a :=
    fun a h1 h2 h3 => rd hag (gr fun k hk =>
      G _ _ _ ⟨by omega, by omega⟩ (.inl ⟨rfl, rfl⟩)) (.inl (by omega)) h3
  have gSbrk : read64 m sbrkBaseAddr = read64 m' sbrkBaseAddr :=
    rd hag (gr fun k hk =>
      G _ _ _ ⟨by unfold sbrkBaseAddr; omega, by unfold sbrkBaseAddr; omega⟩
        (.inr (.inl ⟨rfl, rfl⟩))) (.inr (.inl (by unfold sbrkBaseAddr; omega)))
      (by unfold sbrkBaseAddr binblocksAddr avAddr; omega)
  have gBrk : ∀ a, 0x8001b990 ≤ a → a + 8 ≤ 0x8001b9b0 → read64 m a = read64 m' a :=
    fun a h1 h2 => rd hag (gr fun k hk =>
      G _ _ _ ⟨by omega, by omega⟩ (.inr (.inr (.inl ⟨rfl, rfl⟩)))) (.inr (.inl (by omega)))
      (by unfold binblocksAddr avAddr; omega)
  have gMi : read64 m mallinfoAddr = read64 m' mallinfoAddr :=
    rd hag (gr fun k hk =>
      G _ _ _ ⟨by unfold mallinfoAddr; omega, by unfold mallinfoAddr; omega⟩
        (.inr (.inr (.inr ⟨rfl, rfl⟩)))) (.inr (.inr (by unfold mallinfoAddr; omega)))
      (by unfold mallinfoAddr binblocksAddr avAddr; omega)
  have gTop : read64 m topAddr = read64 m' topAddr :=
    gAv _ (by unfold topAddr avAddr; omega) (by unfold topAddr avAddr; omega)
      (by unfold topAddr binblocksAddr avAddr; omega)
  have gBrk0 : read64 m brkAddr = read64 m' brkAddr :=
    gBrk _ (by unfold brkAddr; omega) (by unfold brkAddr; omega)
  have gPad : read64 m topPadAddr = read64 m' topPadAddr :=
    gBrk _ (by unfold topPadAddr; omega) (by unfold topPadAddr; omega)
  have gMax : read64 m maxSbrkedAddr = read64 m' maxSbrkedAddr :=
    gBrk _ (by unfold maxSbrkedAddr; omega) (by unfold maxSbrkedAddr; omega)
  have gBin16 : ∀ i, i < numBins → read64 m (binAt i + 16) = read64 m' (binAt i + 16) :=
    fun i hi => gAv _ (by unfold binAt avAddr; omega)
      (by unfold binAt avAddr; unfold numBins at hi; omega) (by unfold binAt binblocksAddr avAddr; omega)
  have gBin24 : ∀ i, i < numBins → read64 m (binAt i + 24) = read64 m' (binAt i + 24) :=
    fun i hi => gAv _ (by unfold binAt avAddr; omega)
      (by unfold binAt avAddr; unfold numBins at hi; omega) (by unfold binAt binblocksAddr avAddr; omega)
  have hdr : ∀ q, (q = top ∨ ∃ c ∈ chunks, c.addr = q) →
      read64 m (q + 8) = read64 m' (q + 8) :=
    fun q hq => rd hag (foot_header h hq) (.inr (.inr (by
      unfold heapStart at hlo
      rcases hq with rfl | ⟨c, hc, rfl⟩
      · omega
      · have := (hcb c hc).1; unfold heapStart at this; omega)))
      (by
        unfold heapStart at hlo; unfold binblocksAddr avAddr
        rcases hq with rfl | ⟨c, hc, rfl⟩
        · omega
        · have := (hcb c hc).1; unfold heapStart at this; omega)
  have hfreeRd : ∀ c ∈ chunks, c.inuse = false →
      read64 m (c.addr + 16) = read64 m' (c.addr + 16) ∧
      read64 m (c.addr + 24) = read64 m' (c.addr + 24) ∧
      read64 m (c.addr + c.size) = read64 m' (c.addr + c.size) := by
    intro c hc hf
    obtain ⟨hl, hft⟩ := foot_free h hc hf
    have hca := (hcb c hc).1
    unfold heapStart at hca
    have hbb : ∀ a, c.addr ≤ a → a + 8 ≤ binblocksAddr ∨ binblocksAddr + 8 ≤ a := by
      unfold binblocksAddr avAddr; omega
    refine ⟨rd hag (fun k hk => hl k (by omega)) (.inr (.inr (by omega))) (hbb _ (by omega)),
      rd hag (fun k hk => ?_) (.inr (.inr (by omega))) (hbb _ (by omega)),
      rd hag hft (.inr (.inr (by omega))) (hbb _ (by omega))⟩
    have := hl (k + 8) (by omega)
    rwa [show c.addr + 16 + (k + 8) = c.addr + 24 + k by omega] at this
  have hstart : read64 m (heapStart + 8) = read64 m' (heapStart + 8) :=
    hdr _ (by
      rcases hH.walk.head_or_top with he | he
      · exact .inl he
      · exact .inr he)
  refine ⟨?_, h.top_room⟩
  exact
    { sbrk_base := gSbrk ▸ hH.sbrk_base
      brk := gBrk0 ▸ hH.brk
      brk_le := hH.brk_le
      top_ptr := gTop ▸ hH.top_ptr
      top_le := hH.top_le
      top_size := hH.top_size
      top_header := hdr top (.inl rfl) ▸ hH.top_header
      top_pad := gPad ▸ hH.top_pad
      max_sbrked := gMax ▸ hH.max_sbrked
      mallinfo := gMi ▸ hH.mallinfo
      first_prev := hstart ▸ hH.first_prev
      walk := hH.walk.transport_headers hdr
      coalesced := hH.coalesced
      footer := fun c hc hf => by
        obtain ⟨_, _, hft⟩ := hfreeRd c hc hf
        exact hft ▸ hH.footer c hc hf
      bins_list := by
        intro i h0 h1
        obtain ⟨first, hfirst, hchain⟩ := hH.bins_list i h0 h1
        refine ⟨first, gBin16 i h1 ▸ hfirst, hchain.transport_links (gBin24 i h1) ?_⟩
        intro x hx
        obtain ⟨c, hc, rfl, hf, _⟩ := hH.bin_free i x h0 h1 hx
        exact ⟨(hfreeRd c hc hf).2.1, (hfreeRd c hc hf).1⟩
      bins_nodup := hH.bins_nodup
      bin_free := hH.bin_free
      free_binned := hH.free_binned
      remainder := hH.remainder
      binblocks_present := hbbp
      binblocks := hbbk
      live := hH.live
      exact := hH.exact }


/-- **Clear an empty block's bit.** When every bin of block `b` is empty, a
bitmap that keeps every other set bit keeps the heap shape. -/
theorem PHeapAt.clearBlock {m m' : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} (h : PHeapAt m H top brkv chunks bins)
    {b bb' : Nat} (hemp : ∀ i, 1 < i → i < numBins → i / 4 = b → bins i = [])
    (hbb' : read64 m' binblocksAddr = some bb')
    (hkeep : ∀ bb, read64 m binblocksAddr = some bb → ∀ t, t ≠ b → bb / 2 ^ t % 2 = 1 →
      bb' / 2 ^ t % 2 = 1) (hlt : bb' < 2 ^ 32)
    (hag : ∀ a, vsaFoot H a → ¬ (binblocksAddr ≤ a ∧ a < binblocksAddr + 8) → m'[a]? = m[a]?) :
    PHeapAt m' H top brkv chunks bins := by
  obtain ⟨B, hpage, _⟩ := h
  have HH := B.heap
  refine ⟨B.transport_read_bb (fun a ha => (hag a ha.1.1 ha.2).symm) (by rw [hbb']; rfl) ?_, hpage,
    fun x hx => by rw [hbb'] at hx; cases hx; exact hlt⟩
  intro bb'' h'' i hi1 hi hne
  rw [hbb'] at h''; cases h''
  have hib : i / 4 ≠ b := fun he => hne (hemp i hi1 hi he)
  obtain ⟨bb, hbb⟩ := Option.isSome_iff_exists.1 HH.binblocks_present
  exact hkeep bb hbb _ hib (HH.binblocks bb hbb i hi1 hi hne)

end VsaIris.VsaHeap
