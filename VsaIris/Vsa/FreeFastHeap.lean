import VsaIris.Vsa.MallocFastHeap

/-!
# Freeing into the top, at the level of the heap shape

`_free_r`'s path for the chunk just below the top, with its predecessor in use
and the merged top below the trim threshold, stores two words:

* the chunk's header, `(size + topsize) | PREV_INUSE`, making it the top;
* `av->top` (`topAddr`): the chunk's address.

`FastAt.merge` proves these stores take the fast heap with the block live to
the fast heap without it, with every credit kept.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap

/-- Split a walk at a list boundary. -/
theorem _root_.Vsa.Sim.DlHeap.ChunkWalk.append_inv {m : Mem} {cs ds : List Chunk} :
    ∀ {p top : Nat}, ChunkWalk m p top (cs ++ ds) →
      ∃ mid, ChunkWalk m p mid cs ∧ ChunkWalk m mid top ds := by
  induction cs with
  | nil => intro p top h; exact ⟨p, .top, h⟩
  | cons c cs ih =>
    intro p top h
    cases h with
    | chunk hh hlow hmin hal hn rest =>
      obtain ⟨mid, h1, h2⟩ := ih rest
      exact ⟨mid, .chunk hh hlow hmin hal hn h1, h2⟩

/-- A one-chunk walk: its chunk starts the walk and ends at the top. -/
theorem _root_.Vsa.Sim.DlHeap.ChunkWalk.single {m : Mem} {p top : Nat} {c : Chunk}
    (h : ChunkWalk m p top [c]) :
    c.addr = p ∧ p + c.size = top ∧ ∃ hh, read64 m (p + 8) = some hh ∧ chunkSize hh = c.size ∧
      hh % 4 < 2 ∧ 32 ≤ c.size ∧ c.size % 16 = 0 := by
  cases h with
  | chunk hh hlow hmin hal hn rest =>
    cases rest with
    | top => exact ⟨rfl, rfl, _, hh, rfl, hlow, hmin, hal⟩

/-- Re-top a walk of in-use chunks: the chunks' headers are unchanged and
the new top header has `PREV_INUSE`. -/
theorem _root_.Vsa.Sim.DlHeap.ChunkWalk.retop {m m' : Mem} {p top : Nat} {cs : List Chunk}
    (h : ChunkWalk m p top cs) (hin : ∀ c ∈ cs, c.inuse = true)
    (hdr : ∀ c ∈ cs, read64 m' (c.addr + 8) = read64 m (c.addr + 8))
    {v : Nat} (hv : read64 m' (top + 8) = some v) (hpi : prevInuse v = true) :
    ChunkWalk m' p top cs := by
  induction h with
  | top => exact .top
  | @chunk p top hh h' cs hh0 hlow hmin hal hn rest ih =>
    have hp : read64 m' (p + 8) = some hh := by rw [hdr _ List.mem_cons_self]; exact hh0
    have ih' := ih (fun c hc => hin c (List.mem_cons_of_mem _ hc))
      (fun c hc => hdr c (List.mem_cons_of_mem _ hc)) hv
    have hflag : prevInuse h' = true := hin _ List.mem_cons_self
    rcases rest.head_or_top with he | ⟨c, hc, hca⟩
    · have w := ChunkWalk.chunk (m := m') hp hlow hmin hal (he ▸ hv) ih'
      rwa [hpi, ← hflag] at w
    · have hn' : read64 m' (p + chunkSize hh + 8) = some h' := by
        rw [← hca, hdr c (List.mem_cons_of_mem _ hc), hca]; exact hn
      exact ChunkWalk.chunk hp hlow hmin hal hn' ih'

/-- The two heap stores of the merge, in program order. -/
def mergeLog (p brkv : Nat) : List WEntry :=
  [(p + 8, 8, BitVec.ofNat 64 (brkv - p + 1)), (topAddr, 8, BitVec.ofNat 64 p)]

/-- The memory after the merge. -/
abbrev mergeMem (m : Mem) (p brkv : Nat) : Mem := writeLog m (mergeLog p brkv)

section MergeReads

variable {m : Mem} {p brkv : Nat}

theorem merge_read_header (hp : heapStart ≤ p) (hv : brkv - p + 1 < 2 ^ 64) :
    read64 (mergeMem m p brkv) (p + 8) = some (brkv - p + 1) := by
  have := read64_of_writeLog_at m (mergeLog p brkv) 0 (p + 8) (BitVec.ofNat 64 (brkv - p + 1))
    rfl (by simp only [mergeLog, List.drop, OutLRange, topAddr, avAddr]; unfold heapStart at hp
            refine ⟨by omega, trivial⟩)
  rwa [ofNat_toNat_lt hv] at this

theorem merge_read_top (hv : p < 2 ^ 64) :
    read64 (mergeMem m p brkv) topAddr = some p := by
  have := read64_of_writeLog_at m (mergeLog p brkv) 1 topAddr (BitVec.ofNat 64 p)
    rfl (by simp only [mergeLog, List.drop, OutLRange])
  rwa [ofNat_toNat_lt hv] at this

/-- Every other word reads as before. -/
theorem merge_read_off {a : Nat} (hg : a + 8 ≤ topAddr ∨ topAddr + 8 ≤ a)
    (hh : a + 8 ≤ p + 8 ∨ p + 16 ≤ a) :
    read64 (mergeMem m p brkv) a = read64 m a :=
  read64_logOut fun k hk => by
    simp only [mergeLog, OutL]
    refine ⟨by omega, by omega, trivial⟩

end MergeReads

/-- **Freeing the chunk below the top preserves the fast heap and every
credit.** `c` is the last chunk, `q = c.addr + 16` its payload, and no other
live block starts at `q`. -/
theorem FastAt.merge {m : Mem} {H : List (Nat × Nat)} {maxReq k top brkv : Nat}
    {cs : List Chunk} {c : Chunk} {bins : Nat → List Nat} {q n : Nat}
    (h : FastAt m ((q, n) :: H) maxReq k top brkv (cs ++ [c]) bins)
    (hq : c.addr + 16 = q) (hH : ∀ e ∈ H, e.1 ≠ q) :
    FastAt (mergeMem m c.addr brkv) H maxReq k c.addr brkv cs bins := by
  have hH0 := h.heap.heap
  obtain ⟨mid, wcs, wc⟩ := hH0.walk.append_inv
  obtain ⟨hca, hctop, hh, Rh, hsz, hlow, hmin, hal⟩ := wc.single
  subst hca
  have hb := wcs.chunk_bounds
  have hle := wcs.le
  have hbrk := hH0.brk_le
  have htsz := hH0.top_size
  have htle := hH0.top_le
  unfold heapStart heapEnd at *
  have Rv : read64 (mergeMem m c.addr brkv) (c.addr + 8) = some (brkv - c.addr + 1) :=
    merge_read_header (by unfold heapStart; omega) (by omega)
  have Rt : read64 (mergeMem m c.addr brkv) topAddr = some c.addr := merge_read_top (by omega)
  have Rg : ∀ a, a + 8 ≤ 0x8001c170 → a + 8 ≤ topAddr ∨ topAddr + 8 ≤ a →
      read64 (mergeMem m c.addr brkv) a = read64 m a := fun a ha hg =>
    merge_read_off hg (by omega)
  have Rc : ∀ c' ∈ cs, read64 (mergeMem m c.addr brkv) (c'.addr + 8) = read64 m (c'.addr + 8) :=
    fun c' hc' => by
      have := hb c' hc'
      exact merge_read_off (by unfold topAddr avAddr; omega) (by omega)
  have inuse' : ∀ c' ∈ cs, c'.inuse = true := fun c' hc' => h.fast.inuse c' (List.mem_append_left _ hc')
  have hbins : ∀ i, 0 < i → i < numBins → BinList (mergeMem m c.addr brkv) i (bins i) := fun i h0 h1 => by
    have hi : i ≤ 127 := by unfold numBins at h1; omega
    obtain ⟨first, hf, hcn⟩ := hH0.bins_list i h0 h1
    rw [h.fast.bins_empty i] at hcn ⊢
    cases hcn with
    | close hbk =>
      refine ⟨binAt i, ?_, BinChain.close ?_⟩
      · rw [Rg _ (by unfold binAt avAddr; omega) (by unfold binAt topAddr avAddr; omega)]
        exact hf
      · rw [Rg _ (by unfold binAt avAddr; omega) (by unfold binAt topAddr avAddr; omega)]
        exact hbk
  have Rbb : read64 (mergeMem m c.addr brkv) binblocksAddr = some 0 := by
    rw [Rg _ (by unfold binblocksAddr avAddr; omega) (by unfold binblocksAddr topAddr avAddr; omega)]
    exact h.fast.binblocks
  have hpi : prevInuse (brkv - c.addr + 1) = true := by
    unfold prevInuse; rw [beq_iff_eq]; omega
  have hwalk : ChunkWalk (mergeMem m c.addr brkv) 0x8001c170 c.addr cs :=
    wcs.retop inuse' Rc Rv hpi
  -- a live block of `H` lies in a chunk of `cs`
  have hin : ∀ e ∈ H, ∃ c' ∈ cs, c'.inuse = true ∧ c'.addr + 16 = e.1 ∧ e.2 + 8 ≤ c'.size := by
    intro e he
    obtain ⟨c', hc', hu, h1, h2⟩ := hH0.exact e (List.mem_cons_of_mem _ he) (List.mem_cons_of_mem _ he)
    rcases List.mem_append.mp hc' with hc' | hc'
    · exact ⟨c', hc', hu, h1, h2⟩
    · simp only [List.mem_singleton] at hc'
      subst hc'
      exact absurd (h1.symm.trans hq) (hH e he)
  refine ⟨⟨{ sbrk_base := ?_, brk := ?_, brk_le := hH0.brk_le, top_ptr := Rt
             top_le := by omega, top_size := by omega
             top_header := Rv
             top_pad := ?_, max_sbrked := ?_, mallinfo := ?_, first_prev := ?_
             walk := hwalk
             coalesced := fun i hi => .inl (inuse' _ (List.getElem_mem (by omega)))
             footer := fun c' hc' hf => by rw [inuse' c' hc'] at hf; cases hf
             bins_list := hbins
             bins_nodup := hH0.bins_nodup
             bin_free := fun i q _ _ hq => by rw [h.fast.bins_empty i] at hq; cases hq
             free_binned := fun c' hc' hf => by rw [inuse' c' hc'] at hf; cases hf
             remainder := by rw [h.fast.bins_empty 1]; exact Nat.zero_le 1
             binblocks_present := by rw [Rbb]; rfl
             binblocks := fun _ _ i _ _ hne => absurd (h.fast.bins_empty i) hne
             live := fun e he => ?_, exact := fun e he _ => hin e he }, by omega⟩,
    ⟨inuse', h.fast.bins_empty, Rbb⟩, ?_⟩
  · rw [Rg _ (by unfold sbrkBaseAddr; omega) (by unfold sbrkBaseAddr topAddr avAddr; omega)]
    exact hH0.sbrk_base
  · rw [Rg _ (by unfold brkAddr; omega) (by unfold brkAddr topAddr avAddr; omega)]
    exact hH0.brk
  · rw [Rg _ (by unfold topPadAddr; omega) (by unfold topPadAddr topAddr avAddr; omega)]
    exact hH0.top_pad
  · rw [Rg _ (by unfold maxSbrkedAddr; omega) (by unfold maxSbrkedAddr topAddr avAddr; omega)]
    exact hH0.max_sbrked
  · rw [Rg _ (by unfold mallinfoAddr; omega) (by unfold mallinfoAddr topAddr avAddr; omega)]
    exact hH0.mallinfo
  · rcases wcs.head_or_top with he | ⟨c', hc', hca⟩
    · rw [show heapStart = c.addr from he, Rv]
      simp only [Option.any, beq_iff_eq]; omega
    · rw [show heapStart = c'.addr from hca.symm, Rc c' hc', hca]
      exact hH0.first_prev
  · obtain ⟨c', hc', hu, h1, h2⟩ := hin e he
    exact ⟨c', hc', hu, by omega, by omega⟩
  · -- every credit kept: the top only grew
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact Reserve.zero _ _ _
    intro _
    obtain ⟨top', bytes, r⟩ := h.reserve hk
    have tp := r.top_pointer
    rw [hH0.top_ptr] at tp
    cases tp
    have sh := r.size_header
    rw [hH0.top_header] at sh
    have hbytes : bytes = brkv - c.addr - c.size := by
      have := Option.some.inj sh; omega
    have hta := r.top_aligned
    have hsa := r.size_aligned
    have hcap := r.capacity
    have hlo := r.arena_lo
    have hhi := r.arena_hi
    try unfold heapStart at hlo
    try unfold heapEnd at hhi
    exact ⟨c.addr, brkv - c.addr,
      { request_fits := r.request_fits
        top_pointer := Rt
        size_header := Rv
        top_aligned := by omega
        size_aligned := by omega
        arena_lo := by unfold heapStart; omega
        arena_hi := by unfold heapEnd; omega
        capacity := by omega
        disjoint := by
          intro e he
          obtain ⟨c', hc', _, h1, h2⟩ := hin e he
          have := hb c' hc'
          left; omega }⟩

end VsaIris.VsaHeap
