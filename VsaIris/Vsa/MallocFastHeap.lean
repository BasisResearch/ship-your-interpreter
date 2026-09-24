import VsaIris.Vsa.Malloc
import Vsa.Sim.ValueSpec
import Vsa.Sim.EnvNewSpec
import Vsa.Sim.InterpSpillReads

/-!
# The top split, at the level of the heap shape

`_malloc_r`'s fast path for a request of chunk size `nb` from a heap with no
free chunk and a clear `binblocks` bitmap splits the top chunk. It stores three
words:

* `top + 8`: the victim's header `nb | PREV_INUSE`;
* `av->top` (`topAddr`): the new top `top + nb`;
* `top + nb + 8`: the remainder's header `(size - nb) | PREV_INUSE`.

It returns `top + 16`. `FastAt` is the heap shape at the fast path's entry:
`BlockHeapAt`, every chunk in use, every bin empty, `binblocks` zero, and
the corrected reserve (`Reserve`) for `k` credits. `FastAt.split` proves the three stores
take `FastAt … (k + 1)` to `FastAt … k` with the new block live. This is the
heap half of `MallocRoomRun` on the fast path; the machine half is the
reflected segments in `MallocFastSegs.lean`.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap

/-- The fast path's restriction: no free chunk, no bin in use, and a clear
`binblocks` bitmap (dlmalloc clears bits lazily, so empty bins alone do not
imply it). -/
structure FastHeap (m : Mem) (chunks : List Chunk) (bins : Nat → List Nat) : Prop where
  inuse : ∀ c ∈ chunks, c.inuse = true
  bins_empty : ∀ i, bins i = []
  binblocks : read64 m binblocksAddr = some 0

/-- The heap at the fast path's entry, with `k` credits. -/
structure FastAt (m : Mem) (H : List (Nat × Nat)) (maxReq k top brkv : Nat)
    (chunks : List Chunk) (bins : Nat → List Nat) : Prop where
  heap : BlockHeapAt m H top brkv chunks bins
  fast : FastHeap m chunks bins
  reserve : Reserve m H maxReq k

/-- The three heap stores of the top split, in program order. -/
def splitLog (top nb rem : Nat) : List WEntry :=
  [(top + 8, 8, BitVec.ofNat 64 (nb + 1)), (topAddr, 8, BitVec.ofNat 64 (top + nb)),
   (top + nb + 8, 8, BitVec.ofNat 64 (rem + 1))]

theorem read64_logOut {m : Mem} {w : List WEntry} {a : Nat}
    (h : ∀ k, k < 8 → OutL w (a + k)) : read64 (writeLog m w) a = read64 m a :=
  (read64_agreeP (P := OutL w) (fun k hk => (writeLog_out m w k hk).symm) h).symm

theorem ofNat_toNat_lt {x : Nat} (h : x < 2 ^ 64) : (BitVec.ofNat 64 x).toNat = x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

section Split

variable {m : Mem} {H : List (Nat × Nat)} {maxReq k top brkv : Nat} {chunks : List Chunk}
  {bins : Nat → List Nat}

/-- The entry facts the fast path's code reads, named. -/
structure FastReads (m : Mem) (top brkv : Nat) : Prop where
  top_ptr : read64 m topAddr = some top
  top_header : read64 m (top + 8) = some (brkv - top + 1)
  binblocks : read64 m binblocksAddr = some 0
  bin_fd : ∀ i, 0 < i → i < numBins → read64 m (binAt i + 16) = some (binAt i)
  bin_bk : ∀ i, 0 < i → i < numBins → read64 m (binAt i + 24) = some (binAt i)
  top_lo : heapStart ≤ top
  top_align : top % 16 = 0
  brk_le : brkv ≤ heapEnd

theorem FastAt.reads (h : FastAt m H maxReq k top brkv chunks bins) (hk : 0 < k) :
    FastReads m top brkv where
  top_ptr := h.heap.heap.top_ptr
  top_header := h.heap.heap.top_header
  binblocks := h.fast.binblocks
  bin_fd := fun i h0 h1 => by
    obtain ⟨first, hf, hc⟩ := h.heap.heap.bins_list i h0 h1
    rw [h.fast.bins_empty i] at hc
    cases hc with
    | close _ => exact hf
  bin_bk := fun i h0 h1 => by
    obtain ⟨first, hf, hc⟩ := h.heap.heap.bins_list i h0 h1
    rw [h.fast.bins_empty i] at hc
    cases hc with
    | close hb => exact hb
  top_lo := h.heap.heap.walk.le
  top_align := by
    obtain ⟨top', bytes, r⟩ := h.reserve hk
    have := r.top_pointer
    have e : top' = top := by
      rw [h.heap.heap.top_ptr] at this; exact (Option.some.inj this).symm
    subst e
    exact r.top_aligned
  brk_le := h.heap.heap.brk_le

/-- The reserve's top chunk is the heap's top chunk. -/
theorem FastAt.reserve_top (h : FastAt m H maxReq k top brkv chunks bins) (hk : 0 < k) :
    ∃ bytes, TopReserve m H maxReq k top bytes ∧ bytes = brkv - top := by
  obtain ⟨top', bytes, r⟩ := h.reserve hk
  have tp := r.top_pointer
  rw [h.heap.heap.top_ptr] at tp
  cases tp
  have sh := r.size_header
  rw [h.heap.heap.top_header] at sh
  have hb : bytes = brkv - top := by
    have := Option.some.inj sh; omega
  exact ⟨bytes, r, hb⟩

end Split

/-- Extend a walk at its top: the old chunks' headers are unchanged, the
top's header keeps its `PREV_INUSE` bit, and a new walk continues from the
old top. -/
theorem _root_.Vsa.Sim.DlHeap.ChunkWalk.extend {m m' : Mem} {p top top' : Nat}
    {cs ds : List Chunk} (h : ChunkWalk m p top cs)
    (hdr : ∀ c ∈ cs, read64 (m') (c.addr + 8) = read64 m (c.addr + 8))
    (htop : ∀ h1, read64 m (top + 8) = some h1 →
      ∃ h2, read64 (m') (top + 8) = some h2 ∧ prevInuse h2 = prevInuse h1)
    (hds : ChunkWalk (m') top top' ds) : ChunkWalk (m') p top' (cs ++ ds) := by
  induction h with
  | top => exact hds
  | @chunk p top hh h' cs hh0 hlow hmin hal hn rest ih =>
    have hp : read64 (m') (p + 8) = some hh := by
      rw [hdr _ List.mem_cons_self]; exact hh0
    have ih' := ih (fun c hc => hdr c (List.mem_cons_of_mem _ hc)) htop hds
    rcases rest.head_or_top with he | ⟨c, hc, hca⟩
    · obtain ⟨h2, hr2, hpi⟩ := htop h' (he ▸ hn)
      have w := ChunkWalk.chunk (m := m') hp hlow hmin hal (he ▸ hr2) ih'
      rw [hpi] at w
      exact w
    · have hn' : read64 (m') (p + chunkSize hh + 8) = some h' := by
        rw [← hca, hdr c (List.mem_cons_of_mem _ hc), hca]; exact hn
      exact ChunkWalk.chunk hp hlow hmin hal hn' ih'

section SplitReads

variable {m : Mem} {top nb rem : Nat}

theorem split_read_victim (htop : heapStart ≤ top) (hnb : 32 ≤ nb) (hv : nb + 1 < 2 ^ 64) :
    read64 (writeLog m (splitLog top nb rem)) (top + 8) = some (nb + 1) := by
  have := read64_of_writeLog_at m (splitLog top nb rem) 0 (top + 8) (BitVec.ofNat 64 (nb + 1))
    rfl (by simp only [splitLog, List.drop, OutLRange, topAddr, avAddr]; unfold heapStart at htop
            refine ⟨by omega, by omega, trivial⟩)
  rwa [ofNat_toNat_lt hv] at this

theorem split_read_top (htop : heapStart ≤ top) (hv : top + nb < 2 ^ 64) :
    read64 (writeLog m (splitLog top nb rem)) topAddr = some (top + nb) := by
  have := read64_of_writeLog_at m (splitLog top nb rem) 1 topAddr (BitVec.ofNat 64 (top + nb))
    rfl (by simp only [splitLog, List.drop, OutLRange, topAddr, avAddr]; unfold heapStart at htop
            refine ⟨by omega, trivial⟩)
  rwa [ofNat_toNat_lt hv] at this

theorem split_read_rem (hv : rem + 1 < 2 ^ 64) :
    read64 (writeLog m (splitLog top nb rem)) (top + nb + 8) = some (rem + 1) := by
  have := read64_of_writeLog_at m (splitLog top nb rem) 2 (top + nb + 8)
    (BitVec.ofNat 64 (rem + 1)) rfl (by simp only [splitLog, List.drop, OutLRange])
  rwa [ofNat_toNat_lt hv] at this

/-- Every other word reads as before. -/
theorem split_read_off {a : Nat} (hg : a + 8 ≤ topAddr ∨ topAddr + 8 ≤ a)
    (hv : a + 8 ≤ top + 8 ∨ top + 16 ≤ a) (hr : a + 8 ≤ top + nb + 8 ∨ top + nb + 16 ≤ a) :
    read64 (writeLog m (splitLog top nb rem)) a = read64 m a :=
  read64_logOut fun k hk => by
    simp only [splitLog, OutL]
    refine ⟨by omega, by omega, by omega, trivial⟩

end SplitReads

/-- The memory after the top split. -/
abbrev splitMem (m : Mem) (top nb brkv : Nat) : Mem :=
  writeLog m (splitLog top nb (brkv - top - nb))

/-- **The top split preserves the fast heap, spending one credit.** -/
theorem FastAt.split {m : Mem} {H : List (Nat × Nat)} {maxReq k top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat}
    (h : FastAt m H maxReq (k + 1) top brkv chunks bins) {nb n : Nat}
    (hnb16 : nb % 16 = 0) (hnb32 : 32 ≤ nb) (hnbP : nb ≤ physSize maxReq)
    (hn8 : n + 8 ≤ nb) :
    FastAt (splitMem m top nb brkv) ((top + 16, n) :: H) maxReq k
      (top + nb) brkv (chunks ++ [⟨top, nb, true⟩]) bins := by
  obtain ⟨bytes, r, hbytes⟩ := h.reserve_top (Nat.succ_pos k)
  have R := h.reads (Nat.succ_pos k)
  have hH := h.heap.heap
  have hP := physSize_min maxReq
  have hcap := r.capacity
  have hk1 : physSize maxReq ≤ (k + 1) * physSize maxReq :=
    Nat.le_mul_of_pos_left _ (Nat.succ_pos k)
  have hsucc0 : (k + 1) * physSize maxReq = k * physSize maxReq + physSize maxReq :=
    Nat.succ_mul k (physSize maxReq)
  have hrem : physSize maxReq + 32 ≤ bytes := by omega
  have harena : heapStart ≤ top ∧ top + bytes ≤ heapEnd := ⟨r.arena_lo, r.arena_hi⟩
  have hsz := r.size_aligned
  have htsz := hH.top_size
  have hbrk := R.brk_le
  have htlo := R.top_lo
  unfold heapStart heapEnd at *
  -- the numbers
  have hroom : nb + 32 ≤ brkv - top := by omega
  have Rv : read64 (splitMem m top nb brkv) (top + 8) = some (nb + 1) :=
    split_read_victim (by unfold heapStart; omega) hnb32 (by omega)
  have Rt : read64 (splitMem m top nb brkv) topAddr = some (top + nb) := split_read_top (by unfold heapStart; omega) (by omega)
  have Rr : read64 (splitMem m top nb brkv) (top + nb + 8) = some (brkv - top - nb + 1) := split_read_rem (by omega)
  have Rg : ∀ a, a + 8 ≤ 0x8001c170 → a + 8 ≤ topAddr ∨ topAddr + 8 ≤ a →
      read64 (splitMem m top nb brkv) a = read64 m a := fun a ha hg =>
    split_read_off hg (by omega) (by omega)
  have hb := hH.walk.chunk_bounds
  have Rc : ∀ c ∈ chunks, read64 (splitMem m top nb brkv) (c.addr + 8) = read64 m (c.addr + 8) := fun c hc => by
    have := hb c hc
    unfold heapStart at this
    exact split_read_off (by unfold topAddr avAddr; omega) (by omega) (by omega)
  have inuse' : ∀ c ∈ chunks ++ [⟨top, nb, true⟩], c.inuse = true := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h.fast.inuse c hc
    · simp at hc; subst hc; rfl
  have hbins : ∀ i, 0 < i → i < numBins → BinList (splitMem m top nb brkv) i (bins i) := fun i h0 h1 => by
    have hi : i ≤ 127 := by unfold numBins at h1; omega
    rw [h.fast.bins_empty i]
    refine ⟨binAt i, ?_, BinChain.close ?_⟩
    · rw [Rg _ (by unfold binAt avAddr; omega) (by unfold binAt topAddr avAddr; omega)]
      exact R.bin_fd i h0 h1
    · rw [Rg _ (by unfold binAt avAddr; omega) (by unfold binAt topAddr avAddr; omega)]
      exact R.bin_bk i h0 h1
  have Rbb : read64 (splitMem m top nb brkv) binblocksAddr = some 0 := by
    rw [Rg _ (by unfold binblocksAddr avAddr; omega) (by unfold binblocksAddr topAddr avAddr; omega)]
    exact R.binblocks
  have hnew : ChunkWalk (splitMem m top nb brkv) top (top + nb) [⟨top, nb, true⟩] := by
    have hcs : chunkSize (nb + 1) = nb := by unfold chunkSize; omega
    have hpi : prevInuse (brkv - top - nb + 1) = true := by
      unfold prevInuse; rw [beq_iff_eq]; omega
    have w := ChunkWalk.chunk (m := splitMem m top nb brkv) (top := top + nb) (cs := []) (h := nb + 1)
      (h' := brkv - top - nb + 1) Rv (by omega) (by rw [hcs]; omega) (by rw [hcs]; omega)
      (by rw [hcs]; exact Rr) (by rw [hcs]; exact .top)
    rwa [hcs, hpi] at w
  have hwalk : ChunkWalk (splitMem m top nb brkv) 0x8001c170 (top + nb) (chunks ++ [⟨top, nb, true⟩]) := by
    refine hH.walk.extend Rc (fun h1 hh1 => ⟨nb + 1, Rv, ?_⟩) hnew
    rw [hH.top_header] at hh1
    cases hh1
    unfold prevInuse
    rw [show (nb + 1) % 2 = 1 by omega, show (brkv - top + 1) % 2 = 1 by omega]
  refine ⟨⟨{ sbrk_base := ?_, brk := ?_, brk_le := hH.brk_le, top_ptr := Rt
             top_le := by omega, top_size := by omega
             top_header := by rw [show brkv - (top + nb) + 1 = brkv - top - nb + 1 by omega]; exact Rr
             top_pad := ?_, max_sbrked := ?_, mallinfo := ?_, first_prev := ?_
             walk := hwalk
             coalesced := fun i hi => .inl (inuse' _ (List.getElem_mem (by omega)))
             footer := fun c hc hf => by rw [inuse' c hc] at hf; cases hf
             bins_list := hbins
             bins_nodup := hH.bins_nodup
             bin_free := fun i q _ _ hq => by rw [h.fast.bins_empty i] at hq; cases hq
             free_binned := fun c hc hf => by rw [inuse' c hc] at hf; cases hf
             remainder := by rw [h.fast.bins_empty 1]; exact Nat.zero_le 1
             binblocks_present := by rw [Rbb]; rfl
             binblocks := fun _ _ i _ _ hne => absurd (h.fast.bins_empty i) hne
             live := ?_, exact := ?_ }, by omega⟩,
    ⟨inuse', h.fast.bins_empty, Rbb⟩, ?_⟩
  · rw [Rg _ (by unfold sbrkBaseAddr; omega) (by unfold sbrkBaseAddr topAddr avAddr; omega)]
    exact hH.sbrk_base
  · rw [Rg _ (by unfold brkAddr; omega) (by unfold brkAddr topAddr avAddr; omega)]
    exact hH.brk
  · rw [Rg _ (by unfold topPadAddr; omega) (by unfold topPadAddr topAddr avAddr; omega)]
    exact hH.top_pad
  · rw [Rg _ (by unfold maxSbrkedAddr; omega) (by unfold maxSbrkedAddr topAddr avAddr; omega)]
    exact hH.max_sbrked
  · rw [Rg _ (by unfold mallinfoAddr; omega) (by unfold mallinfoAddr topAddr avAddr; omega)]
    exact hH.mallinfo
  · rcases hH.walk.head_or_top with he | ⟨c, hc, hca⟩
    · rw [show heapStart = top from he, Rv]
      simp only [Option.any, beq_iff_eq]; omega
    · rw [show heapStart = c.addr from hca.symm, Rc c hc, hca]
      exact hH.first_prev
  · intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨⟨top, nb, true⟩, List.mem_append_right _ List.mem_cons_self, rfl,
        by simp, by simp; omega⟩
    · obtain ⟨c, hc, hu, h1, h2⟩ := hH.live e he
      exact ⟨c, List.mem_append_left _ hc, hu, h1, h2⟩
  · intro e he _
    rcases List.mem_cons.mp he with rfl | he'
    · exact ⟨⟨top, nb, true⟩, List.mem_append_right _ List.mem_cons_self, rfl, rfl, by simp; omega⟩
    · obtain ⟨c, hc, hu, h1, h2⟩ := hH.exact e he' he'
      exact ⟨c, List.mem_append_left _ hc, hu, h1, h2⟩
  · -- the reserve with one credit spent
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact Reserve.zero _ _ _
    intro _
    have hkP : physSize maxReq ≤ k * physSize maxReq := Nat.le_mul_of_pos_left _ hk
    exact ⟨top + nb, brkv - top - nb,
      { request_fits := r.request_fits
        top_pointer := Rt
        size_header := Rr
        top_aligned := by have := r.top_aligned; omega
        size_aligned := by omega
        arena_lo := by unfold heapStart; omega
        arena_hi := by unfold heapEnd; omega
        capacity := by omega
        disjoint := by
          intro e he
          rcases List.mem_cons.mp he with rfl | he
          · left; simp only; omega
          · rcases r.disjoint e he with d | d
            · left; omega
            · right; omega }⟩

/-- On the fast path itself: after the top split for `malloc(24)` (a 32-byte
chunk), VSA's `AllocationReserve` over the ledger with the returned block is
false for every positive credit count, while the corrected `Reserve` is
preserved by `FastAt.split`. -/
theorem split24_vsa_reserve_false {m : Mem} {H : List (Nat × Nat)} {top brkv maxReq k : Nat}
    (htop : heapStart ≤ top) (hhi : top + 32 ≤ heapEnd) (hk : 0 < k) :
    ¬ AllocationReserve vsaArena (splitMem m top 32 brkv) ((top + 16, 24) :: H) maxReq k := by
  have Rt : read64 (splitMem m top 32 brkv) topAddr = some (top + 32) :=
    split_read_top htop (by unfold heapEnd at hhi; omega)
  exact vsa_reserve_fails_after_split vsaArena _ H maxReq k top hk Rt

end VsaIris.VsaHeap
