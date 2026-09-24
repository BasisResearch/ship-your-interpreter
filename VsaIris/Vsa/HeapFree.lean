import VsaIris.Vsa.HeapCarve
import VsaIris.Vsa.HeapMoveAt

/-!
# The heap edits of `_free_r`

`_free_r` releases the chunk below its argument, coalescing it with a free
neighbour on either side, and either links the result into a bin or merges it
into the top. The edits compose through virtual intermediate memories, each a
page-aligned heap:

* `PHeapAt.drop`: a live block leaves the list.
* `PHeapAt.unlink`: a free chunk leaves its bin and is marked in use
  (`PHeapAt.take` without a block).
* `PHeapAt.absorb`: an in-use chunk absorbs the in-use chunk after it.
* `PHeapAt.toTop`: the in-use chunk below the top becomes the top.
* `PHeapAt.release`: an in-use chunk becomes free and joins a bin.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.MallocFast

/-- **A live block leaves the list.** -/
theorem PHeapAt.drop {m : Mem} {e : Nat × Nat} {H : List (Nat × Nat)} {top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} (h : PHeapAt m (e :: H) top brkv chunks bins) :
    PHeapAt m H top brkv chunks bins :=
  ⟨⟨{ h.heap.heap with
      live := fun e' he' => h.heap.heap.live e' (List.mem_cons_of_mem _ he')
      exact := fun e' he' _ => h.heap.heap.exact e' (List.mem_cons_of_mem _ he')
        (List.mem_cons_of_mem _ he') }, h.heap.top_room⟩, h.brk_page, h.bb_lt⟩

/-- **Unlink a free chunk.** `PHeapAt.take` without handing out a block: `v`
leaves bin `i` and the next header's `PREV_INUSE` marks it in use. -/
theorem PHeapAt.unlink {m m' : Mem} {H : List (Nat × Nat)} {top brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} (h : PHeapAt m H top brkv chunks bins)
    {i : Nat} (hi0 : 0 < i) (hi : i < numBins) {pre post : List Nat} {v : Nat}
    (hbin : bins i = pre ++ v :: post)
    {c : Chunk} (hc : c ∈ chunks) (hcv : c.addr = v)
    {pred succ : Nat} (hpred : (binAt i :: pre).getLast? = some pred)
    (hsucc : (post ++ [binAt i]).head? = some succ)
    (hfd : fdOf m' pred = some succ) (hbk : bkOf m' succ = some pred)
    {hd' : Nat} (hhdr : read64 m' (v + c.size + 8) = some hd')
    (hsz : ∀ hd, read64 m (v + c.size + 8) = some hd → chunkSize hd' = chunkSize hd ∧ hd' % 4 < 2)
    (hpi : prevInuse hd' = true)
    (hag : ∀ a, vsaFoot H a → ¬ TakeW pred succ (v + c.size) a → m'[a]? = m[a]?) :
    PHeapAt m' H top brkv (chunks.map (reflag (v + c.size) true)) (updBins bins i (pre ++ post)) :=
  (h.take hi0 hi hbin hc hcv (n := 0) (by have := (h.heap.heap.walk.chunk_bounds c hc).2.2; omega)
    hpred hsucc hfd hbk hhdr hsz hpi hag).drop

/-- Merging two adjacent chunks into an in-use one keeps coalescing. -/
theorem coal_merge {X Y M : Chunk} (hM : M.inuse = true) :
    ∀ {cs₁ cs₂ : List Chunk}, Coal (cs₁ ++ X :: Y :: cs₂) → Coal (cs₁ ++ M :: cs₂)
  | [], [], _ => by simpa using coal_single M
  | [], d :: cs₂, h => by
    simp only [List.nil_append] at h ⊢
    exact coal_cons_cons.2 ⟨.inl hM, (coal_cons_cons.1 (coal_cons_cons.1 h).2).2⟩
  | [z], cs₂, h => by
    simp only [List.cons_append, List.nil_append] at h ⊢
    exact coal_cons_cons.2 ⟨.inr hM, coal_merge hM (cs₁ := []) (coal_cons_cons.1 h).2⟩
  | z :: w :: cs₁, cs₂, h => by
    simp only [List.cons_append] at h ⊢
    exact coal_cons_cons.2 ⟨(coal_cons_cons.1 h).1, coal_merge hM (cs₁ := w :: cs₁) (coal_cons_cons.1 h).2⟩

/-- **An in-use chunk absorbs the next one.** The in-use chunk `x` of size `a`
and the in-use chunk after it, of size `b`, become one in-use chunk of size
`a + b`: `x`'s header records the size with its `PREV_INUSE` kept, and the
absorbed header may change. No live block starts in the absorbed chunk
(`hno`). -/
theorem PHeapAt.absorb {m m' : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {cs₁ cs₂ : List Chunk} {bins : Nat → List Nat} {x a b : Nat}
    (h : PHeapAt m H top brkv (cs₁ ++ ⟨x, a, true⟩ :: ⟨x + a, b, true⟩ :: cs₂) bins)
    (hno : ∀ e ∈ H, e.1 ≠ x + a + 16)
    {h' : Nat} (hhdr : read64 m' (x + 8) = some h') (hsz : chunkSize h' = a + b)
    (hlow : h' % 4 < 2) (hpi : ∀ h0, read64 m (x + 8) = some h0 → prevInuse h' = prevInuse h0)
    (hag : ∀ w, vsaFoot H w → ¬ (x + 8 ≤ w ∧ w < x + 16) → ¬ (x + a + 8 ≤ w ∧ w < x + a + 16) →
      m'[w]? = m[w]?) :
    PHeapAt m' H top brkv (cs₁ ++ ⟨x, a + b, true⟩ :: cs₂) bins := by
  obtain ⟨B, hpage, hbbl⟩ := h
  have HH := B.heap
  obtain ⟨hal, htop16⟩ := HH.aligned
  have hlo := HH.walk.le
  have hcb := HH.walk.chunk_bounds
  have hbrk := HH.brk_le
  have htle := HH.top_le
  have hX : (⟨x, a, true⟩ : Chunk) ∈ cs₁ ++ ⟨x, a, true⟩ :: ⟨x + a, b, true⟩ :: cs₂ := by simp
  have hY : (⟨x + a, b, true⟩ : Chunk) ∈ cs₁ ++ ⟨x, a, true⟩ :: ⟨x + a, b, true⟩ :: cs₂ := by simp
  have hXb := hcb _ hX; have hYb := hcb _ hY
  have hx16 : x % 16 = 0 := hal _ hX
  have hy16 : (x + a) % 16 = 0 := hal _ hY
  simp only at hXb hYb hx16 hy16
  unfold heapStart at hlo hXb hYb
  -- the walk around `x`
  obtain ⟨mid, W1, W2⟩ := HH.walk.append_inv
  have HX := walkHead W2
  have hmid : x = mid := HX.addr
  subst hmid
  obtain ⟨hh, hhr, hhs, hhl⟩ := HX.hdr
  have HY := walkHead HX.rest
  simp only at HY
  obtain ⟨h3, h3r, h3p⟩ := HY.next
  simp only at h3r h3p
  have hW1b := W1.chunk_bounds
  have hW3b : ∀ c ∈ cs₂, x + a + b ≤ c.addr ∧ c.addr + c.size ≤ top ∧ 32 ≤ c.size :=
    HY.rest.chunk_bounds
  have ha16 : a % 16 = 0 := HX.al
  have hb16 : b % 16 = 0 := HY.al
  have hW3le := HY.rest.le
  -- words the absorb does not write
  have keep : ∀ w, (∀ k, k < 8 → vsaFoot H (w + k)) → (w + 8 ≤ x + 8 ∨ x + 16 ≤ w) →
      (w + 8 ≤ x + a + 8 ∨ x + a + 16 ≤ w) → read64 m' w = read64 m w := by
    intro w hf h1 h2
    exact read64_keep fun k hk => hag _ (hf k hk) (by omega) (by omega)
  have Kg : ∀ w, (∀ k, k < 8 → allocGlobal (w + k)) → read64 m' w = read64 m w := by
    intro w hg
    have := hg 0 (by omega); have := hg 7 (by omega)
    unfold allocGlobal InRange at *
    exact keep w (fun k hk => .inl (hg k hk)) (.inl (by omega)) (.inl (by omega))
  -- the new walk
  have W3 : ChunkWalk m' (x + a + b) top cs₂ := by
    refine HY.rest.transport_headers fun q hq => (keep _ ?_ ?_ ?_).symm
    · rcases hq with rfl | ⟨c, hc, rfl⟩
      · exact foot_header B (.inl rfl)
      · exact foot_header B (.inr ⟨c, by simp [hc], rfl⟩)
    · rcases hq with rfl | ⟨c, hc, rfl⟩
      · exact .inr (by omega)
      · have := hW3b c hc; exact .inr (by omega)
    · rcases hq with rfl | ⟨c, hc, rfl⟩
      · exact .inr (by omega)
      · have := hW3b c hc; exact .inr (by omega)
  have hnxf : ∀ k, k < 8 → vsaFoot H (x + a + b + 8 + k) := by
    have hq : x + a + b = top ∨
        ∃ c ∈ cs₁ ++ ⟨x, a, true⟩ :: ⟨x + a, b, true⟩ :: cs₂, c.addr = x + a + b := by
      rcases HY.rest.head_or_top with he | ⟨c, hc, hca⟩
      · exact .inl he
      · exact .inr ⟨c, by simp [hc], hca⟩
    exact foot_header B hq
  have h3r' : read64 m' (x + a + b + 8) = some h3 :=
    (keep _ hnxf (.inr (by omega)) (.inr (by omega))).trans h3r
  have WX : ChunkWalk m' x top (⟨x, a + b, true⟩ :: cs₂) := by
    have w := ChunkWalk.chunk (m := m') (p := x) (h := h') (h' := h3) hhdr hlow
      (by rw [hsz]; omega) (by rw [hsz]; omega)
      (by rw [hsz, ← Nat.add_assoc]; exact h3r') (by rw [hsz, ← Nat.add_assoc]; exact W3)
    rwa [hsz, h3p] at w
  have hwalk : ChunkWalk m' heapStart top (cs₁ ++ ⟨x, a + b, true⟩ :: cs₂) := by
    refine W1.extend (fun c hc => keep _ (foot_header B (.inr ⟨c, by simp [hc], rfl⟩)) ?_ ?_)
      (fun h1 hh1 => ⟨h', hhdr, hpi h1 hh1⟩) WX
    · have := hW1b c hc; exact .inl (by omega)
    · have := hW1b c hc; exact .inl (by omega)
  -- the old and new chunk lists
  have hmemL : ∀ c, c ∈ cs₁ ++ ⟨x, a, true⟩ :: ⟨x + a, b, true⟩ :: cs₂ ↔
      c ∈ cs₁ ∨ c = ⟨x, a, true⟩ ∨ c = ⟨x + a, b, true⟩ ∨ c ∈ cs₂ := by
    intro c; simp only [List.mem_append, List.mem_cons]
  have hmemL' : ∀ c, c ∈ cs₁ ++ ⟨x, a + b, true⟩ :: cs₂ ↔
      c ∈ cs₁ ∨ c = ⟨x, a + b, true⟩ ∨ c ∈ cs₂ := by
    intro c; simp only [List.mem_append, List.mem_cons]
  have hfree_loc : ∀ c ∈ cs₁ ++ ⟨x, a, true⟩ :: ⟨x + a, b, true⟩ :: cs₂, c.inuse = false →
      (c ∈ cs₁ ∧ c.addr + c.size ≤ x) ∨ (c ∈ cs₂ ∧ x + a + b ≤ c.addr) := by
    intro c hc hf
    rcases (hmemL c).1 hc with h1 | rfl | rfl | h1
    · exact .inl ⟨h1, (hW1b c h1).2.1⟩
    · cases hf
    · cases hf
    · exact .inr ⟨h1, (hW3b c h1).1⟩
  have hfree_new : ∀ c ∈ cs₁ ++ ⟨x, a, true⟩ :: ⟨x + a, b, true⟩ :: cs₂, c.inuse = false →
      c ∈ cs₁ ++ ⟨x, a + b, true⟩ :: cs₂ := by
    intro c hc hf
    rcases hfree_loc c hc hf with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp [h1]
  have hfree_old : ∀ c ∈ cs₁ ++ ⟨x, a + b, true⟩ :: cs₂, c.inuse = false →
      c ∈ cs₁ ++ ⟨x, a, true⟩ :: ⟨x + a, b, true⟩ :: cs₂ := by
    intro c hc hf
    rcases (hmemL' c).1 hc with h1 | rfl | h1
    · simp [h1]
    · cases hf
    · simp [h1]
  -- links of bin nodes
  have Klink : ∀ j y, 0 < j → j < numBins → (y = binAt j ∨ y ∈ bins j) →
      fdOf m' y = fdOf m y ∧ bkOf m' y = bkOf m y := by
    intro j y hj0 hj hy
    have hgj := binAt_geo j hj
    rcases hy with rfl | hy
    · exact ⟨Kg _ fun k hk => .inl ⟨by omega, by omega⟩, Kg _ fun k hk => .inl ⟨by omega, by omega⟩⟩
    · obtain ⟨c, hc, rfl, hf⟩ := HH.member hj0 hj hy
      have hff := (foot_free B hc hf).1
      have hloc := hfree_loc c hc hf
      have hcs := (HH.walk.chunk_bounds c hc).2.2
      refine ⟨keep _ (fun k hk => hff k (by omega)) ?_ ?_,
        keep _ (fun k hk => by have := hff (8 + k) (by omega); rwa [show c.addr + 16 + (8 + k) =
          c.addr + 24 + k by omega] at this) ?_ ?_⟩ <;>
        rcases hloc with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega
  have kBb : read64 m' binblocksAddr = read64 m binblocksAddr :=
    Kg _ fun k hk => .inl ⟨by unfold binblocksAddr avAddr; omega, by unfold binblocksAddr avAddr; omega⟩
  have kTop : read64 m' topAddr = read64 m topAddr :=
    Kg _ fun k hk => .inl ⟨by unfold topAddr avAddr; omega, by unfold topAddr avAddr; omega⟩
  have gHi : ∀ w, 0x8001b990 ≤ w → w + 8 ≤ 0x8001b9b0 → ∀ k, k < 8 → allocGlobal (w + k) :=
    fun w h1 h2 k hk => .inr (.inr (.inr (.inl ⟨by omega, by omega⟩)))
  have hMm : (⟨x, a + b, true⟩ : Chunk) ∈ cs₁ ++ ⟨x, a + b, true⟩ :: cs₂ := by simp
  refine ⟨⟨{ sbrk_base := ?_, brk := ?_, brk_le := HH.brk_le, top_ptr := kTop.trans HH.top_ptr
             top_le := HH.top_le, top_size := HH.top_size, top_header := ?_
             top_pad := ?_, max_sbrked := ?_, mallinfo := ?_, first_prev := ?_
             walk := hwalk, coalesced := coal_merge rfl HH.coalesced, footer := ?_
             bins_list := ?_, bins_nodup := HH.bins_nodup
             bin_free := ?_, free_binned := ?_, remainder := HH.remainder
             binblocks_present := by rw [kBb]; exact HH.binblocks_present
             binblocks := fun bb hbb => HH.binblocks bb (by rw [← kBb]; exact hbb)
             live := ?_, exact := ?_ }, B.top_room⟩, hpage,
    fun bb hbb => hbbl bb (by rw [← kBb]; exact hbb)⟩
  · rw [Kg _ (fun k hk => .inr (.inr (.inl ⟨by unfold sbrkBaseAddr; omega,
      by unfold sbrkBaseAddr; omega⟩)))]
    exact HH.sbrk_base
  · rw [Kg _ (gHi _ (by unfold brkAddr; omega) (by unfold brkAddr; omega))]
    exact HH.brk
  · rw [keep _ (foot_header B (.inl rfl)) (.inr (by omega)) (.inr (by omega))]
    exact HH.top_header
  · rw [Kg _ (gHi _ (by unfold topPadAddr; omega) (by unfold topPadAddr; omega))]
    exact HH.top_pad
  · rw [Kg _ (gHi _ (by unfold maxSbrkedAddr; omega) (by unfold maxSbrkedAddr; omega))]
    exact HH.max_sbrked
  · rw [Kg _ (fun k hk => .inr (.inr (.inr (.inr (.inr ⟨by unfold mallinfoAddr; omega,
      by unfold mallinfoAddr; omega⟩)))))]
    exact HH.mallinfo
  · rcases W1.head_or_top with he | ⟨c, hc, hca⟩
    · have hfp := HH.first_prev
      rw [he, hhr] at hfp
      rw [he, hhdr]
      unfold prevInuse at hpi
      have := hpi hh hhr
      simp only [Option.any] at hfp ⊢
      exact this ▸ hfp
    · have := hW1b c hc
      rw [← hca, keep _ (foot_header B (.inr ⟨c, by simp [hc], rfl⟩)) (.inl (by omega))
        (.inl (by omega)), hca]
      exact HH.first_prev
  · intro c hc hf
    have hcL := hfree_old c hc hf
    have hloc := hfree_loc c hcL hf
    rw [keep _ (foot_free B hcL hf).2 (by rcases hloc with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega)
      (by rcases hloc with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega)]
    exact HH.footer c hcL hf
  · intro j hj0 hj
    rw [binList_iff_ring]
    have hold := binList_iff_ring.1 (HH.bins_list j hj0 hj)
    refine ⟨?_, hold.2⟩
    have hr := hold.1
    unfold Ring at hr ⊢
    refine hr.transport fun a' b' hab => ?_
    have ⟨ha, hb⟩ := pair_mem hab
    have hnode : ∀ y ∈ binAt j :: bins j ++ [binAt j], y = binAt j ∨ y ∈ bins j := by
      intro y hy
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
        or_false] at hy
      rcases hy with h1 | h1 | h1
      · exact .inl h1
      · exact .inr h1
      · exact .inl h1
    exact ⟨(Klink j a' hj0 hj (hnode a' ha)).1, (Klink j b' hj0 hj (hnode b' hb)).2⟩
  · intro j q hj0 hj hq
    obtain ⟨c, hc, h1, h2, h3⟩ := HH.bin_free j q hj0 hj hq
    exact ⟨c, hfree_new c hc h2, h1, h2, h3⟩
  · intro c hc hf
    exact HH.free_binned c (hfree_old c hc hf) hf
  · intro e he
    obtain ⟨c, hc, hu, h1, h2⟩ := HH.live e he
    rcases (hmemL c).1 hc with h3 | rfl | rfl | h3
    · exact ⟨c, by simp [h3], hu, h1, h2⟩
    · exact ⟨_, hMm, rfl, h1, by simp only at h1 h2 ⊢; omega⟩
    · exact ⟨_, hMm, rfl, by simp only at h1 ⊢; omega, by simp only at h1 h2 ⊢; omega⟩
    · exact ⟨c, by simp [h3], hu, h1, h2⟩
  · intro e he hr
    obtain ⟨c, hc, hu, h1, h2⟩ := HH.exact e he hr
    rcases (hmemL c).1 hc with h3 | rfl | rfl | h3
    · exact ⟨c, by simp [h3], hu, h1, h2⟩
    · exact ⟨_, hMm, rfl, h1, by simp only at h1 h2 ⊢; omega⟩
    · exact absurd h1.symm (hno e he)
    · exact ⟨c, by simp [h3], hu, h1, h2⟩

end VsaIris.VsaHeap
