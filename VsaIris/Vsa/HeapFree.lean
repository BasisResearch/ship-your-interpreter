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

/-- A prefix of a coalesced list is coalesced. -/
theorem coal_of_append {cs ds : List Chunk} (h : Coal (cs ++ ds)) : Coal cs := by
  intro i hi
  have := h i (by simp; omega)
  rwa [List.getElem_append_left (by omega), List.getElem_append_left (by omega)] at this

/-- **The chunk below the top becomes the top.** The in-use chunk `x` just
below the top, its predecessor in use and no live block in it (`hno`), merges
into the top: `av->top := x` and `x`'s header records the size to the break
with `PREV_INUSE`. -/
theorem PHeapAt.toTop {m m' : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {cs₁ : List Chunk} {bins : Nat → List Nat} {x a : Nat}
    (h : PHeapAt m H top brkv (cs₁ ++ [⟨x, a, true⟩]) bins)
    (hno : ∀ e ∈ H, e.1 ≠ x + 16)
    (hprev : ∀ h0, read64 m (x + 8) = some h0 → h0 % 2 = 1)
    (htp : read64 m' topAddr = some x) (hhdr : read64 m' (x + 8) = some (brkv - x + 1))
    (hag : ∀ w, vsaFoot H w → ¬ (x + 8 ≤ w ∧ w < x + 16) → ¬ (topAddr ≤ w ∧ w < topAddr + 8) →
      m'[w]? = m[w]?) :
    PHeapAt m' H x brkv cs₁ bins := by
  obtain ⟨B, hpage, hbbl⟩ := h
  have HH := B.heap
  obtain ⟨hal, htop16⟩ := HH.aligned
  have hlo := HH.walk.le
  have hcb := HH.walk.chunk_bounds
  have hbrk := HH.brk_le
  have htle := HH.top_le
  have htsz := HH.top_size
  have hX : (⟨x, a, true⟩ : Chunk) ∈ cs₁ ++ [⟨x, a, true⟩] := by simp
  have hXb := hcb _ hX
  have hx16 : x % 16 = 0 := hal _ hX
  simp only at hXb hx16
  unfold heapStart at hlo hXb
  obtain ⟨mid, W1, W2⟩ := HH.walk.append_inv
  have HX := walkHead W2
  have hmid : x = mid := HX.addr
  subst hmid
  have ha16 : a % 16 = 0 := HX.al
  have hxa : x + a = top := by have := HX.rest; cases this; rfl
  have hW1b := W1.chunk_bounds
  have keep : ∀ w, (∀ k, k < 8 → vsaFoot H (w + k)) → (w + 8 ≤ x + 8 ∨ x + 16 ≤ w) →
      (w + 8 ≤ topAddr ∨ topAddr + 8 ≤ w) → read64 m' w = read64 m w := by
    intro w hf h1 h2
    exact read64_keep fun k hk => hag _ (hf k hk) (by omega) (by omega)
  have Kg : ∀ w, (∀ k, k < 8 → allocGlobal (w + k)) → (w + 8 ≤ topAddr ∨ topAddr + 8 ≤ w) →
      read64 m' w = read64 m w := by
    intro w hg ht
    have := hg 0 (by omega); have := hg 7 (by omega)
    unfold allocGlobal InRange at *
    exact keep w (fun k hk => .inl (hg k hk)) (.inl (by omega)) ht
  have hwalk : ChunkWalk m' heapStart x cs₁ := by
    have w := W1.extend (fun c hc => keep _ (foot_header B (.inr ⟨c, by simp [hc], rfl⟩))
        (by have := hW1b c hc; exact .inl (by omega))
        (by have := hW1b c hc; unfold topAddr avAddr; unfold heapStart at this; omega))
      (fun h1 hh1 => ⟨brkv - x + 1, hhdr, by
        have := hprev h1 hh1
        unfold prevInuse; rw [show (brkv - x + 1) % 2 = 1 by omega, this]⟩)
      (ChunkWalk.top (m := m') (p := x))
    rwa [List.append_nil] at w
  have hmemL : ∀ c, c ∈ cs₁ ++ [⟨x, a, true⟩] ↔ c ∈ cs₁ ∨ c = ⟨x, a, true⟩ := by
    intro c; simp only [List.mem_append, List.mem_singleton]
  have hfree_in : ∀ c ∈ cs₁ ++ [⟨x, a, true⟩], c.inuse = false → c ∈ cs₁ := by
    intro c hc hf
    rcases (hmemL c).1 hc with h1 | rfl
    · exact h1
    · cases hf
  have hin_old : ∀ c ∈ cs₁, c ∈ cs₁ ++ [⟨x, a, true⟩] := fun c hc => by simp [hc]
  have Klink : ∀ j y, 0 < j → j < numBins → (y = binAt j ∨ y ∈ bins j) →
      fdOf m' y = fdOf m y ∧ bkOf m' y = bkOf m y := by
    intro j y hj0 hj hy
    have hgj := binAt_geo j hj
    rcases hy with rfl | hy
    · exact ⟨Kg _ (fun k hk => .inl ⟨by omega, by omega⟩)
          (by unfold topAddr binAt avAddr; unfold binAt avAddr at hgj; omega),
        Kg _ (fun k hk => .inl ⟨by omega, by omega⟩)
          (by unfold topAddr binAt avAddr; unfold binAt avAddr at hgj; omega)⟩
    · obtain ⟨c, hc, rfl, hf⟩ := HH.member hj0 hj hy
      have hff := (foot_free B hc hf).1
      have hc1 := hfree_in c hc hf
      have := hW1b c hc1
      unfold heapStart at this
      refine ⟨keep _ (fun k hk => hff k (by omega)) (.inl (by omega))
          (by unfold topAddr avAddr; omega),
        keep _ (fun k hk => by have := hff (8 + k) (by omega); rwa [show c.addr + 16 + (8 + k) =
          c.addr + 24 + k by omega] at this) (.inl (by omega)) (by unfold topAddr avAddr; omega)⟩
  have gAv : ∀ w, 0x8001ad10 ≤ w → w + 8 ≤ 0x8001b520 → ∀ k, k < 8 → allocGlobal (w + k) :=
    fun w h1 h2 k hk => .inl ⟨by omega, by omega⟩
  have gHi : ∀ w, 0x8001b990 ≤ w → w + 8 ≤ 0x8001b9b0 → ∀ k, k < 8 → allocGlobal (w + k) :=
    fun w h1 h2 k hk => .inr (.inr (.inr (.inl ⟨by omega, by omega⟩)))
  have kBb : read64 m' binblocksAddr = read64 m binblocksAddr :=
    Kg _ (gAv _ (by unfold binblocksAddr avAddr; omega) (by unfold binblocksAddr avAddr; omega))
      (by unfold binblocksAddr topAddr avAddr; omega)
  refine ⟨⟨{ sbrk_base := ?_, brk := ?_, brk_le := HH.brk_le, top_ptr := htp
             top_le := by omega, top_size := by omega, top_header := hhdr
             top_pad := ?_, max_sbrked := ?_, mallinfo := ?_, first_prev := ?_
             walk := hwalk, coalesced := coal_of_append HH.coalesced, footer := ?_
             bins_list := ?_, bins_nodup := HH.bins_nodup
             bin_free := ?_, free_binned := ?_, remainder := HH.remainder
             binblocks_present := by rw [kBb]; exact HH.binblocks_present
             binblocks := fun bb hbb => HH.binblocks bb (by rw [← kBb]; exact hbb)
             live := ?_, exact := ?_ }, by omega⟩, hpage,
    fun bb hbb => hbbl bb (by rw [← kBb]; exact hbb)⟩
  · rw [Kg _ (fun k hk => .inr (.inr (.inl ⟨by unfold sbrkBaseAddr; omega,
      by unfold sbrkBaseAddr; omega⟩))) (by unfold sbrkBaseAddr topAddr avAddr; omega)]
    exact HH.sbrk_base
  · rw [Kg _ (gHi _ (by unfold brkAddr; omega) (by unfold brkAddr; omega))
      (by unfold brkAddr topAddr avAddr; omega)]
    exact HH.brk
  · rw [Kg _ (gHi _ (by unfold topPadAddr; omega) (by unfold topPadAddr; omega))
      (by unfold topPadAddr topAddr avAddr; omega)]
    exact HH.top_pad
  · rw [Kg _ (gHi _ (by unfold maxSbrkedAddr; omega) (by unfold maxSbrkedAddr; omega))
      (by unfold maxSbrkedAddr topAddr avAddr; omega)]
    exact HH.max_sbrked
  · rw [Kg _ (fun k hk => .inr (.inr (.inr (.inr (.inr ⟨by unfold mallinfoAddr; omega,
      by unfold mallinfoAddr; omega⟩))))) (by unfold mallinfoAddr topAddr avAddr; omega)]
    exact HH.mallinfo
  · rcases W1.head_or_top with he | ⟨c, hc, hca⟩
    · rw [he, hhdr]; simp only [Option.any, beq_iff_eq]; omega
    · have := hW1b c hc
      rw [← hca, keep _ (foot_header B (.inr ⟨c, by simp [hc], rfl⟩)) (.inl (by omega))
        (by unfold topAddr avAddr; unfold heapStart at this; omega), hca]
      exact HH.first_prev
  · intro c hc hf
    have hcL := hin_old c hc
    have := hW1b c hc
    unfold heapStart at this
    rw [keep _ (foot_free B hcL hf).2 (.inl (by omega)) (by unfold topAddr avAddr; omega)]
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
    exact ⟨c, hfree_in c hc h2, h1, h2, h3⟩
  · intro c hc hf
    exact HH.free_binned c (hin_old c hc) hf
  · intro e he
    obtain ⟨c, hc, hu, h1, h2⟩ := HH.exact e he he
    rcases (hmemL c).1 hc with h3 | rfl
    · exact ⟨c, h3, hu, by omega, by omega⟩
    · exact absurd h1.symm (hno e he)
  · intro e he hr
    obtain ⟨c, hc, hu, h1, h2⟩ := HH.exact e he hr
    rcases (hmemL c).1 hc with h3 | rfl
    · exact ⟨c, h3, hu, h1, h2⟩
    · exact absurd h1.symm (hno e he)

/-- Freeing a chunk between two in-use ones keeps coalescing. -/
theorem coal_release {X X' : Chunk} :
    ∀ {cs₁ cs₂ : List Chunk}, Coal (cs₁ ++ X :: cs₂) → (∀ c ∈ cs₁.getLast?, c.inuse = true) →
      (∀ d ∈ cs₂.head?, d.inuse = true) → Coal (cs₁ ++ X' :: cs₂)
  | [], [], _, _, _ => by simpa using coal_single X'
  | [], d :: cs₂, h, _, hd => by
    simp only [List.nil_append] at h ⊢
    exact coal_cons_cons.2 ⟨.inr (hd d rfl), (coal_cons_cons.1 h).2⟩
  | [z], cs₂, h, hl, hd => by
    simp only [List.cons_append, List.nil_append] at h ⊢
    exact coal_cons_cons.2 ⟨.inl (hl z rfl), coal_release (cs₁ := []) (coal_cons_cons.1 h).2
      (fun _ h => nomatch h) hd⟩
  | z :: w :: cs₁, cs₂, h, hl, hd => by
    simp only [List.cons_append] at h ⊢
    exact coal_cons_cons.2 ⟨(coal_cons_cons.1 h).1, coal_release (cs₁ := w :: cs₁)
      (coal_cons_cons.1 h).2 (fun c hc => hl c (by simpa using hc)) hd⟩

/-- The words a release writes: the chunk's links, the insertion point's two
links, `binblocks`, and the chunk's footer with the next header. -/
def RelW (v sz pred succ : Nat) (w : Nat) : Prop :=
  (v + 16 ≤ w ∧ w < v + 32) ∨ (pred + 16 ≤ w ∧ w < pred + 24) ∨ (succ + 24 ≤ w ∧ w < succ + 32) ∨
    (binblocksAddr ≤ w ∧ w < binblocksAddr + 8) ∨ (v + sz ≤ w ∧ w < v + sz + 16)

/-- **Release an in-use chunk into a bin.** The in-use chunk `v`, with no live
block in it (`hno`), its predecessor in use and an in-use chunk after it (not
the top), becomes free: the next header's `PREV_INUSE` is cleared, its footer
written, and it is linked into bin `j` between `pred` and `succ`, with `j`'s
block bit set. Bin 1 takes it only when empty. -/
theorem PHeapAt.release {m m' : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {cs₁ cs₂ : List Chunk} {bins : Nat → List Nat} {v sz : Nat}
    (h : PHeapAt m H top brkv (cs₁ ++ ⟨v, sz, true⟩ :: cs₂) bins)
    (hno : ∀ e ∈ H, e.1 ≠ v + 16)
    (hprev : ∀ h0, read64 m (v + 8) = some h0 → h0 % 2 = 1)
    (hnext : ∀ d ∈ cs₂.head?, d.inuse = true) (hnt : v + sz ≠ top)
    {j pred succ bb' : Nat} {pre' post' : List Nat}
    (hj0 : 0 < j) (hj : j < numBins) (hidx : 1 < j → binIndex sz = j) (hj1 : j = 1 → bins 1 = [])
    (hpos : bins j = pre' ++ post')
    (hpred : (binAt j :: pre').getLast? = some pred) (hsucc : (post' ++ [binAt j]).head? = some succ)
    (hfdV : fdOf m' v = some succ) (hbkV : bkOf m' v = some pred)
    (hfdP : fdOf m' pred = some v) (hbkS : bkOf m' succ = some v)
    (hft : read64 m' (v + sz) = some sz)
    (hnx : ∀ hd, read64 m (v + sz + 8) = some hd → ∃ hd', read64 m' (v + sz + 8) = some hd' ∧
      chunkSize hd' = chunkSize hd ∧ hd' % 4 < 2 ∧ prevInuse hd' = false)
    (hbbr : read64 m' binblocksAddr = some bb') (hbblt : bb' < 2 ^ 32)
    (hbbset : 1 < j → bb' / 2 ^ (j / 4) % 2 = 1)
    (hbbkeep : ∀ bb, read64 m binblocksAddr = some bb →
      ∀ k, bb / 2 ^ k % 2 = 1 → bb' / 2 ^ k % 2 = 1)
    (hag : ∀ w, vsaFoot H w → ¬ RelW v sz pred succ w → m'[w]? = m[w]?) :
    PHeapAt m' H top brkv (cs₁ ++ ⟨v, sz, false⟩ :: cs₂) (updBins bins j (pre' ++ v :: post')) := by
  obtain ⟨B, hpage, hbbl⟩ := h
  have HH := B.heap
  obtain ⟨hal, htop16⟩ := HH.aligned
  have hlo := HH.walk.le
  have hcb := HH.walk.chunk_bounds
  have hbrk := HH.brk_le
  have htle := HH.top_le
  have hgj := binAt_geo j hj
  have hV : (⟨v, sz, true⟩ : Chunk) ∈ cs₁ ++ ⟨v, sz, true⟩ :: cs₂ := by simp
  have hVb := hcb _ hV
  have hv16 : v % 16 = 0 := hal _ hV
  simp only at hVb hv16
  unfold heapStart at hlo hVb
  -- the walk around `v`
  obtain ⟨mid, W1, W2⟩ := HH.walk.append_inv
  have HV := walkHead W2
  have hmid : v = mid := HV.addr
  subst hmid
  have hsz16 : sz % 16 = 0 := HV.al
  obtain ⟨hh, hhr, hhs, hhl⟩ := HV.hdr
  obtain ⟨d, cs₃, rfl⟩ : ∃ d cs₃, cs₂ = d :: cs₃ := by
    rcases hc : cs₂ with _ | ⟨d, cs₃⟩
    · have := HV.rest; rw [hc] at this; exfalso; cases this; exact hnt rfl
    · exact ⟨d, cs₃, rfl⟩
  have HD := walkHead HV.rest
  simp only at HD
  have hdin : d.inuse = true := hnext d rfl
  have hda : d.addr = v + sz := HD.addr
  obtain ⟨hd0, hd0r, hd0s, hd0l⟩ := HD.hdr
  obtain ⟨h2, h2r, h2p⟩ := HD.next
  have hdmin := HD.min; have hdal := HD.al
  have hW3b : ∀ c ∈ cs₃, v + sz + d.size ≤ c.addr ∧ c.addr + c.size ≤ top ∧ 32 ≤ c.size :=
    HD.rest.chunk_bounds
  have hW3le := HD.rest.le
  have hW1b := W1.chunk_bounds
  -- the chunks around `v`
  have hmemL : ∀ c, c ∈ cs₁ ++ ⟨v, sz, true⟩ :: d :: cs₃ ↔
      c ∈ cs₁ ∨ c = ⟨v, sz, true⟩ ∨ c = d ∨ c ∈ cs₃ := by
    intro c; simp only [List.mem_append, List.mem_cons]
  have hmemL' : ∀ c, c ∈ cs₁ ++ ⟨v, sz, false⟩ :: d :: cs₃ ↔
      c ∈ cs₁ ∨ c = ⟨v, sz, false⟩ ∨ c = d ∨ c ∈ cs₃ := by
    intro c; simp only [List.mem_append, List.mem_cons]
  have hfree_loc : ∀ c ∈ cs₁ ++ ⟨v, sz, true⟩ :: d :: cs₃, c.inuse = false →
      (c ∈ cs₁ ∧ c.addr + c.size ≤ v) ∨ (c ∈ cs₃ ∧ v + sz + d.size ≤ c.addr) := by
    intro c hc hf
    rcases (hmemL c).1 hc with h1 | rfl | rfl | h1
    · exact .inl ⟨h1, (hW1b c h1).2.1⟩
    · cases hf
    · rw [hdin] at hf; cases hf
    · exact .inr ⟨h1, (hW3b c h1).1⟩
  have hfree_new : ∀ c ∈ cs₁ ++ ⟨v, sz, true⟩ :: d :: cs₃, c.inuse = false →
      c ∈ cs₁ ++ ⟨v, sz, false⟩ :: d :: cs₃ := by
    intro c hc hf
    rcases hfree_loc c hc hf with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp [h1]
  have hvfree : ∀ k, 0 < k → k < numBins → v ∉ bins k := by
    intro k hk0 hk hm
    obtain ⟨c, hc, hca, hf⟩ := HH.member hk0 hk hm
    have := HH.chunk_eq hc hV hca
    rw [this] at hf; cases hf
  -- the insertion point's nodes
  have hpm : pred = binAt j ∨ pred ∈ bins j := by
    have := List.mem_of_getLast? hpred
    rcases List.mem_cons.mp this with h1 | h1
    · exact .inl h1
    · exact .inr (by rw [hpos]; exact List.mem_append_left _ h1)
  have hsm : succ = binAt j ∨ succ ∈ bins j := by
    have := List.mem_of_head? hsucc
    rcases List.mem_append.mp this with h1 | h1
    · exact .inr (by rw [hpos]; exact List.mem_append_right _ h1)
    · exact .inl (List.mem_singleton.mp h1)
  -- a bin node: its header, or a free chunk before `v` or after `d`
  have hnodeLoc : ∀ k, 0 < k → k < numBins → ∀ y, (y = binAt k ∨ y ∈ bins k) →
      y % 16 = 0 ∧ ((y = binAt k ∧ 0x8001ad20 ≤ y ∧ y + 32 ≤ 0x8001b520) ∨
        (0x8001c170 ≤ y ∧ (y + 32 ≤ v ∨ v + sz + d.size ≤ y) ∧
          ∀ o, 16 ≤ o → o < 32 → vsaFoot H (y + o))) := by
    intro k hk0 hk y hy
    rcases hy with rfl | hy
    · have := binAt_geo k hk
      exact ⟨this.1, .inl ⟨rfl, by unfold binAt avAddr; omega, this.2.2⟩⟩
    · obtain ⟨c, hc, rfl, hf⟩ := HH.member hk0 hk hy
      have hcs := (hcb c hc).2.2
      have hcl := (hcb c hc).1
      unfold heapStart at hcl
      refine ⟨hal c hc, .inr ⟨hcl, ?_, B.node_foot hk0 hk (.inr hy)⟩⟩
      rcases hfree_loc c hc hf with ⟨_, h1⟩ | ⟨_, h1⟩
      · exact .inl (by omega)
      · exact .inr h1
  have hpN : pred % 16 = 0 ∧ ((0x8001ad20 ≤ pred ∧ pred + 32 ≤ 0x8001b520) ∨
      (0x8001c170 ≤ pred ∧ (pred + 32 ≤ v ∨ v + sz + d.size ≤ pred))) := by
    obtain ⟨h16, ⟨_, h1, h2⟩ | ⟨h1, h2, _⟩⟩ := hnodeLoc j hj0 hj pred hpm
    · exact ⟨h16, .inl ⟨h1, h2⟩⟩
    · exact ⟨h16, .inr ⟨h1, h2⟩⟩
  obtain ⟨_, hpnode⟩ := HH.node hj0 hj hpm
  obtain ⟨_, hsnode⟩ := HH.node hj0 hj hsm
  have hbp : ∀ b', (b' = top ∨ ∃ c ∈ cs₁ ++ ⟨v, sz, true⟩ :: d :: cs₃, c.addr = b') →
      ∀ k, 0 < k → k < 32 → b' ≠ pred + k :=
    fun b' hb k hk0 hk => HH.bnd_ne_node hj hpnode hb k hk0 hk
  have hbs : ∀ b', (b' = top ∨ ∃ c ∈ cs₁ ++ ⟨v, sz, true⟩ :: d :: cs₃, c.addr = b') →
      ∀ k, 0 < k → k < 32 → b' ≠ succ + k :=
    fun b' hb k hk0 hk => HH.bnd_ne_node hj hsnode hb k hk0 hk
  have hsN : succ % 16 = 0 ∧ ((0x8001ad20 ≤ succ ∧ succ + 32 ≤ 0x8001b520) ∨
      (0x8001c170 ≤ succ ∧ (succ + 32 ≤ v ∨ v + sz + d.size ≤ succ))) := by
    obtain ⟨h16, ⟨_, h1, h2⟩ | ⟨h1, h2, _⟩⟩ := hnodeLoc j hj0 hj succ hsm
    · exact ⟨h16, .inl ⟨h1, h2⟩⟩
    · exact ⟨h16, .inr ⟨h1, h2⟩⟩
  -- words the release does not write
  have keep : ∀ w, (∀ k, k < 8 → vsaFoot H (w + k)) → w % 8 = 0 →
      w ≠ v + 16 → w ≠ v + 24 → w ≠ pred + 16 → w ≠ succ + 24 → w ≠ binblocksAddr →
      w ≠ v + sz → w ≠ v + sz + 8 → read64 m' w = read64 m w := by
    intro w hf hw8 h1 h2 h3 h4 h5 h6 h7
    have hp8 : pred % 8 = 0 := by omega
    have hs8 : succ % 8 = 0 := by omega
    refine read64_keep fun k hk => hag _ (hf k hk) ?_
    unfold RelW binblocksAddr avAddr
    unfold binblocksAddr avAddr at h5
    omega
  have Kg : ∀ w, (∀ k, k < 8 → allocGlobal (w + k)) → w % 8 = 0 → w + 8 ≤ 0x8001c170 →
      w ≠ pred + 16 → w ≠ succ + 24 → w ≠ binblocksAddr → read64 m' w = read64 m w := by
    intro w hg hw8 hw h3 h4 h5
    exact keep w (fun k hk => .inl (hg k hk)) hw8 (by omega) (by omega) h3 h4 h5 (by omega)
      (by omega)
  have Kg' : ∀ w, (∀ k, k < 8 → allocGlobal (w + k)) → w % 8 = 0 → 0x8001b520 ≤ w →
      w + 8 ≤ 0x8001c170 → read64 m' w = read64 m w := by
    intro w hg hw8 h1 h2
    refine Kg w hg hw8 h2 ?_ ?_ (by unfold binblocksAddr avAddr; omega)
    · rcases hpN with ⟨_, ⟨_, _⟩ | ⟨_, _ | _⟩⟩ <;> (try unfold heapStart at *) <;> (try unfold topAddr avAddr at *) <;> omega
    · rcases hsN with ⟨_, ⟨_, _⟩ | ⟨_, _ | _⟩⟩ <;> (try unfold heapStart at *) <;> (try unfold topAddr avAddr at *) <;> omega
  -- the new walk
  have W3 : ChunkWalk m' (v + sz + d.size) top cs₃ := by
    refine HD.rest.transport_headers fun q hq => ?_
    have hq16 : q % 16 = 0 := by
      rcases hq with rfl | ⟨c, hc, rfl⟩
      · exact htop16
      · exact hal c (by simp [hc])
    have hqb : v + sz + d.size ≤ q := by
      rcases hq with rfl | ⟨c, hc, rfl⟩
      · exact hW3le
      · exact (hW3b c hc).1
    have hqf : ∀ k, k < 8 → vsaFoot H (q + 8 + k) := by
      rcases hq with rfl | ⟨c, hc, rfl⟩
      · exact foot_header B (.inl rfl)
      · exact foot_header B (.inr ⟨c, by simp [hc], rfl⟩)
    have hqb' : q = top ∨ ∃ c ∈ cs₁ ++ ⟨v, sz, true⟩ :: d :: cs₃, c.addr = q := by
      rcases hq with rfl | ⟨c, hc, rfl⟩
      · exact .inl rfl
      · exact .inr ⟨c, by simp [hc], rfl⟩
    have hnp : q ≠ pred + 8 := hbp q hqb' 8 (by omega) (by omega)
    have hns : q ≠ succ + 16 := hbs q hqb' 16 (by omega) (by omega)
    exact (keep _ hqf (by omega) (by omega) (by omega) (by omega) (by omega)
      (by unfold binblocksAddr avAddr; omega) (by omega) (by omega)).symm
  have hnxb : v + sz + d.size = top ∨
      ∃ c ∈ cs₁ ++ ⟨v, sz, true⟩ :: d :: cs₃, c.addr = v + sz + d.size := by
    rcases HD.rest.head_or_top with he | ⟨c, hc, hca⟩
    · exact .inl he
    · exact .inr ⟨c, by simp [hc], hca⟩
  have hnxf : ∀ k, k < 8 → vsaFoot H (v + sz + d.size + 8 + k) := foot_header B hnxb
  have hnpd : v + sz + d.size ≠ pred + 8 := hbp _ hnxb 8 (by omega) (by omega)
  have hnsd : v + sz + d.size ≠ succ + 16 := hbs _ hnxb 16 (by omega) (by omega)
  have h2r' : read64 m' (v + sz + d.size + 8) = some h2 :=
    (keep _ hnxf (by omega) (by omega) (by omega) (by omega) (by omega)
      (by unfold binblocksAddr avAddr; omega) (by omega) (by omega)).trans h2r
  have hdsz : chunkSize hd0 = d.size := hd0s
  obtain ⟨hd', hd'r, hd's, hd'l, hd'p⟩ := hnx hd0 hd0r
  have hdeq : (⟨v + sz, chunkSize hd', prevInuse h2⟩ : Chunk) = d := by
    rw [hd's, hdsz, h2p, ← hda]
  have Wd : ChunkWalk m' (v + sz) top (d :: cs₃) := by
    have w := ChunkWalk.chunk (m := m') (p := v + sz) (h := hd') (h' := h2) hd'r hd'l
      (by rw [hd's, hdsz]; exact hdmin) (by rw [hd's, hdsz]; exact hdal)
      (by rw [hd's, hdsz]; exact h2r') (by rw [hd's, hdsz]; exact W3)
    rwa [hdeq] at w
  have hvhdr : read64 m' (v + 8) = read64 m (v + 8) := by
    have hpv : v + 8 ≠ pred + 16 := by
      rcases hpN with ⟨_, ⟨_, _⟩ | ⟨_, _ | _⟩⟩ <;> (try unfold heapStart at *) <;> (try unfold topAddr avAddr at *) <;> omega
    have hsv : v + 8 ≠ succ + 24 := by
      rcases hsN with ⟨_, ⟨_, _⟩ | ⟨_, _ | _⟩⟩ <;> (try unfold heapStart at *) <;> (try unfold topAddr avAddr at *) <;> omega
    exact keep _ (foot_header B (.inr ⟨_, hV, rfl⟩)) (by omega) (by omega) (by omega) hpv hsv
      (by unfold binblocksAddr avAddr; omega) (by omega) (by omega)
  have WV : ChunkWalk m' v top (⟨v, sz, false⟩ :: d :: cs₃) := by
    have w := ChunkWalk.chunk (m := m') (p := v) (h := hh) (h' := hd') (by rw [hvhdr]; exact hhr)
      hhl (by rw [hhs]; exact HV.min) (by rw [hhs]; exact hsz16) (by rw [hhs]; exact hd'r)
      (by rw [hhs]; exact Wd)
    rwa [hhs, hd'p] at w
  have hwalk : ChunkWalk m' heapStart top (cs₁ ++ ⟨v, sz, false⟩ :: d :: cs₃) := by
    refine W1.extend (fun c hc => ?_) (fun h1 hh1 => ⟨h1, by rw [hvhdr]; exact hh1, rfl⟩) WV
    have := hW1b c hc
    have hc16 := hal c (by simp [hc])
    have hnp : c.addr ≠ pred + 8 := hbp _ (.inr ⟨c, by simp [hc], rfl⟩) 8 (by omega) (by omega)
    have hns : c.addr ≠ succ + 16 := hbs _ (.inr ⟨c, by simp [hc], rfl⟩) 16 (by omega) (by omega)
    unfold heapStart at this
    exact keep _ (foot_header B (.inr ⟨c, by simp [hc], rfl⟩)) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by unfold binblocksAddr avAddr; omega) (by omega) (by omega)
  -- the chunk before `v` is in use
  have hlast : ∀ c ∈ cs₁.getLast?, c.inuse = true := by
    intro c hc
    obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.1 hc
    have hw := HH.walk
    simp only [List.append_assoc, List.singleton_append] at hw
    obtain ⟨⟨hn, hnr, hnp⟩, hnext'⟩ := walk_next_of hw
    have hcv : c.addr + c.size = v := by
      rcases hnext' with ⟨_, h1⟩ | ⟨d', cs', h1, h2⟩
      · cases h1
      · simp only [List.cons.injEq] at h1; rw [← h2, ← h1.1]
    rw [hcv] at hnr
    have := hprev hn hnr
    rw [← hnp]; unfold prevInuse; simp only [beq_iff_eq]; omega
  -- bin `j`'s ring, split at the insertion point
  have hvJ : v ∉ bins j := hvfree j hj0 hj
  have hbinsJ : updBins bins j (pre' ++ v :: post') j = pre' ++ v :: post' := updBins_same _ _ _
  have hbinsK : ∀ k, k ≠ j → updBins bins j (pre' ++ v :: post') k = bins k :=
    fun k h1 => updBins_other _ _ h1
  have hringJ := (binList_iff_ring.1 (HH.bins_list j hj0 hj)).1
  have hneJ := (binList_iff_ring.1 (HH.bins_list j hj0 hj)).2
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.1 hpred
  obtain ⟨zs, hzs⟩ := List.head?_eq_some_iff.1 hsucc
  have hnd := HH.bins_nodup j
  rw [hpos] at hnd
  have hbj_ne : ∀ y ∈ pre' ++ post', y ≠ binAt j := fun y hy => hneJ y (by rw [hpos]; exact hy)
  have hndpre : (binAt j :: pre').Nodup :=
    List.nodup_cons.2 ⟨fun hm => hbj_ne _ (List.mem_append_left _ hm) rfl,
      (List.nodup_append.mp hnd).1⟩
  have hndpost : (post' ++ [binAt j]).Nodup := by
    rw [List.nodup_append]
    refine ⟨(List.nodup_append.mp hnd).2.1, by simp, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton.mp hb]
    exact hbj_ne a (List.mem_append_right _ ha)
  have hdisj : ∀ a ∈ pre', ∀ b ∈ post', a ≠ b := fun a ha b hb =>
    (List.nodup_append.mp hnd).2.2 a ha b hb
  have hnodeJ : ∀ y, y ∈ binAt j :: pre' ∨ y ∈ post' ++ [binAt j] → y = binAt j ∨ y ∈ bins j := by
    rintro y (hy | hy)
    · rcases List.mem_cons.mp hy with h1 | h1
      · exact .inl h1
      · exact .inr (by rw [hpos]; exact List.mem_append_left _ h1)
    · rcases List.mem_append.mp hy with h1 | h1
      · exact .inr (by rw [hpos]; exact List.mem_append_right _ h1)
      · exact .inl (List.mem_singleton.mp h1)
  -- links of nodes away from the written ones
  have Kfd : ∀ k, 0 < k → k < numBins → ∀ y, (y = binAt k ∨ y ∈ bins k) → y ≠ pred →
      fdOf m' y = fdOf m y := by
    intro k hk0 hk y hy hne
    obtain ⟨hy16, ⟨_, hyg1, hyg2⟩ | ⟨hylo, hyl, hyf⟩⟩ := hnodeLoc k hk0 hk y hy
    · have hs : y + 16 ≠ succ + 24 := by omega
      exact Kg _ (fun o ho => .inl ⟨by omega, by omega⟩) (by omega) (by omega)
        (by intro he; exact hne (by omega)) hs (by unfold binblocksAddr avAddr; omega)
    · have hs : y + 16 ≠ succ + 24 := by omega
      exact keep _ (fun o ho => by
          have := hyf (16 + o) (by omega) (by omega)
          rwa [show y + (16 + o) = y + 16 + o by omega] at this) (by omega)
        (by omega) (by omega) (by intro he; exact hne (by omega)) hs
        (by unfold binblocksAddr avAddr; omega) (by omega) (by omega)
  have Kbk : ∀ k, 0 < k → k < numBins → ∀ y, (y = binAt k ∨ y ∈ bins k) → y ≠ succ →
      bkOf m' y = bkOf m y := by
    intro k hk0 hk y hy hne
    obtain ⟨hy16, ⟨_, hyg1, hyg2⟩ | ⟨hylo, hyl, hyf⟩⟩ := hnodeLoc k hk0 hk y hy
    · have hp : y + 24 ≠ pred + 16 := by omega
      exact Kg _ (fun o ho => .inl ⟨by omega, by omega⟩) (by omega) (by omega) hp
        (by intro he; exact hne (by omega)) (by unfold binblocksAddr avAddr; omega)
    · have hp : y + 24 ≠ pred + 16 := by omega
      exact keep _ (fun o ho => by
          have := hyf (24 + o) (by omega) (by omega)
          rwa [show y + (24 + o) = y + 24 + o by omega] at this) (by omega)
        (by omega) (by omega) hp (by intro he; exact hne (by omega))
        (by unfold binblocksAddr avAddr; omega) (by omega) (by omega)
  have ring_j : Ring m' (binAt j) (pre' ++ v :: post') := by
    have hold : Ring m (binAt j) (bins j) := hringJ
    rw [hpos] at hold
    unfold Ring at hold ⊢
    have e1 : binAt j :: (pre' ++ post') ++ [binAt j] = ys ++ pred :: succ :: zs := by
      rw [show binAt j :: (pre' ++ post') ++ [binAt j] = (binAt j :: pre') ++ (post' ++ [binAt j])
        by simp, hys, hzs]; simp
    have e2 : binAt j :: (pre' ++ v :: post') ++ [binAt j] = ys ++ pred :: v :: succ :: zs := by
      rw [show binAt j :: (pre' ++ v :: post') ++ [binAt j] =
        (binAt j :: pre') ++ v :: (post' ++ [binAt j]) by simp, hys, hzs]; simp
    rw [e1] at hold
    rw [e2]
    refine links_link hold hfdP hbkV hfdV hbkS fun a b hab => ?_
    rcases hab with hab | hab
    · rw [← hys] at hab
      have ⟨ha, hb⟩ := pair_mem hab
      have hane : a ≠ pred := pair_ne_last (hys ▸ hab) (hys ▸ hndpre)
      have hbne : b ≠ binAt j := pair_ne_head hab hndpre
      refine ⟨Kfd j hj0 hj a (hnodeJ a (.inl ha)) hane, Kbk j hj0 hj b (hnodeJ b (.inl hb)) ?_⟩
      intro hbs
      have hbpre : b ∈ pre' := by
        rcases List.mem_cons.mp hb with h1 | h1
        · exact absurd h1 hbne
        · exact h1
      rcases List.mem_append.mp (hzs ▸ List.mem_cons_self : succ ∈ post' ++ [binAt j]) with h1 | h1
      · exact hdisj b hbpre succ h1 hbs
      · exact hbne (hbs.trans (List.mem_singleton.mp h1))
    · rw [← hzs] at hab
      have ⟨ha, hb⟩ := pair_mem hab
      have hbne : b ≠ succ := pair_ne_head (hzs ▸ hab) (hzs ▸ hndpost)
      have hane : a ≠ binAt j := pair_ne_last hab hndpost
      refine ⟨Kfd j hj0 hj a (hnodeJ a (.inr ha)) ?_, Kbk j hj0 hj b (hnodeJ b (.inr hb)) hbne⟩
      intro hap
      have hapost : a ∈ post' := by
        rcases List.mem_append.mp ha with h1 | h1
        · exact h1
        · exact absurd (List.mem_singleton.mp h1) hane
      have := List.mem_of_getLast? hpred
      rcases List.mem_cons.mp this with h1 | h1
      · exact hane (hap.trans h1)
      · exact hdisj pred h1 a hapost hap.symm
  -- nodes of other bins are none of the written nodes
  have hoNe : ∀ k, 0 < k → k < numBins → k ≠ j → ∀ y, (y = binAt k ∨ y ∈ bins k) →
      y ≠ pred ∧ y ≠ succ := by
    intro k hk0 hk hkj y hy
    have hne : ∀ z, (z = binAt j ∨ z ∈ bins j) → y ≠ z := by
      rintro z (rfl | hz) he
      · rcases hy with rfl | hy
        · exact hkj (by unfold binAt avAddr at he; omega)
        · obtain ⟨c, hc, rfl, _⟩ := HH.member hk0 hk hy
          have := (hcb c hc).1; unfold heapStart at this; omega
      · subst he
        rcases hy with rfl | hy
        · obtain ⟨c, hc, hca, _⟩ := HH.member hj0 hj hz
          have := (hcb c hc).1; have := binAt_geo k hk; unfold heapStart at *; omega
        · exact hkj (HH.bin_unique hk0 hk hj0 hj hy hz)
    exact ⟨hne pred hpm, hne succ hsm⟩
  have hbinlist : ∀ k, 0 < k → k < numBins →
      BinList m' k (updBins bins j (pre' ++ v :: post') k) := by
    intro k hk0 hk
    by_cases hkj : k = j
    · subst hkj
      rw [hbinsJ]
      refine binList_iff_ring.2 ⟨ring_j, ?_⟩
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact hbj_ne y (List.mem_append_left _ hy)
      · rcases List.mem_cons.mp hy with rfl | hy
        · have := binAt_geo k hk; omega
        · exact hbj_ne y (List.mem_append_right _ hy)
    · rw [hbinsK k hkj]
      have hold := binList_iff_ring.1 (HH.bins_list k hk0 hk)
      rw [binList_iff_ring]
      refine ⟨?_, hold.2⟩
      have hr := hold.1
      unfold Ring at hr ⊢
      refine hr.transport fun a b hab => ?_
      have ⟨ha, hb⟩ := pair_mem hab
      have hnode : ∀ y ∈ binAt k :: bins k ++ [binAt k], y = binAt k ∨ y ∈ bins k := by
        intro y hy
        simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
          or_false] at hy
        rcases hy with h1 | h1 | h1
        · exact .inl h1
        · exact .inr h1
        · exact .inl h1
      exact ⟨Kfd k hk0 hk a (hnode a ha) (hoNe k hk0 hk hkj a (hnode a ha)).1,
        Kbk k hk0 hk b (hnode b hb) (hoNe k hk0 hk hkj b (hnode b hb)).2⟩
  -- globals
  have gAv : ∀ w, 0x8001ad10 ≤ w → w + 8 ≤ 0x8001b520 → ∀ k, k < 8 → allocGlobal (w + k) :=
    fun w h1 h2 k hk => .inl ⟨by omega, by omega⟩
  have gHi : ∀ w, 0x8001b990 ≤ w → w + 8 ≤ 0x8001b9b0 → ∀ k, k < 8 → allocGlobal (w + k) :=
    fun w h1 h2 k hk => .inr (.inr (.inr (.inl ⟨by omega, by omega⟩)))
  have kTop : read64 m' topAddr = read64 m topAddr := by
    refine Kg _ (gAv _ (by unfold topAddr avAddr; omega) (by unfold topAddr avAddr; omega))
      (by unfold topAddr avAddr; omega) (by unfold topAddr avAddr; omega) ?_ ?_
      (by unfold topAddr binblocksAddr avAddr; omega)
    · rcases hpN with ⟨_, ⟨_, _⟩ | ⟨_, _ | _⟩⟩ <;> (try unfold heapStart at *) <;> (try unfold topAddr avAddr at *) <;> omega
    · rcases hsN with ⟨_, ⟨_, _⟩ | ⟨_, _ | _⟩⟩ <;> (try unfold heapStart at *) <;> (try unfold topAddr avAddr at *) <;> omega
  have hVm : (⟨v, sz, false⟩ : Chunk) ∈ cs₁ ++ ⟨v, sz, false⟩ :: d :: cs₃ := by simp
  refine ⟨⟨{ sbrk_base := ?_, brk := ?_, brk_le := HH.brk_le, top_ptr := kTop.trans HH.top_ptr
             top_le := HH.top_le, top_size := HH.top_size, top_header := ?_
             top_pad := ?_, max_sbrked := ?_, mallinfo := ?_, first_prev := ?_
             walk := hwalk
             coalesced := coal_release HH.coalesced hlast (fun d' hd' => by
               simp at hd'; rw [← hd']; exact hdin)
             footer := ?_
             bins_list := hbinlist, bins_nodup := ?_
             bin_free := ?_, free_binned := ?_, remainder := ?_
             binblocks_present := by rw [hbbr]; rfl
             binblocks := ?_
             live := ?_, exact := ?_ }, B.top_room⟩, hpage, fun bb hbb => by
    rw [hbbr] at hbb; cases hbb; exact hbblt⟩
  · rw [Kg' _ (fun k hk => .inr (.inr (.inl ⟨by unfold sbrkBaseAddr; omega,
      by unfold sbrkBaseAddr; omega⟩))) (by unfold sbrkBaseAddr; omega)
      (by unfold sbrkBaseAddr; omega) (by unfold sbrkBaseAddr; omega)]
    exact HH.sbrk_base
  · rw [Kg' _ (gHi _ (by unfold brkAddr; omega) (by unfold brkAddr; omega))
      (by unfold brkAddr; omega) (by unfold brkAddr; omega) (by unfold brkAddr; omega)]
    exact HH.brk
  · have hnp : top ≠ pred + 8 := hbp _ (.inl rfl) 8 (by omega) (by omega)
    have hns : top ≠ succ + 16 := hbs _ (.inl rfl) 16 (by omega) (by omega)
    have htb : v + sz + d.size ≤ top := hW3le
    rw [keep _ (foot_header B (.inl rfl)) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by unfold binblocksAddr avAddr; omega) (by omega) (by omega)]
    exact HH.top_header
  · rw [Kg' _ (gHi _ (by unfold topPadAddr; omega) (by unfold topPadAddr; omega))
      (by unfold topPadAddr; omega) (by unfold topPadAddr; omega) (by unfold topPadAddr; omega)]
    exact HH.top_pad
  · rw [Kg' _ (gHi _ (by unfold maxSbrkedAddr; omega) (by unfold maxSbrkedAddr; omega))
      (by unfold maxSbrkedAddr; omega) (by unfold maxSbrkedAddr; omega)
      (by unfold maxSbrkedAddr; omega)]
    exact HH.max_sbrked
  · rw [Kg' _ (fun k hk => .inr (.inr (.inr (.inr (.inr ⟨by unfold mallinfoAddr; omega,
      by unfold mallinfoAddr; omega⟩))))) (by unfold mallinfoAddr; omega)
      (by unfold mallinfoAddr; omega) (by unfold mallinfoAddr; omega)]
    exact HH.mallinfo
  · rcases W1.head_or_top with he | ⟨c, hc, hca⟩
    · rw [he, hvhdr]; exact he ▸ HH.first_prev
    · have hw := hwalk
      rw [← hca]
      have := hW1b c hc
      have hc16 := hal c (by simp [hc])
      have hnp : c.addr ≠ pred + 8 := hbp _ (.inr ⟨c, by simp [hc], rfl⟩) 8 (by omega) (by omega)
      have hns : c.addr ≠ succ + 16 := hbs _ (.inr ⟨c, by simp [hc], rfl⟩) 16 (by omega) (by omega)
      unfold heapStart at this
      rw [keep _ (foot_header B (.inr ⟨c, by simp [hc], rfl⟩)) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by unfold binblocksAddr avAddr; omega) (by omega) (by omega), hca]
      exact HH.first_prev
  · intro c hc hf
    rcases (hmemL' c).1 hc with h1 | rfl | rfl | h1
    · have hcL : c ∈ cs₁ ++ ⟨v, sz, true⟩ :: d :: cs₃ := by simp [h1]
      have := hW1b c h1
      have hc16 := hal c hcL
      have hcs := walk_sizes HH.walk c hcL
      have hnp : c.addr + c.size ≠ pred + 16 := hbp _ (HH.end_bnd hcL) 16 (by omega) (by omega)
      have hns : c.addr + c.size ≠ succ + 24 := hbs _ (HH.end_bnd hcL) 24 (by omega) (by omega)
      unfold heapStart at this
      rw [keep _ (foot_free B hcL hf).2 (by omega) (by omega) (by omega) hnp hns
        (by unfold binblocksAddr avAddr; omega) (by omega) (by omega)]
      exact HH.footer c hcL hf
    · exact hft
    · rw [hdin] at hf; cases hf
    · have hcL : c ∈ cs₁ ++ ⟨v, sz, true⟩ :: d :: cs₃ := by simp [h1]
      have := hW3b c h1
      have hc16 := hal c hcL
      have hcs := walk_sizes HH.walk c hcL
      have hnp : c.addr + c.size ≠ pred + 16 := hbp _ (HH.end_bnd hcL) 16 (by omega) (by omega)
      have hns : c.addr + c.size ≠ succ + 24 := hbs _ (HH.end_bnd hcL) 24 (by omega) (by omega)
      rw [keep _ (foot_free B hcL hf).2 (by omega) (by omega) (by omega) hnp hns
        (by unfold binblocksAddr avAddr; omega) (by omega) (by omega)]
      exact HH.footer c hcL hf
  · intro k
    by_cases hkj : k = j
    · subst hkj; rw [hbinsJ]
      rw [List.nodup_append]
      have hvpost : v ∉ post' := fun hm => hvJ (by rw [hpos]; exact List.mem_append_right _ hm)
      refine ⟨(List.nodup_append.mp hnd).1,
        List.nodup_cons.2 ⟨hvpost, (List.nodup_append.mp hnd).2.1⟩, ?_⟩
      intro a ha b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact fun he => hvJ (by rw [hpos, ← he]; exact List.mem_append_left _ ha)
      · exact hdisj a ha b hb
    · rw [hbinsK k hkj]; exact HH.bins_nodup k
  · intro k q hk0 hk hq
    by_cases hkj : k = j
    · subst hkj; rw [hbinsJ] at hq
      rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨c, hc, h1, h2, h3⟩ := HH.bin_free k q hk0 hk (by rw [hpos]; exact List.mem_append_left _ hq)
        exact ⟨c, hfree_new c hc h2, h1, h2, h3⟩
      · rcases List.mem_cons.mp hq with rfl | hq
        · exact ⟨_, hVm, rfl, rfl, fun h1 => hidx h1⟩
        · obtain ⟨c, hc, h1, h2, h3⟩ := HH.bin_free k q hk0 hk (by rw [hpos]; exact List.mem_append_right _ hq)
          exact ⟨c, hfree_new c hc h2, h1, h2, h3⟩
    · rw [hbinsK k hkj] at hq
      obtain ⟨c, hc, h1, h2, h3⟩ := HH.bin_free k q hk0 hk hq
      exact ⟨c, hfree_new c hc h2, h1, h2, h3⟩
  · have hjmem : ∀ y, y ∈ pre' ++ v :: post' ↔ y = v ∨ y ∈ bins j := by
      intro y; rw [hpos]; simp only [List.mem_append, List.mem_cons]
      constructor
      · rintro (h | h | h)
        · exact .inr (.inl h)
        · exact .inl h
        · exact .inr (.inr h)
      · rintro (h | h | h)
        · exact .inr (.inl h)
        · exact .inl h
        · exact .inr (.inr h)
    intro c hc hf
    rcases (hmemL' c).1 hc with h1 | rfl | rfl | h1
    rotate_left
    · refine ⟨j, hj0, hj, by rw [hbinsJ, hjmem]; exact .inl rfl, ?_⟩
      intro k hk0 hk hmem
      by_cases hkj : k = j
      · exact hkj
      · rw [hbinsK k hkj] at hmem; exact absurd hmem (hvfree k hk0 hk)
    · rw [hdin] at hf; cases hf
    all_goals
      have hcL : c ∈ cs₁ ++ ⟨v, sz, true⟩ :: d :: cs₃ := by simp [h1]
      have hcv : c.addr ≠ v := by
        rcases hfree_loc c hcL hf with ⟨_, h2⟩ | ⟨_, h2⟩
        · have := (hcb c hcL).2.2; omega
        · omega
      obtain ⟨k, hk0, hk, hmem, huniq⟩ := HH.free_binned c hcL hf
      refine ⟨k, hk0, hk, ?_, ?_⟩
      · by_cases hkj : k = j
        · subst hkj; rw [hbinsJ, hjmem]; exact .inr hmem
        · rw [hbinsK k hkj]; exact hmem
      · intro k' hk0' hk' hmem'
        by_cases hkj' : k' = j
        · subst hkj'; rw [hbinsJ, hjmem] at hmem'
          rcases hmem' with he | hmem'
          · exact absurd he hcv
          · exact huniq k' hk0' hk' hmem'
        · rw [hbinsK k' hkj'] at hmem'; exact huniq k' hk0' hk' hmem'
  · by_cases h1j : j = 1
    · subst h1j; rw [hbinsJ]
      have h1 := hj1 rfl
      rw [hpos] at h1
      have hp : pre' = [] := (List.append_eq_nil_iff.1 h1).1
      have hq : post' = [] := (List.append_eq_nil_iff.1 h1).2
      subst hp hq; simp
    · rw [hbinsK 1 (fun he => h1j he.symm)]; exact HH.remainder
  · intro bb hbb k hk1 hk hne
    rw [hbbr] at hbb; cases hbb
    by_cases hkj : k = j
    · subst hkj; exact hbbset hk1
    · rw [hbinsK k hkj] at hne
      obtain ⟨bb0, hbb0⟩ := Option.isSome_iff_exists.1 HH.binblocks_present
      exact hbbkeep bb0 hbb0 (k / 4) (HH.binblocks bb0 hbb0 k hk1 hk hne)
  · intro e he
    obtain ⟨c, hc, hu, h1, h2⟩ := HH.exact e he he
    rcases (hmemL c).1 hc with h3 | rfl | rfl | h3
    · exact ⟨c, by simp [h3], hu, by omega, by omega⟩
    · exact absurd h1.symm (hno e he)
    · exact ⟨c, by simp, hu, by omega, by omega⟩
    · exact ⟨c, by simp [h3], hu, by omega, by omega⟩
  · intro e he hr
    obtain ⟨c, hc, hu, h1, h2⟩ := HH.exact e he hr
    rcases (hmemL c).1 hc with h3 | rfl | rfl | h3
    · exact ⟨c, by simp [h3], hu, h1, h2⟩
    · exact absurd h1.symm (hno e he)
    · exact ⟨c, by simp, hu, h1, h2⟩
    · exact ⟨c, by simp [h3], hu, h1, h2⟩

end VsaIris.VsaHeap
