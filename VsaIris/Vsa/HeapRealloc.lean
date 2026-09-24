import VsaIris.Vsa.HeapFree

/-!
# Heap edits for `_realloc_r`

`_realloc_r` resizes in-use chunks in place. Besides the edits `free` uses
(`PHeapAt.unlink`, `absorb`, `coalPrev`), it cuts an in-use chunk in two
(`PHeapAt.cut`, the tail holding a zero-length block that `_free_r` then
releases), grows the last chunk into the top (`PHeapAt.growTop`), and changes
the length of a live block within its chunk (`PHeapAt.reblock`).
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.MallocFast VsaIris.Sym

/-- Splitting a chunk into two in-use chunks keeps coalescing. -/
theorem coal_cut {a b c : Chunk} (ha : a.inuse = true) (hb : b.inuse = true) :
    ∀ {cs₁ cs₂ : List Chunk}, Coal (cs₁ ++ c :: cs₂) → Coal (cs₁ ++ a :: b :: cs₂)
  | [], [], _ => by
    simp only [List.nil_append]
    exact coal_cons_cons.2 ⟨.inl ha, coal_single b⟩
  | [], d :: cs₂, h => by
    simp only [List.nil_append] at h ⊢
    exact coal_cons_cons.2 ⟨.inl ha, coal_cons_cons.2 ⟨.inl hb, (coal_cons_cons.1 h).2⟩⟩
  | [x], cs₂, h => by
    simp only [List.cons_append, List.nil_append] at h ⊢
    obtain ⟨_, h'⟩ := coal_cons_cons.1 h
    exact coal_cons_cons.2 ⟨.inr ha, coal_cut ha hb (cs₁ := []) h'⟩
  | x :: y :: cs₁, cs₂, h => by
    simp only [List.cons_append] at h ⊢
    obtain ⟨hx, h'⟩ := coal_cons_cons.1 h
    exact coal_cons_cons.2 ⟨hx, coal_cut ha hb (cs₁ := y :: cs₁) h'⟩

/-- A live extent sits at the payload start of an in-use chunk, and the chunk
holding an address inside another chunk's range is that chunk. -/
theorem exact_in {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} (HH : HeapAt m H (fun e => e ∈ H) top brkv chunks bins)
    {e : Nat × Nat} (he : e ∈ H) {X : Chunk} (hX : X ∈ chunks)
    (h1 : X.addr + 16 ≤ e.1) (h2 : e.1 < X.addr + X.size) :
    X.inuse = true ∧ X.addr + 16 = e.1 ∧ e.2 + 8 ≤ X.size := by
  obtain ⟨c, hc, hu, hca, hcn⟩ := HH.exact e he he
  have hcb := HH.walk.chunk_bounds c hc
  have hXb := HH.walk.chunk_bounds X hX
  rcases HH.walk.chunk_sep c hc X hX with rfl | h3 | h3
  · exact ⟨hu, hca, hcn⟩
  · omega
  · omega

/-- **Cut an in-use chunk in two.** The in-use chunk `x` of size `a + b`
becomes the in-use chunks `x` (size `a`, its `PREV_INUSE` kept) and `x + a`
(size `b`), which holds the zero-length block `(x + a + 16, 0)` for `free` to
release. A live block at `x + 16` fits in the first part (`hfit`). -/
theorem PHeapAt.cut {m m' : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {cs₁ cs₂ : List Chunk} {bins : Nat → List Nat} {x a b : Nat}
    (h : PHeapAt m H top brkv (cs₁ ++ ⟨x, a + b, true⟩ :: cs₂) bins)
    (ha16 : a % 16 = 0) (ha32 : 32 ≤ a) (hb32 : 32 ≤ b)
    (hfit : ∀ e ∈ H, e.1 = x + 16 → e.2 + 8 ≤ a)
    {h' : Nat} (hhdr : read64 m' (x + 8) = some h') (hsz : chunkSize h' = a)
    (hlow : h' % 4 < 2) (hpi : ∀ h0, read64 m (x + 8) = some h0 → prevInuse h' = prevInuse h0)
    {hy : Nat} (hyr : read64 m' (x + a + 8) = some hy) (hys : chunkSize hy = b)
    (hyl : hy % 4 < 2) (hyp : prevInuse hy = true)
    (hag : ∀ w, vsaFoot H w → ¬ (x + 8 ≤ w ∧ w < x + 16) → ¬ (x + a + 8 ≤ w ∧ w < x + a + 16) →
      m'[w]? = m[w]?) :
    PHeapAt m' ((x + a + 16, 0) :: H) top brkv (cs₁ ++ ⟨x, a, true⟩ :: ⟨x + a, b, true⟩ :: cs₂) bins := by
  obtain ⟨B, hpage, hbbl⟩ := h
  have HH := B.heap
  obtain ⟨hal, htop16⟩ := HH.aligned
  have hlo := HH.walk.le
  have hcb := HH.walk.chunk_bounds
  have hbrk := HH.brk_le
  have htle := HH.top_le
  have hX : (⟨x, a + b, true⟩ : Chunk) ∈ cs₁ ++ ⟨x, a + b, true⟩ :: cs₂ := by simp
  have hXb := hcb _ hX
  have hx16 : x % 16 = 0 := hal _ hX
  simp only at hXb hx16
  unfold heapStart at hlo hXb
  -- the walk around `x`
  obtain ⟨mid, W1, W2⟩ := HH.walk.append_inv
  have HX := walkHead W2
  have hmid : x = mid := HX.addr
  subst hmid
  obtain ⟨h3, h3r, h3p⟩ := HX.next
  simp only at h3r h3p
  have hW1b := W1.chunk_bounds
  have hW3b : ∀ c ∈ cs₂, x + a + b ≤ c.addr ∧ c.addr + c.size ≤ top ∧ 32 ≤ c.size := by
    have := HX.rest.chunk_bounds; simpa [Nat.add_assoc] using this
  have hab16 : (a + b) % 16 = 0 := HX.al
  -- words the cut does not write
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
    have R := HX.rest
    simp only at R
    rw [show x + (a + b) = x + a + b by omega] at R
    refine R.transport_headers fun q hq => (keep _ ?_ ?_ ?_).symm
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
    have hq : x + a + b = top ∨ ∃ c ∈ cs₁ ++ ⟨x, a + b, true⟩ :: cs₂, c.addr = x + a + b := by
      have R := HX.rest
      simp only at R
      rw [show x + (a + b) = x + a + b by omega] at R
      rcases R.head_or_top with he | ⟨c, hc, hca⟩
      · exact .inl he
      · exact .inr ⟨c, by simp [hc], hca⟩
    exact foot_header B hq
  have h3r' : read64 m' (x + a + b + 8) = some h3 := by
    rw [keep _ hnxf (.inr (by omega)) (.inr (by omega)), show x + a + b + 8 = x + (a + b) + 8 by omega]
    exact h3r
  have WY : ChunkWalk m' (x + a) top (⟨x + a, b, true⟩ :: cs₂) := by
    have w := ChunkWalk.chunk (m := m') (p := x + a) (h := hy) (h' := h3) hyr hyl
      (by rw [hys]; omega) (by rw [hys]; omega) (by rw [hys]; exact h3r') (by rw [hys]; exact W3)
    rwa [hys, h3p] at w
  have WX : ChunkWalk m' x top (⟨x, a, true⟩ :: ⟨x + a, b, true⟩ :: cs₂) := by
    have w := ChunkWalk.chunk (m := m') (p := x) (h := h') (h' := hy) hhdr hlow
      (by rw [hsz]; omega) (by rw [hsz]; omega) (by rw [hsz]; exact hyr) (by rw [hsz]; exact WY)
    rwa [hsz, hyp] at w
  have hwalk : ChunkWalk m' heapStart top (cs₁ ++ ⟨x, a, true⟩ :: ⟨x + a, b, true⟩ :: cs₂) := by
    refine W1.extend (fun c hc => keep _ (foot_header B (.inr ⟨c, by simp [hc], rfl⟩)) ?_ ?_)
      (fun h1 hh1 => ⟨h', hhdr, hpi h1 hh1⟩) WX
    · have := hW1b c hc; exact .inl (by omega)
    · have := hW1b c hc; exact .inl (by omega)
  -- the old and new chunk lists
  have hmemL : ∀ c, c ∈ cs₁ ++ ⟨x, a + b, true⟩ :: cs₂ ↔
      c ∈ cs₁ ∨ c = ⟨x, a + b, true⟩ ∨ c ∈ cs₂ := by
    intro c; simp only [List.mem_append, List.mem_cons]
  have hmemL' : ∀ c, c ∈ cs₁ ++ ⟨x, a, true⟩ :: ⟨x + a, b, true⟩ :: cs₂ ↔
      c ∈ cs₁ ∨ c = ⟨x, a, true⟩ ∨ c = ⟨x + a, b, true⟩ ∨ c ∈ cs₂ := by
    intro c; simp only [List.mem_append, List.mem_cons]
  have hfree_loc : ∀ c ∈ cs₁ ++ ⟨x, a + b, true⟩ :: cs₂, c.inuse = false →
      (c ∈ cs₁ ∧ c.addr + c.size ≤ x) ∨ (c ∈ cs₂ ∧ x + a + b ≤ c.addr) := by
    intro c hc hf
    rcases (hmemL c).1 hc with h1 | rfl | h1
    · exact .inl ⟨h1, (hW1b c h1).2.1⟩
    · cases hf
    · exact .inr ⟨h1, (hW3b c h1).1⟩
  have hfree_new : ∀ c ∈ cs₁ ++ ⟨x, a + b, true⟩ :: cs₂, c.inuse = false →
      c ∈ cs₁ ++ ⟨x, a, true⟩ :: ⟨x + a, b, true⟩ :: cs₂ := by
    intro c hc hf
    rcases hfree_loc c hc hf with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp [h1]
  have hfree_old : ∀ c ∈ cs₁ ++ ⟨x, a, true⟩ :: ⟨x + a, b, true⟩ :: cs₂, c.inuse = false →
      c ∈ cs₁ ++ ⟨x, a + b, true⟩ :: cs₂ := by
    intro c hc hf
    rcases (hmemL' c).1 hc with h1 | rfl | rfl | h1
    · simp [h1]
    · cases hf
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
  have hXm : (⟨x, a, true⟩ : Chunk) ∈ cs₁ ++ ⟨x, a, true⟩ :: ⟨x + a, b, true⟩ :: cs₂ := by simp
  have hYm : (⟨x + a, b, true⟩ : Chunk) ∈ cs₁ ++ ⟨x, a, true⟩ :: ⟨x + a, b, true⟩ :: cs₂ := by simp
  -- every live extent at the payload start of a chunk of the new list
  have hex : ∀ e ∈ H, ∃ c ∈ cs₁ ++ ⟨x, a, true⟩ :: ⟨x + a, b, true⟩ :: cs₂,
      c.inuse = true ∧ c.addr + 16 = e.1 ∧ e.2 + 8 ≤ c.size := by
    intro e he
    obtain ⟨c, hc, hu, h1, h2⟩ := HH.exact e he he
    rcases (hmemL c).1 hc with h3 | rfl | h3
    · exact ⟨c, by simp [h3], hu, h1, h2⟩
    · exact ⟨_, hXm, rfl, h1, hfit e he h1.symm⟩
    · exact ⟨c, by simp [h3], hu, h1, h2⟩
  refine ⟨⟨{ sbrk_base := ?_, brk := ?_, brk_le := HH.brk_le, top_ptr := kTop.trans HH.top_ptr
             top_le := HH.top_le, top_size := HH.top_size, top_header := ?_
             top_pad := ?_, max_sbrked := ?_, mallinfo := ?_, first_prev := ?_
             walk := hwalk, coalesced := coal_cut rfl rfl HH.coalesced, footer := ?_
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
      obtain ⟨hh, hhr, _, _⟩ := HX.hdr
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
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨_, hYm, rfl, by simp only; omega, by simp only; omega⟩
    · obtain ⟨c, hc, hu, h1, h2⟩ := hex e he
      exact ⟨c, hc, hu, by omega, by omega⟩
  · intro e he _
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨_, hYm, rfl, rfl, by simp only; omega⟩
    · exact hex e he

/-- Replacing a chunk by one with the same flag keeps coalescing. -/
theorem coal_swap {c c' : Chunk} (hc : c'.inuse = c.inuse) :
    ∀ {cs₁ cs₂ : List Chunk}, Coal (cs₁ ++ c :: cs₂) → Coal (cs₁ ++ c' :: cs₂)
  | [], [], _ => by simpa using coal_single c'
  | [], d :: cs₂, h => by
    simp only [List.nil_append] at h ⊢
    obtain ⟨h1, h2⟩ := coal_cons_cons.1 h
    exact coal_cons_cons.2 ⟨by rw [hc]; exact h1, h2⟩
  | [x], cs₂, h => by
    simp only [List.cons_append, List.nil_append] at h ⊢
    obtain ⟨h1, h'⟩ := coal_cons_cons.1 h
    exact coal_cons_cons.2 ⟨by rw [hc]; exact h1, coal_swap hc (cs₁ := []) h'⟩
  | x :: y :: cs₁, cs₂, h => by
    simp only [List.cons_append] at h ⊢
    obtain ⟨hx, h'⟩ := coal_cons_cons.1 h
    exact coal_cons_cons.2 ⟨hx, coal_swap hc (cs₁ := y :: cs₁) h'⟩

/-- **A live block changes length within its chunk.** -/
theorem PHeapAt.reblock {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} {q n n' : Nat} (h : PHeapAt m ((q, n) :: H) top brkv chunks bins)
    {c : Chunk} (hc : c ∈ chunks) (hu : c.inuse = true) (hca : c.addr + 16 = q)
    (hn : n' + 8 ≤ c.size) : PHeapAt m ((q, n') :: H) top brkv chunks bins := by
  obtain ⟨B, hpage, hbbl⟩ := h
  have HH := B.heap
  refine ⟨⟨{ HH with live := fun e he => ?_, exact := fun e he _ => ?_ }, B.top_room⟩, hpage, hbbl⟩
  · rcases List.mem_cons.mp he with rfl | he
    · exact ⟨c, hc, hu, by simp only; omega, by simp only; omega⟩
    · exact HH.live e (List.mem_cons_of_mem _ he)
  · rcases List.mem_cons.mp he with rfl | he
    · exact ⟨c, hc, hu, hca, hn⟩
    · exact HH.exact e (List.mem_cons_of_mem _ he) (List.mem_cons_of_mem _ he)

/-- **The last chunk grows into the top.** The in-use chunk `x` of size `a`
just below the top takes `d` more bytes; the top moves up by `d` with its
header rewritten, and still has room below the break. -/
theorem PHeapAt.growTop {m m' : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {cs₁ : List Chunk} {bins : Nat → List Nat} {x a d : Nat}
    (h : PHeapAt m H top brkv (cs₁ ++ [⟨x, a, true⟩]) bins)
    (hd16 : d % 16 = 0) (hroom : x + a + d + 16 ≤ brkv)
    {h' : Nat} (hhdr : read64 m' (x + 8) = some h') (hsz : chunkSize h' = a + d)
    (hlow : h' % 4 < 2) (hpi : ∀ h0, read64 m (x + 8) = some h0 → prevInuse h' = prevInuse h0)
    (htp : read64 m' topAddr = some (x + a + d))
    (hth : read64 m' (x + a + d + 8) = some (brkv - (x + a + d) + 1))
    (hag : ∀ w, vsaFoot H w → ¬ (x + 8 ≤ w ∧ w < x + 16) → ¬ (topAddr ≤ w ∧ w < topAddr + 8) →
      ¬ (x + a + d + 8 ≤ w ∧ w < x + a + d + 16) → m'[w]? = m[w]?) :
    PHeapAt m' H (x + a + d) brkv (cs₁ ++ [⟨x, a + d, true⟩]) bins := by
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
  subst hxa
  have hW1b := W1.chunk_bounds
  have keep : ∀ w, (∀ k, k < 8 → vsaFoot H (w + k)) → (w + 8 ≤ x + 8 ∨ x + 16 ≤ w) →
      (w + 8 ≤ topAddr ∨ topAddr + 8 ≤ w) → (w + 8 ≤ x + a + d + 8 ∨ x + a + d + 16 ≤ w) →
      read64 m' w = read64 m w := by
    intro w hf h1 h2 h3
    exact read64_keep fun k hk => hag _ (hf k hk) (by omega) (by omega) (by omega)
  have Kg : ∀ w, (∀ k, k < 8 → allocGlobal (w + k)) → (w + 8 ≤ topAddr ∨ topAddr + 8 ≤ w) →
      read64 m' w = read64 m w := by
    intro w hg ht
    have := hg 0 (by omega); have := hg 7 (by omega)
    unfold allocGlobal InRange at *
    exact keep w (fun k hk => .inl (hg k hk)) (.inl (by omega)) ht (.inl (by omega))
  have hthp : prevInuse (brkv - (x + a + d) + 1) = true := by
    unfold prevInuse; rw [beq_iff_eq]; omega
  have WX : ChunkWalk m' x (x + a + d) [⟨x, a + d, true⟩] := by
    have w := ChunkWalk.chunk (m := m') (p := x) (h := h') (h' := brkv - (x + a + d) + 1) hhdr hlow
      (by rw [hsz]; omega) (by rw [hsz]; omega) (by rw [hsz, ← Nat.add_assoc]; exact hth)
      (by rw [hsz, ← Nat.add_assoc]; exact ChunkWalk.top)
    rwa [hsz, hthp] at w
  have hwalk : ChunkWalk m' heapStart (x + a + d) (cs₁ ++ [⟨x, a + d, true⟩]) :=
    W1.extend (fun c hc => keep _ (foot_header B (.inr ⟨c, by simp [hc], rfl⟩))
        (by have := hW1b c hc; exact .inl (by omega))
        (by have := hW1b c hc; unfold topAddr avAddr; unfold heapStart at this; omega)
        (by have := hW1b c hc; exact .inl (by omega)))
      (fun h1 hh1 => ⟨h', hhdr, hpi h1 hh1⟩) WX
  have hmemL : ∀ c, c ∈ cs₁ ++ [⟨x, a, true⟩] ↔ c ∈ cs₁ ∨ c = ⟨x, a, true⟩ := by
    intro c; simp only [List.mem_append, List.mem_singleton]
  have hmemL' : ∀ c, c ∈ cs₁ ++ [⟨x, a + d, true⟩] ↔ c ∈ cs₁ ∨ c = ⟨x, a + d, true⟩ := by
    intro c; simp only [List.mem_append, List.mem_singleton]
  have hfree_in : ∀ c ∈ cs₁ ++ [⟨x, a, true⟩], c.inuse = false → c ∈ cs₁ := by
    intro c hc hf
    rcases (hmemL c).1 hc with h1 | rfl
    · exact h1
    · cases hf
  have hfree_in' : ∀ c ∈ cs₁ ++ [⟨x, a + d, true⟩], c.inuse = false → c ∈ cs₁ := by
    intro c hc hf
    rcases (hmemL' c).1 hc with h1 | rfl
    · exact h1
    · cases hf
  have hin_old : ∀ c ∈ cs₁, c ∈ cs₁ ++ [⟨x, a, true⟩] := fun c hc => by simp [hc]
  have hin_new : ∀ c ∈ cs₁, c ∈ cs₁ ++ [⟨x, a + d, true⟩] := fun c hc => by simp [hc]
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
          (by unfold topAddr avAddr; omega) (.inl (by omega)),
        keep _ (fun k hk => by have := hff (8 + k) (by omega); rwa [show c.addr + 16 + (8 + k) =
          c.addr + 24 + k by omega] at this) (.inl (by omega)) (by unfold topAddr avAddr; omega)
          (.inl (by omega))⟩
  have gAv : ∀ w, 0x8001ad10 ≤ w → w + 8 ≤ 0x8001b520 → ∀ k, k < 8 → allocGlobal (w + k) :=
    fun w h1 h2 k hk => .inl ⟨by omega, by omega⟩
  have gHi : ∀ w, 0x8001b990 ≤ w → w + 8 ≤ 0x8001b9b0 → ∀ k, k < 8 → allocGlobal (w + k) :=
    fun w h1 h2 k hk => .inr (.inr (.inr (.inl ⟨by omega, by omega⟩)))
  have kBb : read64 m' binblocksAddr = read64 m binblocksAddr :=
    Kg _ (gAv _ (by unfold binblocksAddr avAddr; omega) (by unfold binblocksAddr avAddr; omega))
      (by unfold binblocksAddr topAddr avAddr; omega)
  have hXm : (⟨x, a + d, true⟩ : Chunk) ∈ cs₁ ++ [⟨x, a + d, true⟩] := by simp
  refine ⟨⟨{ sbrk_base := ?_, brk := ?_, brk_le := HH.brk_le, top_ptr := htp
             top_le := by omega, top_size := by omega, top_header := hth
             top_pad := ?_, max_sbrked := ?_, mallinfo := ?_, first_prev := ?_
             walk := hwalk, coalesced := coal_swap (c := ⟨x, a, true⟩) (c' := ⟨x, a + d, true⟩) rfl (cs₂ := []) (HH.coalesced : Coal (cs₁ ++ [⟨x, a, true⟩])), footer := ?_
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
    · have hfp := HH.first_prev
      obtain ⟨hh, hhr, _, _⟩ := HX.hdr
      rw [he, hhr] at hfp
      rw [he, hhdr]
      unfold prevInuse at hpi
      have := hpi hh hhr
      simp only [Option.any] at hfp ⊢
      exact this ▸ hfp
    · have := hW1b c hc
      rw [← hca, keep _ (foot_header B (.inr ⟨c, by simp [hc], rfl⟩)) (.inl (by omega))
        (by unfold topAddr avAddr; unfold heapStart at this; omega) (.inl (by omega)), hca]
      exact HH.first_prev
  · intro c hc hf
    have hc1 := hfree_in' c hc hf
    have hcL := hin_old c hc1
    have := hW1b c hc1
    unfold heapStart at this
    rw [keep _ (foot_free B hcL hf).2 (.inl (by omega)) (by unfold topAddr avAddr; omega)
      (.inl (by omega))]
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
    exact ⟨c, hin_new c (hfree_in c hc h2), h1, h2, h3⟩
  · intro c hc hf
    exact HH.free_binned c (hin_old c (hfree_in' c hc hf)) hf
  · intro e he
    obtain ⟨c, hc, hu, h1, h2⟩ := HH.live e he
    rcases (hmemL c).1 hc with h3 | rfl
    · exact ⟨c, hin_new c h3, hu, h1, h2⟩
    · exact ⟨_, hXm, rfl, h1, by simp only at h2 ⊢; omega⟩
  · intro e he hr
    obtain ⟨c, hc, hu, h1, h2⟩ := HH.exact e he hr
    rcases (hmemL c).1 hc with h3 | rfl
    · exact ⟨c, hin_new c h3, hu, h1, h2⟩
    · exact ⟨_, hXm, rfl, h1, by simp only at h2 ⊢; omega⟩

/-- **A live block is fresh among the others.** A block at the payload start
of its in-use chunk, starting where no other live block does, lies in the
arena and is disjoint from every other live extent. -/
theorem PHeapAt.fresh_of_block {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} {q n : Nat}
    (h : PHeapAt m ((q, n) :: H) top brkv chunks bins) (hst : Starts ((q, n) :: H)) :
    FreshAt H q n := by
  have HH := h.heap.heap
  have hbrk := HH.brk_le
  have htle := HH.top_le
  have hroom := h.heap.top_room
  obtain ⟨c, hc, hu, hca, hcn⟩ := HH.exact (q, n) List.mem_cons_self List.mem_cons_self
  simp only at hca hcn
  have hb := HH.walk.chunk_bounds c hc
  unfold Starts at hst
  rw [List.map_cons, List.nodup_cons] at hst
  have hne : ∀ e ∈ H, e.1 ≠ q := fun e he heq => hst.1 (List.mem_map.2 ⟨e, he, heq⟩)
  refine ⟨⟨?_, ?_, ?_, fun e he a ha hea => ?_⟩, hne⟩
  · unfold heapStart at hb; omega
  · show heapStart ≤ _; omega
  · show _ ≤ heapEnd; omega
  · obtain ⟨c1, hc1, hu1, h1, h2⟩ := HH.exact e (List.mem_cons_of_mem _ he) (List.mem_cons_of_mem _ he)
    unfold InExt at ha hea
    simp only at ha
    have hb1 := HH.walk.chunk_bounds c1 hc1
    rcases HH.walk.chunk_sep c hc c1 hc1 with rfl | h3 | h3
    · exact hne e he (by omega)
    · omega
    · omega

/-- The bytes of a live block other than those listed are footprint. -/
theorem PHeapAt.block_foot {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} {q n : Nat}
    (h : PHeapAt m ((q, n) :: H) top brkv chunks bins) (hst : Starts ((q, n) :: H)) :
    ∀ k, k < n → vsaFoot H (q + k) := by
  have F := h.fresh_of_block hst
  obtain ⟨_, hlo, hhi, hdj⟩ := F.block
  intro k hk
  exact .inr ⟨by show heapStart ≤ _; exact Nat.le_trans hlo (Nat.le_add_right _ _),
    by show _ < heapEnd; exact Nat.lt_of_lt_of_le (by omega) hhi,
    fun e he hin => hdj e he (q + k) ⟨by simp only; omega, by simp only; omega⟩ hin⟩

end VsaIris.VsaHeap
