import VsaIris.Vsa.HeapAlg

/-!
# Taking a free chunk

Every exact-fit path of `_malloc_r` takes a free chunk `v` out of its bin
and marks it in use: a small or large bin hit (`0x800047f4`, `0x80004c20`),
the last remainder (`0x80004d78`), and the `binblocks` scan (`0x800049e8`).
The machine writes three words:

* the predecessor's `fd` := the successor (`bk->fd = fd`);
* the successor's `bk` := the predecessor (`fd->bk = bk`);
* the next chunk's header := with `PREV_INUSE` set.

`PHeapAt.take` proves the page-aligned heap shape of the result: the chunk
in use, the bin without `v`, and the fresh block `(v + 16, n)` live.

Every word `HeapAt` reads, and every word the take writes, is an aligned
doubleword. So two of them overlap only when they are equal (`read_keep`),
and each field reduces to address inequalities decided by 16-alignment and
the chunk geometry.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.MallocFast

/-- Two aligned doublewords either coincide or do not overlap. -/
theorem dw_disjoint {a b : Nat} (ha : a % 8 = 0) (hb : b % 8 = 0) (hne : a ≠ b) :
    a + 8 ≤ b ∨ b + 8 ≤ a := by omega

/-- A doubleword kept by a memory update: every byte agrees. -/
theorem read64_keep {m m' : Mem} {a : Nat} (h : ∀ k, k < 8 → m'[a + k]? = m[a + k]?) :
    read64 m' a = read64 m a :=
  read64_agreeP (P := fun b => m'[b]? = m[b]?) (fun _ hb => hb) h

/-! ## Heap geometry -/

section Geo

variable {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat} {chunks : List Chunk}
  {bins : Nat → List Nat}

/-- Every chunk and the top are 16-aligned. -/
theorem _root_.Vsa.Sim.DlHeap.HeapAt.aligned (h : HeapAt m H (fun e => e ∈ H) top brkv chunks bins) :
    (∀ c ∈ chunks, c.addr % 16 = 0) ∧ top % 16 = 0 :=
  walk_aligned h.walk (by unfold heapStart; decide)

/-- Chunks are determined by their address. -/
theorem _root_.Vsa.Sim.DlHeap.HeapAt.chunk_eq (h : HeapAt m H (fun e => e ∈ H) top brkv chunks bins) {c c' : Chunk}
    (hc : c ∈ chunks) (hc' : c' ∈ chunks) (he : c.addr = c'.addr) : c = c' := by
  rcases h.walk.chunk_sep c hc c' hc' with h1 | h1 | h1
  · exact h1
  · have := (h.walk.chunk_bounds c hc).2.2; omega
  · have := (h.walk.chunk_bounds c' hc').2.2; omega

/-- A boundary (a chunk's address, or the top) is never strictly inside a chunk. -/
theorem _root_.Vsa.Sim.DlHeap.HeapAt.boundary_out (h : HeapAt m H (fun e => e ∈ H) top brkv chunks bins)
    {x : Chunk} (hx : x ∈ chunks) {b : Nat} (hb : b = top ∨ ∃ c ∈ chunks, c.addr = b) :
    b ≤ x.addr ∨ x.addr + x.size ≤ b := by
  have bx := h.walk.chunk_bounds x hx
  rcases hb with rfl | ⟨c, hc, rfl⟩
  · exact .inr bx.2.1
  · rcases h.walk.chunk_sep x hx c hc with rfl | h1 | h1
    · exact .inl (Nat.le_refl _)
    · exact .inr h1
    · have := (h.walk.chunk_bounds c hc).2.2; exact .inl (by omega)

/-- A bin member is a free chunk. -/
theorem _root_.Vsa.Sim.DlHeap.HeapAt.member (h : HeapAt m H (fun e => e ∈ H) top brkv chunks bins) {j q : Nat}
    (hj0 : 0 < j) (hj : j < numBins) (hq : q ∈ bins j) :
    ∃ c ∈ chunks, c.addr = q ∧ c.inuse = false := by
  obtain ⟨c, hc, h1, h2, _⟩ := h.bin_free j q hj0 hj hq
  exact ⟨c, hc, h1, h2⟩

/-- A chunk is in at most one bin. -/
theorem _root_.Vsa.Sim.DlHeap.HeapAt.bin_unique (h : HeapAt m H (fun e => e ∈ H) top brkv chunks bins) {j j' q : Nat}
    (hj0 : 0 < j) (hj : j < numBins) (hj0' : 0 < j') (hj' : j' < numBins)
    (hq : q ∈ bins j) (hq' : q ∈ bins j') : j = j' := by
  obtain ⟨c, hc, rfl, hf⟩ := h.member hj0 hj hq
  obtain ⟨k, _, _, _, huniq⟩ := h.free_binned c hc hf
  exact (huniq j hj0 hj hq).trans (huniq j' hj0' hj' hq').symm

/-- A chunk ends at the top or at the next chunk. -/
theorem _root_.Vsa.Sim.DlHeap.HeapAt.end_bnd (h : HeapAt m H (fun e => e ∈ H) top brkv chunks bins)
    {c : Chunk} (hc : c ∈ chunks) :
    c.addr + c.size = top ∨ ∃ d ∈ chunks, d.addr = c.addr + c.size := by
  obtain ⟨cs₁, cs₂, hsplit⟩ := List.append_of_mem hc
  have hw := h.walk
  rw [hsplit] at hw
  rcases (walk_next_of hw).2 with ⟨he, _⟩ | ⟨d, cs₃, rfl, hd⟩
  · exact .inl he
  · exact .inr ⟨d, by rw [hsplit]; simp, hd⟩

/-- Bin headers are 16-aligned, in `__malloc_av_`, below the arena. -/
theorem binAt_geo (j : Nat) (hj : j < numBins) :
    binAt j % 16 = 0 ∧ 0x8001ad10 ≤ binAt j ∧ binAt j + 32 ≤ 0x8001b520 := by
  unfold binAt avAddr; unfold numBins at hj; omega

end Geo

/-! ## The take -/

/-- The three words a take writes: the predecessor's `fd`, the successor's
`bk`, the next chunk's header. -/
def TakeW (pred succ nx : Nat) (a : Nat) : Prop :=
  (pred + 16 ≤ a ∧ a < pred + 24) ∨ (succ + 24 ≤ a ∧ a < succ + 32) ∨ (nx + 8 ≤ a ∧ a < nx + 16)

/-- An aligned footprint word that is none of the written words is kept. -/
theorem take_keep {m m' : Mem} {H : List (Nat × Nat)} {pred succ nx a : Nat}
    (hag : ∀ b, vsaFoot H b → ¬ TakeW pred succ nx b → m'[b]? = m[b]?)
    (hfoot : ∀ k, k < 8 → vsaFoot H (a + k)) (ha : a % 8 = 0) (hp : pred % 8 = 0)
    (hs : succ % 8 = 0) (hn : nx % 8 = 0)
    (h1 : a ≠ pred + 16) (h2 : a ≠ succ + 24) (h3 : a ≠ nx + 8) : read64 m' a = read64 m a :=
  read64_keep fun k hk => hag _ (hfoot k hk) (by unfold TakeW; omega)

/-- A node of bin `i`: its header, or a member. -/
theorem _root_.Vsa.Sim.DlHeap.HeapAt.node {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat}
    (h : HeapAt m H (fun e => e ∈ H) top brkv chunks bins) {i x : Nat} (hi0 : 0 < i)
    (hi : i < numBins) (hx : x = binAt i ∨ x ∈ bins i) :
    x % 16 = 0 ∧ (x = binAt i ∨ ∃ cx ∈ chunks, cx.addr = x ∧ cx.inuse = false ∧ x ∈ bins i) := by
  rcases hx with rfl | hx
  · exact ⟨(binAt_geo i hi).1, .inl rfl⟩
  · obtain ⟨cx, hcx, rfl, hf⟩ := h.member hi0 hi hx
    exact ⟨h.aligned.1 cx hcx, .inr ⟨cx, hcx, rfl, hf, hx⟩⟩

/-- A boundary is never 16 bytes into a bin node. -/
theorem _root_.Vsa.Sim.DlHeap.HeapAt.bnd_ne_node {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat}
    (h : HeapAt m H (fun e => e ∈ H) top brkv chunks bins) {i x b : Nat} (hi : i < numBins)
    (hx : x = binAt i ∨ ∃ cx ∈ chunks, cx.addr = x ∧ cx.inuse = false ∧ x ∈ bins i)
    (hb : b = top ∨ ∃ c ∈ chunks, c.addr = b) (k : Nat) (hk0 : 0 < k) (hk : k < 32) :
    b ≠ x + k := by
  have hlo : heapStart ≤ b := by
    rcases hb with rfl | ⟨c, hc, rfl⟩
    · exact h.walk.le
    · exact (h.walk.chunk_bounds c hc).1
  rcases hx with rfl | ⟨cx, hcx, rfl, _, _⟩
  · have := binAt_geo i hi; unfold heapStart at hlo; omega
  · have := (h.walk.chunk_bounds cx hcx).2.2
    rcases h.boundary_out hcx hb with h1 | h1 <;> omega

/-- **Take a free chunk.** Unlinking `v` from bin `i` (the predecessor's `fd`
and the successor's `bk`) and setting `PREV_INUSE` in the next header gives
the page-aligned heap with `v` in use and the block `(v + 16, n)` live. -/
theorem PHeapAt.take {m m' : Mem} {H : List (Nat × Nat)} {top brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} (h : PHeapAt m H top brkv chunks bins)
    {i : Nat} (hi0 : 0 < i) (hi : i < numBins) {pre post : List Nat} {v : Nat}
    (hbin : bins i = pre ++ v :: post)
    {c : Chunk} (hc : c ∈ chunks) (hcv : c.addr = v) {n : Nat} (hn : n + 8 ≤ c.size)
    {pred succ : Nat} (hpred : (binAt i :: pre).getLast? = some pred)
    (hsucc : (post ++ [binAt i]).head? = some succ)
    (hfd : fdOf m' pred = some succ) (hbk : bkOf m' succ = some pred)
    {hd' : Nat} (hhdr : read64 m' (v + c.size + 8) = some hd')
    (hsz : ∀ hd, read64 m (v + c.size + 8) = some hd → chunkSize hd' = chunkSize hd ∧ hd' % 4 < 2)
    (hpi : prevInuse hd' = true)
    (hag : ∀ a, vsaFoot H a → ¬ TakeW pred succ (v + c.size) a → m'[a]? = m[a]?) :
    PHeapAt m' ((v + 16, n) :: H) top brkv (chunks.map (reflag (v + c.size) true))
      (updBins bins i (pre ++ post)) := by
  obtain ⟨B, hpage⟩ := h
  have HH := B.heap
  obtain ⟨hal, htop16⟩ := HH.aligned
  have hvmem : v ∈ bins i := by rw [hbin]; exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨c0, hc0, hc0a, hc0f⟩ := HH.member hi0 hi hvmem
  obtain rfl : c = c0 := HH.chunk_eq hc hc0 (hcv.trans hc0a.symm)
  subst hcv
  have hnd := HH.bins_nodup i
  rw [hbin] at hnd
  -- the chunk after `c`
  obtain ⟨cs₁, cs₂, hsplit⟩ := List.append_of_mem hc
  have hw := HH.walk
  rw [hsplit] at hw
  obtain ⟨⟨hd, hrd, hpd⟩, hnext⟩ := walk_next_of hw
  have hbc := HH.walk.chunk_bounds c hc
  have hnxtop : c.addr + c.size ≠ top := by
    intro he
    rw [he, HH.top_header] at hrd
    cases hrd
    rw [hc0f] at hpd
    have := HH.top_size
    unfold prevInuse at hpd
    simp only [beq_eq_false_iff_ne, ne_eq] at hpd
    omega
  obtain ⟨d, cs₃, hcs₂, hda⟩ : ∃ d cs₃, cs₂ = d :: cs₃ ∧ d.addr = c.addr + c.size := by
    rcases hnext with ⟨he, _⟩ | h'
    · exact absurd he hnxtop
    · exact h'
  have hdmem : d ∈ chunks := by rw [hsplit, hcs₂]; simp
  have hnxb : (c.addr + c.size = top ∨ ∃ c' ∈ chunks, c'.addr = c.addr + c.size) :=
    .inr ⟨d, hdmem, hda⟩
  -- the written nodes
  have hpredm : pred = binAt i ∨ pred ∈ bins i := by
    have := List.mem_of_getLast? hpred
    rcases List.mem_cons.mp this with h1 | h1
    · exact .inl h1
    · exact .inr (by rw [hbin]; exact List.mem_append_left _ h1)
  have hsuccm : succ = binAt i ∨ succ ∈ bins i := by
    have := List.mem_of_head? hsucc
    rcases List.mem_append.mp this with h1 | h1
    · exact .inr (by rw [hbin]; exact List.mem_append_right _ (List.mem_cons_of_mem _ h1))
    · exact .inl (List.mem_singleton.mp h1)
  obtain ⟨hp16, hpnode⟩ := HH.node hi0 hi hpredm
  obtain ⟨hs16, hsnode⟩ := HH.node hi0 hi hsuccm
  have hnx16 : (c.addr + c.size) % 16 = 0 := by rw [← hda]; exact hal d hdmem
  have keep : ∀ a, (∀ k, k < 8 → vsaFoot H (a + k)) → a % 8 = 0 → a ≠ pred + 16 →
      a ≠ succ + 24 → a ≠ c.addr + c.size + 8 → read64 m' a = read64 m a :=
    fun a hf ha h1 h2 h3 => take_keep hag hf ha (by omega) (by omega) (by omega) h1 h2 h3
  -- where the written words lie
  have hloc : ∀ x, (x = binAt i ∨ ∃ cx ∈ chunks, cx.addr = x ∧ cx.inuse = false ∧ x ∈ bins i) →
      (0x8001ad10 + 16 ≤ x ∧ x + 32 ≤ 0x8001b520) ∨ (heapStart ≤ x ∧ x + 32 ≤ top) := by
    rintro x (rfl | ⟨cx, hcx, rfl, _, _⟩)
    · have := binAt_geo i hi; unfold binAt avAddr at *; exact .inl (by omega)
    · have := HH.walk.chunk_bounds cx hcx; exact .inr ⟨this.1, by omega⟩
  have hpl := hloc pred hpnode
  have hsl := hloc succ hsnode
  have hnxlo : heapStart + 32 ≤ c.addr + c.size := by omega
  -- a global doubleword is kept
  have gkeep : ∀ a, (∀ k, k < 8 → allocGlobal (a + k)) → a % 8 = 0 →
      (a + 8 ≤ 0x8001ad10 + 32 ∨ 0x8001b520 ≤ a) → a + 8 ≤ heapStart →
      read64 m' a = read64 m a := by
    intro a hg ha hr hh
    refine keep a (fun k hk => .inl (hg k hk)) ha ?_ ?_ ?_ <;> (unfold heapStart at *; omega)
  have gAv : ∀ a, 0x8001ad10 ≤ a → a + 8 ≤ 0x8001b520 → ∀ k, k < 8 → allocGlobal (a + k) :=
    fun a h1 h2 k hk => .inl ⟨by omega, by omega⟩
  have gHi : ∀ a, 0x8001b990 ≤ a → a + 8 ≤ 0x8001b9b0 → ∀ k, k < 8 → allocGlobal (a + k) :=
    fun a h1 h2 k hk => .inr (.inr (.inr (.inl ⟨by omega, by omega⟩)))
  have kSbrk : read64 m' sbrkBaseAddr = read64 m sbrkBaseAddr :=
    gkeep _ (fun k hk => .inr (.inr (.inl ⟨by unfold sbrkBaseAddr; omega, by unfold sbrkBaseAddr; omega⟩)))
      (by decide) (by unfold sbrkBaseAddr; omega) (by unfold sbrkBaseAddr heapStart; omega)
  have kBrk : read64 m' brkAddr = read64 m brkAddr :=
    gkeep _ (gHi _ (by unfold brkAddr; omega) (by unfold brkAddr; omega)) (by decide)
      (by unfold brkAddr; omega) (by unfold brkAddr heapStart; omega)
  have kPad : read64 m' topPadAddr = read64 m topPadAddr :=
    gkeep _ (gHi _ (by unfold topPadAddr; omega) (by unfold topPadAddr; omega)) (by decide)
      (by unfold topPadAddr; omega) (by unfold topPadAddr heapStart; omega)
  have kMax : read64 m' maxSbrkedAddr = read64 m maxSbrkedAddr :=
    gkeep _ (gHi _ (by unfold maxSbrkedAddr; omega) (by unfold maxSbrkedAddr; omega)) (by decide)
      (by unfold maxSbrkedAddr; omega) (by unfold maxSbrkedAddr heapStart; omega)
  have kMi : read64 m' mallinfoAddr = read64 m mallinfoAddr :=
    gkeep _ (fun k hk => .inr (.inr (.inr (.inr (.inr ⟨by unfold mallinfoAddr; omega,
      by unfold mallinfoAddr; omega⟩))))) (by decide) (by unfold mallinfoAddr; omega)
      (by unfold mallinfoAddr heapStart; omega)
  have kTop : read64 m' topAddr = read64 m topAddr :=
    gkeep _ (gAv _ (by unfold topAddr avAddr; omega) (by unfold topAddr avAddr; omega)) (by decide)
      (by unfold topAddr avAddr; omega) (by unfold topAddr avAddr heapStart; omega)
  have kBb : read64 m' binblocksAddr = read64 m binblocksAddr :=
    gkeep _ (gAv _ (by unfold binblocksAddr avAddr; omega) (by unfold binblocksAddr avAddr; omega))
      (by decide) (by unfold binblocksAddr avAddr; omega) (by unfold binblocksAddr avAddr heapStart; omega)
  -- a header word is kept, but the next chunk's
  have hkeep : ∀ q, (q = top ∨ ∃ c' ∈ chunks, c'.addr = q) → q ≠ c.addr + c.size →
      read64 m' (q + 8) = read64 m (q + 8) := by
    intro q hq hne
    have hq16 : q % 16 = 0 := by rcases hq with rfl | ⟨c', hc', rfl⟩; exact htop16; exact hal c' hc'
    refine keep _ (foot_header B hq) (by omega) (by omega) ?_ (by omega)
    have := HH.bnd_ne_node hi hsnode hq 16 (by omega) (by omega)
    omega
  -- the walk, with `c` in use
  have hwalk : ChunkWalk m' heapStart top (chunks.map (reflag (c.addr + c.size) true)) := by
    have := walk_reheader HH.walk (fun r hne hr => hkeep r hr hne) hhdr
      (fun _ _ => ⟨hd, hrd, hsz hd hrd⟩)
    rwa [hpi] at this
  -- link words of bin nodes
  have nodeFoot : ∀ j x, 0 < j → j < numBins → (x = binAt j ∨ x ∈ bins j) →
      ∀ k, 16 ≤ k → k < 32 → vsaFoot H (x + k) := by
    intro j x hj0 hj hx k hk1 hk2
    rcases hx with rfl | hx
    · have := binAt_geo j hj
      exact .inl (.inl ⟨by omega, by omega⟩)
    · obtain ⟨cx, hcx, rfl, hf⟩ := HH.member hj0 hj hx
      have := (foot_free B hcx hf).1 (k - 16) (by omega)
      rwa [show cx.addr + 16 + (k - 16) = cx.addr + k by omega] at this
  have nodeLoc : ∀ j x, 0 < j → j < numBins → (x = binAt j ∨ x ∈ bins j) →
      x % 16 = 0 ∧ x ≠ c.addr + c.size - 16 := by
    intro j x hj0 hj hx
    obtain ⟨hx16, hxn⟩ := HH.node hj0 hj hx
    refine ⟨hx16, ?_⟩
    rcases hxn with rfl | ⟨cx, hcx, rfl, _, _⟩
    · have := binAt_geo j hj; unfold heapStart at hnxlo; omega
    · rcases HH.boundary_out hc (.inr ⟨cx, hcx, rfl⟩) with h1 | h1 <;> omega
  have fdkeep : ∀ j x, 0 < j → j < numBins → (x = binAt j ∨ x ∈ bins j) → x ≠ pred →
      fdOf m' x = fdOf m x := by
    intro j x hj0 hj hx hne
    obtain ⟨hx16, _⟩ := nodeLoc j x hj0 hj hx
    exact keep _ (fun k hk => by
      have := nodeFoot j x hj0 hj hx (16 + k) (by omega) (by omega)
      rwa [show x + (16 + k) = x + 16 + k by omega] at this) (by omega) (by omega) (by omega) (by omega)
  have bkkeep : ∀ j x, 0 < j → j < numBins → (x = binAt j ∨ x ∈ bins j) → x ≠ succ →
      bkOf m' x = bkOf m x := by
    intro j x hj0 hj hx hne
    obtain ⟨hx16, hxnx⟩ := nodeLoc j x hj0 hj hx
    exact keep _ (fun k hk => by
      have := nodeFoot j x hj0 hj hx (24 + k) (by omega) (by omega)
      rwa [show x + (24 + k) = x + 24 + k by omega] at this) (by omega) (by omega) (by omega) (by omega)
  -- nodes of different bins differ
  have nodes_ne : ∀ j j' x y, 0 < j → j < numBins → 0 < j' → j' < numBins → j ≠ j' →
      (x = binAt j ∨ x ∈ bins j) → (y = binAt j' ∨ y ∈ bins j') → x ≠ y := by
    intro j j' x y hj0 hj hj0' hj' hne hx hy hxy
    subst hxy
    rcases hx with rfl | hx <;> rcases hy with hy | hy
    · unfold binAt at hy; omega
    · obtain ⟨cx, hcx, hcxa, _⟩ := HH.member hj0' hj' hy
      have := (HH.walk.chunk_bounds cx hcx).1
      have := binAt_geo j hj; unfold heapStart at *; omega
    · obtain ⟨cx, hcx, hcxa, _⟩ := HH.member hj0 hj hx
      have := (HH.walk.chunk_bounds cx hcx).1
      have := binAt_geo j' hj'; unfold heapStart at *; omega
    · exact hne (HH.bin_unique hj0 hj hj0' hj' hx hy)
  have hbi_ne : ∀ x ∈ bins i, x ≠ binAt i := ((binList_iff_ring.1 (HH.bins_list i hi0 hi)).2)
  -- bin `i` after the unlink
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.1 hpred
  obtain ⟨zs, hzs⟩ := List.head?_eq_some_iff.1 hsucc
  have hndfull : (binAt i :: (pre ++ c.addr :: post)).Nodup := by
    refine List.nodup_cons.2 ⟨fun hm => hbi_ne _ (by rw [hbin]; exact hm) rfl, hnd⟩
  have hndpre : (binAt i :: pre).Nodup :=
    hndfull.sublist (List.Sublist.cons_cons _ (List.sublist_append_left _ _))
  have hndpost : (post ++ [binAt i]).Nodup := by
    rw [List.nodup_append]
    refine ⟨(List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).2, by simp, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton.mp hb]
    exact hbi_ne a (by rw [hbin]; exact List.mem_append_right _ (List.mem_cons_of_mem _ ha))
  have hdisj : ∀ a ∈ pre, ∀ b ∈ post, a ≠ b := by
    intro a ha b hb
    have := (List.nodup_append.mp hnd).2.2 a ha b (List.mem_cons_of_mem _ hb)
    exact this
  have hvpre : c.addr ∉ pre := fun hm => (List.nodup_append.mp hnd).2.2 c.addr hm c.addr List.mem_cons_self rfl
  have hvpost : c.addr ∉ post := (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1
  have ring_i : Ring m' (binAt i) (pre ++ post) := by
    have hold := (binList_iff_ring.1 (HH.bins_list i hi0 hi)).1
    rw [hbin] at hold
    unfold Ring at hold ⊢
    have e1 : binAt i :: (pre ++ c.addr :: post) ++ [binAt i] = ys ++ pred :: c.addr :: succ :: zs := by
      rw [show binAt i :: (pre ++ c.addr :: post) ++ [binAt i] = (binAt i :: pre) ++ c.addr :: (post ++ [binAt i])
        by simp, hys, hzs]; simp
    have e2 : binAt i :: (pre ++ post) ++ [binAt i] = ys ++ pred :: succ :: zs := by
      rw [show binAt i :: (pre ++ post) ++ [binAt i] = (binAt i :: pre) ++ (post ++ [binAt i])
        by simp, hys, hzs]; simp
    rw [e1] at hold
    rw [e2]
    refine links_unlink hold hfd hbk fun a b hab => ?_
    rcases hab with hab | hab
    · rw [← hys] at hab
      have ⟨ha, hb⟩ := pair_mem hab
      have hane : a ≠ pred := pair_ne_last (hys ▸ hab) (hys ▸ hndpre)
      have hbne : b ≠ binAt i := pair_ne_head hab hndpre
      have hnode : ∀ x ∈ binAt i :: pre, x = binAt i ∨ x ∈ bins i := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact .inl rfl
        · exact .inr (by rw [hbin]; exact List.mem_append_left _ hx)
      refine ⟨fdkeep i a hi0 hi (hnode a ha) hane, bkkeep i b hi0 hi (hnode b hb) ?_⟩
      intro hbs
      have hbpre : b ∈ pre := by
        rcases List.mem_cons.mp hb with h1 | h1
        · exact absurd h1 hbne
        · exact h1
      rcases List.mem_append.mp (hzs ▸ List.mem_cons_self : succ ∈ post ++ [binAt i]) with h1 | h1
      · exact hdisj b hbpre succ h1 hbs
      · exact hbne (hbs.trans (List.mem_singleton.mp h1))
    · rw [← hzs] at hab
      have ⟨ha, hb⟩ := pair_mem hab
      have hbne : b ≠ succ := pair_ne_head (hzs ▸ hab) (hzs ▸ hndpost)
      have hane : a ≠ binAt i := pair_ne_last hab hndpost
      have hnode : ∀ x ∈ post ++ [binAt i], x = binAt i ∨ x ∈ bins i := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact .inr (by rw [hbin]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hx))
        · exact .inl (List.mem_singleton.mp hx)
      refine ⟨fdkeep i a hi0 hi (hnode a ha) ?_, bkkeep i b hi0 hi (hnode b hb) hbne⟩
      intro hap
      have hapost : a ∈ post := by
        rcases List.mem_append.mp ha with h1 | h1
        · exact h1
        · exact absurd (List.mem_singleton.mp h1) hane
      have := List.mem_of_getLast? hpred
      rcases List.mem_cons.mp this with h1 | h1
      · exact hane (hap.trans h1)
      · exact hdisj pred h1 a hapost hap.symm
  -- chunks: only `c` ends at the next chunk
  have end_eq : ∀ c1 ∈ chunks, c1.addr + c1.size = c.addr + c.size → c1 = c := by
    intro c1 hc1 he
    rcases HH.walk.chunk_sep c1 hc1 c hc with h1 | h1 | h1
    · exact h1
    · have := (HH.walk.chunk_bounds c1 hc1).2.2; omega
    · have := (HH.walk.chunk_bounds c1 hc1).2.2; omega
  have reflag_keep : ∀ c1 ∈ chunks, c1.addr ≠ c.addr → reflag (c.addr + c.size) true c1 = c1 := by
    intro c1 hc1 hne
    unfold reflag
    rw [ite_eq_right_iff.2 fun he => absurd (congrArg Chunk.addr (end_eq c1 hc1 he)) hne]
  have hc_reflag : (reflag (c.addr + c.size) true c).inuse = true := by simp [reflag]
  have hsub : ∀ j q, q ∈ updBins bins i (pre ++ post) j → q ∈ bins j := by
    intro j q hq
    by_cases hj : j = i
    · subst hj
      rw [updBins_same] at hq
      rw [hbin]
      rcases List.mem_append.mp hq with h1 | h1
      · exact List.mem_append_left _ h1
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h1)
    · rwa [updBins_other _ _ hj] at hq
  have hne_v : ∀ j q, 0 < j → j < numBins → q ∈ updBins bins i (pre ++ post) j → q ≠ c.addr := by
    intro j q hj0 hj hq hqv
    subst hqv
    by_cases hji : j = i
    · subst hji
      rw [updBins_same] at hq
      rcases List.mem_append.mp hq with h1 | h1
      · exact hvpre h1
      · exact hvpost h1
    · rw [updBins_other _ _ hji] at hq
      exact hji (HH.bin_unique hj0 hj hi0 hi hq hvmem)
  refine ⟨⟨{ sbrk_base := kSbrk.trans HH.sbrk_base,
              brk := kBrk.trans HH.brk,
              brk_le := HH.brk_le,
              top_ptr := kTop.trans HH.top_ptr,
              top_le := HH.top_le,
              top_size := HH.top_size,
              top_header := (hkeep top (.inl rfl) (Ne.symm hnxtop)).trans HH.top_header,
              top_pad := kPad.trans HH.top_pad,
              max_sbrked := by rw [kMax]; exact HH.max_sbrked,
              mallinfo := by rw [kMi]; exact HH.mallinfo,
              first_prev := ?_,
              walk := hwalk,
              coalesced := coalesced_reflag_true HH.coalesced,
              footer := ?_,
              bins_list := ?_,
              bins_nodup := ?_,
              bin_free := ?_,
              free_binned := ?_,
              remainder := ?_,
              binblocks_present := by rw [kBb]; exact HH.binblocks_present,
              binblocks := ?_,
              live := ?_,
              exact := ?_ }, B.top_room⟩, hpage⟩
  · -- the first chunk's header
    have hs := HH.walk.head_or_top
    have hne : heapStart ≠ c.addr + c.size := by omega
    rw [hkeep heapStart (by rcases hs with h1 | h1; exact .inl h1; exact .inr h1) hne]
    exact HH.first_prev
  · -- footers of the free chunks
    intro c' hc' hf
    obtain ⟨c1, hc1, ha, hs, hcase⟩ := mem_reflag hc'
    rcases hcase with ⟨_, hin⟩ | ⟨_, rfl⟩
    · rw [hin] at hf; cases hf
    · have hft := HH.footer c' hc1 hf
      have hb := HH.end_bnd hc1
      have hb16 : (c'.addr + c'.size) % 16 = 0 := by
        rcases hb with h1 | ⟨d', hd', h1⟩
        · rw [h1]; exact htop16
        · rw [← h1]; exact hal d' hd'
      rw [keep _ (foot_free B hc1 hf).2 (by omega) ?_ (by omega) (by omega)]
      · exact hft
      · have := HH.bnd_ne_node hi hpnode (by rcases hb with h1 | h1; exact .inl h1; exact .inr h1)
          16 (by omega) (by omega)
        exact this
  · -- the bins
    intro j hj0 hj
    rw [binList_iff_ring]
    refine ⟨?_, fun x hx => (binList_iff_ring.1 (HH.bins_list j hj0 hj)).2 x (hsub j x hx)⟩
    by_cases hji : j = i
    · subst hji; rw [updBins_same]; exact ring_i
    · rw [updBins_other _ _ hji]
      have hold := (binList_iff_ring.1 (HH.bins_list j hj0 hj)).1
      unfold Ring at hold ⊢
      refine hold.transport fun a b hab => ?_
      have ⟨ha, hb⟩ := pair_mem hab
      have hnode : ∀ x ∈ binAt j :: bins j ++ [binAt j], x = binAt j ∨ x ∈ bins j := by
        intro x hx
        simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
          or_false] at hx
        rcases hx with h1 | h1 | h1
        · exact .inl h1
        · exact .inr h1
        · exact .inl h1
      exact ⟨fdkeep j a hj0 hj (hnode a ha) (nodes_ne j i a pred hj0 hj hi0 hi hji (hnode a ha) hpredm),
        bkkeep j b hj0 hj (hnode b hb) (nodes_ne j i b succ hj0 hj hi0 hi hji (hnode b hb) hsuccm)⟩
  · -- no duplicates
    intro j
    by_cases hji : j = i
    · subst hji
      rw [updBins_same, List.nodup_append]
      exact ⟨(List.nodup_append.mp hnd).1, (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).2,
        fun a ha b hb => hdisj a ha b hb⟩
    · rw [updBins_other _ _ hji]; exact HH.bins_nodup j
  · -- bin members are free chunks
    intro j q hj0 hj hq
    obtain ⟨c1, hc1, h1, h2, h3⟩ := HH.bin_free j q hj0 hj (hsub j q hq)
    refine ⟨reflag (c.addr + c.size) true c1, reflag_mem hc1, ?_⟩
    rw [reflag_keep c1 hc1 (h1 ▸ hne_v j q hj0 hj hq)]
    exact ⟨h1, h2, h3⟩
  · -- free chunks are binned
    intro c' hc' hf
    obtain ⟨c1, hc1, ha, hs, hcase⟩ := mem_reflag hc'
    rcases hcase with ⟨_, hin⟩ | ⟨hne, rfl⟩
    · rw [hin] at hf; cases hf
    · obtain ⟨j, hj0, hj, hm, huniq⟩ := HH.free_binned c' hc1 hf
      have hcne : c'.addr ≠ c.addr := fun he => hne (by rw [end_eq c' hc1 (by
        rw [HH.chunk_eq hc1 hc he])])
      refine ⟨j, hj0, hj, ?_, fun j' hj0' hj' hm' => huniq j' hj0' hj' (hsub j' _ hm')⟩
      by_cases hji : j = i
      · subst hji
        rw [updBins_same]
        rw [hbin] at hm
        rcases List.mem_append.mp hm with h1 | h1
        · exact List.mem_append_left _ h1
        · rcases List.mem_cons.mp h1 with h2 | h2
          · exact absurd h2 hcne
          · exact List.mem_append_right _ h2
      · rwa [updBins_other _ _ hji]
  · -- the last-remainder bin
    by_cases h1 : (1 : Nat) = i
    · subst h1
      rw [updBins_same]
      have := HH.remainder
      rw [hbin] at this
      simp only [List.length_append, List.length_cons] at this ⊢
      omega
    · rw [updBins_other _ _ h1]; exact HH.remainder
  · -- the `binblocks` bits of nonempty bins
    intro bb hbb j hj1 hj hne
    refine HH.binblocks bb (by rw [← kBb]; exact hbb) j hj1 hj ?_
    intro he
    apply hne
    by_cases hji : j = i
    · subst hji; rw [hbin] at he; simp at he
    · rw [updBins_other _ _ hji]; exact he
  · -- live blocks
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨_, reflag_mem hc, hc_reflag, by simp [reflag_addr], by simp [reflag_addr, reflag_size]; omega⟩
    · obtain ⟨c1, hc1, hu, h1, h2⟩ := HH.live e he
      exact ⟨_, reflag_mem hc1, reflag_inuse_true hu, by rw [reflag_addr]; exact h1,
        by rw [reflag_addr, reflag_size]; exact h2⟩
  · -- exact blocks
    intro e he _
    rcases List.mem_cons.mp he with rfl | he'
    · exact ⟨_, reflag_mem hc, hc_reflag, by simp [reflag_addr], by simp [reflag_size]; omega⟩
    · obtain ⟨c1, hc1, hu, h1, h2⟩ := HH.exact e he' he'
      exact ⟨_, reflag_mem hc1, reflag_inuse_true hu, by rw [reflag_addr]; exact h1,
        by rw [reflag_size]; exact h2⟩

/-- **The taken block is fresh**: inside the arena, 16-aligned, and disjoint
from every live extent, which all lie in in-use chunks. -/
theorem PHeapAt.take_fresh {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} (h : PHeapAt m H top brkv chunks bins)
    {c : Chunk} (hc : c ∈ chunks) (hf : c.inuse = false) {n : Nat} (hn : n + 8 ≤ c.size) :
    FreshBlock vsaLayoutP H (c.addr + 16) n ∧ (c.addr + 16) % 16 = 0 := by
  have HH := h.heap.heap
  have hb := HH.walk.chunk_bounds c hc
  have hbrk := HH.brk_le
  have htle := HH.top_le
  have hal := HH.aligned.1 c hc
  have hroom := h.heap.top_room
  refine ⟨⟨?_, ?_, ?_, fun e he a ha hea => ?_⟩, by omega⟩
  · unfold heapStart at hb; omega
  · show heapStart ≤ _; omega
  · show _ ≤ heapEnd; omega
  · obtain ⟨c1, hc1, hu, h1, h2⟩ := HH.live e he
    unfold InExt at ha hea
    simp only at ha
    have hb1 := HH.walk.chunk_bounds c1 hc1
    rcases HH.walk.chunk_sep c hc c1 hc1 with rfl | h3 | h3
    · rw [hu] at hf; cases hf
    · omega
    · omega

end VsaIris.VsaHeap
