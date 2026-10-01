import VsaIris.Vsa.HeapFree

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.MallocFast VsaIris.Sym

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

  have keep : ∀ w, (∀ k, k < 8 → vsaFoot H (w + k)) → (w + 8 ≤ x + 8 ∨ x + 16 ≤ w) →
      (w + 8 ≤ x + a + 8 ∨ x + a + 16 ≤ w) → read64 m' w = read64 m w := by
    intro w hf h1 h2
    exact read64_keep fun k hk => hag _ (hf k hk) (by omega) (by omega)
  have hag' : ∀ w, vsaFoot H w → ¬ (x + 8 ≤ w ∧ w < x + 16 ∨ x + a + 8 ≤ w ∧ w < x + a + 16) →
      m'[w]? = m[w]? := fun w hf hu => hag w hf (fun h => hu (.inl h)) (fun h => hu (.inr h))
  have hG : ∀ w, allocGlobal w → (x + 8 ≤ w ∧ w < x + 16 ∨ x + a + 8 ≤ w ∧ w < x + a + 16) →
      topAddr ≤ w ∧ w < topAddr + 8 := by
    intro w hg hu; unfold allocGlobal InRange at hg; omega

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

  have hmemL : ∀ c, c ∈ cs₁ ++ ⟨x, a + b, true⟩ :: cs₂ ↔
      c ∈ cs₁ ∨ c = ⟨x, a + b, true⟩ ∨ c ∈ cs₂ := by
    intro c; simp only [List.mem_append, List.mem_cons]
  have hfree_loc : ∀ c ∈ cs₁ ++ ⟨x, a + b, true⟩ :: cs₂, c.inuse = false →
      (c ∈ cs₁ ∧ c.addr + c.size ≤ x) ∨ (c ∈ cs₂ ∧ x + a + b ≤ c.addr) := by
    intro c hc hf
    rcases (hmemL c).1 hc with h1 | rfl | h1
    · exact .inl ⟨h1, (hW1b c h1).2.1⟩
    · cases hf
    · exact .inr ⟨h1, (hW3b c h1).1⟩
  have hfree_new : ∀ c ∈ cs₁ ++ ⟨x, a + b, true⟩ :: cs₂, c.inuse = false →
      c ∈ cs₁ ++ ⟨x, a, true⟩ :: ⟨x + a, b, true⟩ :: cs₂ := fun c hc hf =>
    free_mid (xs := [_]) (ys := [_, _]) hc hf (by simp)
  have hfree_old : ∀ c ∈ cs₁ ++ ⟨x, a, true⟩ :: ⟨x + a, b, true⟩ :: cs₂, c.inuse = false →
      c ∈ cs₁ ++ ⟨x, a + b, true⟩ :: cs₂ := fun c hc hf =>
    free_mid (xs := [_, _]) (ys := [_]) hc hf (by simp)
  obtain ⟨gS, gB, gP, gM, gI, gBb, -⟩ := HH.keep_globals hag' hG
  obtain ⟨kBins, kFoot⟩ := B.keep_free hag' hG fun c hc hf w _ => by
    have := (HH.walk.chunk_bounds c hc).2.2
    rcases hfree_loc c hc hf with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega
  obtain ⟨fB, fF⟩ := HH.free_to hfree_new hfree_old
  have hXm : (⟨x, a, true⟩ : Chunk) ∈ cs₁ ++ ⟨x, a, true⟩ :: ⟨x + a, b, true⟩ :: cs₂ := by simp
  have hYm : (⟨x + a, b, true⟩ : Chunk) ∈ cs₁ ++ ⟨x, a, true⟩ :: ⟨x + a, b, true⟩ :: cs₂ := by simp

  have hex : ∀ e ∈ H, ∃ c ∈ cs₁ ++ ⟨x, a, true⟩ :: ⟨x + a, b, true⟩ :: cs₂,
      c.inuse = true ∧ c.addr + 16 = e.1 ∧ e.2 + 8 ≤ c.size := by
    intro e he
    obtain ⟨c, hc, hu, h1, h2⟩ := HH.exact e he he
    rcases (hmemL c).1 hc with h3 | rfl | h3
    · exact ⟨c, by simp [h3], hu, h1, h2⟩
    · exact ⟨_, hXm, rfl, h1, hfit e he h1.symm⟩
    · exact ⟨c, by simp [h3], hu, h1, h2⟩
  refine ⟨⟨{ sbrk_base := gS, brk := gB, brk_le := HH.brk_le
             top_ptr := (keep _ (fun k hk => .inl (by unfold allocGlobal InRange topAddr avAddr; omega))
               (.inl (by unfold topAddr avAddr; omega)) (.inl (by unfold topAddr avAddr; omega))).trans HH.top_ptr
             top_le := HH.top_le, top_size := HH.top_size, top_header := ?_
             top_pad := gP, max_sbrked := gM, mallinfo := gI, first_prev := ?_
             walk := hwalk, coalesced := coal_cut rfl rfl HH.coalesced
             footer := fun c hc hf => kFoot c (hfree_old c hc hf) hf
             bins_list := kBins, bins_nodup := HH.bins_nodup
             bin_free := fB, free_binned := fF, remainder := HH.remainder
             binblocks_present := gBb ▸ HH.binblocks_present
             binblocks := fun bb hbb => HH.binblocks bb (gBb ▸ hbb)
             live := ?_, exact := ?_ }, B.top_room⟩, hpage, fun bb hbb => hbbl bb (gBb ▸ hbb)⟩
  · rw [keep _ (foot_header B (.inl rfl)) (.inr (by omega)) (.inr (by omega))]
    exact HH.top_header
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
  · intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨_, hYm, rfl, by simp only; omega, by simp only; omega⟩
    · obtain ⟨c, hc, hu, h1, h2⟩ := hex e he
      exact ⟨c, hc, hu, by omega, by omega⟩
  · intro e he _
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨_, hYm, rfl, rfl, by simp only; omega⟩
    · exact hex e he

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

theorem PHeapAt.setTop {m m' : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {cs₁ : List Chunk} {bins : Nat → List Nat} {x a a' : Nat}
    (h : PHeapAt m H top brkv (cs₁ ++ [⟨x, a, true⟩]) bins)
    (ha16' : a' % 16 = 0) (ha32 : 32 ≤ a') (hroom : x + a' + 16 ≤ brkv)
    {h' : Nat} (hhdr : read64 m' (x + 8) = some h') (hsz : chunkSize h' = a')
    (hlow : h' % 4 < 2) (hpi : ∀ h0, read64 m (x + 8) = some h0 → prevInuse h' = prevInuse h0)
    (htp : read64 m' topAddr = some (x + a'))
    (hth : read64 m' (x + a' + 8) = some (brkv - (x + a') + 1))
    (hag : ∀ w, vsaFoot H w → ¬ (x + 8 ≤ w ∧ w < x + 16) → ¬ (topAddr ≤ w ∧ w < topAddr + 8) →
      ¬ (x + a' + 8 ≤ w ∧ w < x + a' + 16) → m'[w]? = m[w]?)
    (hfit : ∀ e ∈ H, x + 16 ≤ e.1 → e.1 + e.2 ≤ x + a + 8 → e.1 + e.2 ≤ x + a' + 8) :
    PHeapAt m' H (x + a') brkv (cs₁ ++ [⟨x, a', true⟩]) bins := by
  obtain ⟨B, hpage, hbbl⟩ := h
  have HH := B.heap
  obtain ⟨hal, htop16⟩ := HH.aligned
  have hlo := HH.walk.le
  have hbrk := HH.brk_le
  have htle := HH.top_le
  have htsz := HH.top_size
  have hX : (⟨x, a, true⟩ : Chunk) ∈ cs₁ ++ [⟨x, a, true⟩] := by simp
  have hXb := HH.walk.chunk_bounds _ hX
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
  have hag' : ∀ w, vsaFoot H w → ¬ (x + 8 ≤ w ∧ w < x + 16 ∨ topAddr ≤ w ∧ w < topAddr + 8 ∨
      x + a' + 8 ≤ w ∧ w < x + a' + 16) → m'[w]? = m[w]? := fun w hf hu =>
    hag w hf (fun h => hu (.inl h)) (fun h => hu (.inr (.inl h))) (fun h => hu (.inr (.inr h)))
  have hG : ∀ w, allocGlobal w → (x + 8 ≤ w ∧ w < x + 16 ∨ topAddr ≤ w ∧ w < topAddr + 8 ∨
      x + a' + 8 ≤ w ∧ w < x + a' + 16) → topAddr ≤ w ∧ w < topAddr + 8 := by
    intro w hg hu; unfold allocGlobal InRange at hg; omega
  have hfo : ∀ c ∈ cs₁ ++ [⟨x, a', true⟩], c.inuse = false → c ∈ cs₁ ++ [⟨x, a, true⟩] :=
    fun c hc hf => free_mid (xs := [_]) (ys := [_]) (cs₂ := []) hc hf (by simp)
  obtain ⟨gS, gB, gP, gM, gI, gBb, -⟩ := HH.keep_globals hag' hG
  obtain ⟨kBins, kFoot⟩ := B.keep_free hag' hG fun c hc hf w _ => by
    have := hW1b c (by simpa using free_mid (xs := [_]) (ys := []) (cs₂ := []) hc hf (by simp))
    unfold topAddr avAddr heapStart at *; omega
  have kH : ∀ c ∈ cs₁, read64 m' (c.addr + 8) = read64 m (c.addr + 8) := fun c hc =>
    B.keep_hdr hag' (.inr ⟨c, by simp [hc], rfl⟩) fun w _ => by
      have := hW1b c hc; unfold topAddr avAddr heapStart at *; omega
  obtain ⟨fB, fF⟩ := HH.free_to (fun c hc hf => free_mid (xs := [_]) (ys := [_]) (cs₂ := []) hc hf (by simp)) hfo
  have hthp : prevInuse (brkv - (x + a') + 1) = true := by
    unfold prevInuse; rw [beq_iff_eq]; omega
  have WX : ChunkWalk m' x (x + a') [⟨x, a', true⟩] := by
    have w := ChunkWalk.chunk (m := m') (p := x) (h := h') (h' := brkv - (x + a') + 1) hhdr hlow
      (by rw [hsz]; omega) (by rw [hsz]; omega) (by rw [hsz]; exact hth)
      (by rw [hsz]; exact ChunkWalk.top)
    rwa [hsz, hthp] at w
  have hmemL : ∀ c, c ∈ cs₁ ++ [⟨x, a, true⟩] ↔ c ∈ cs₁ ∨ c = ⟨x, a, true⟩ := by
    intro c; simp only [List.mem_append, List.mem_singleton]
  have hin_new : ∀ c ∈ cs₁, c ∈ cs₁ ++ [⟨x, a', true⟩] := fun c hc => by simp [hc]
  have hXm : (⟨x, a', true⟩ : Chunk) ∈ cs₁ ++ [⟨x, a', true⟩] := by simp
  refine ⟨⟨{ sbrk_base := gS, brk := gB, brk_le := HH.brk_le, top_ptr := htp
             top_le := by omega, top_size := by omega, top_header := hth
             top_pad := gP, max_sbrked := gM, mallinfo := gI, first_prev := ?_
             walk := W1.extend kH (fun h1 hh1 => ⟨h', hhdr, hpi h1 hh1⟩) WX
             coalesced := coal_swap (c := ⟨x, a, true⟩) (c' := ⟨x, a', true⟩) rfl (cs₂ := []) (HH.coalesced : Coal (cs₁ ++ [⟨x, a, true⟩]))
             footer := fun c hc hf => kFoot c (hfo c hc hf) hf
             bins_list := kBins, bins_nodup := HH.bins_nodup
             bin_free := fB, free_binned := fF, remainder := HH.remainder
             binblocks_present := gBb ▸ HH.binblocks_present
             binblocks := fun bb hbb => HH.binblocks bb (gBb ▸ hbb)
             live := ?_, exact := ?_ }, by omega⟩, hpage, fun bb hbb => hbbl bb (gBb ▸ hbb)⟩
  · rcases W1.head_or_top with he | ⟨c, hc, hca⟩
    · have hfp := HH.first_prev
      obtain ⟨hh, hhr, _, _⟩ := HX.hdr
      rw [he, hhr] at hfp
      rw [he, hhdr]
      unfold prevInuse at hpi
      have := hpi hh hhr
      simp only [Option.any] at hfp ⊢
      exact this ▸ hfp
    · rw [← hca, kH c hc, hca]; exact HH.first_prev
  · intro e he
    obtain ⟨c, hc, hu, h1, h2⟩ := HH.live e he
    rcases (hmemL c).1 hc with h3 | rfl
    · exact ⟨c, hin_new c h3, hu, h1, h2⟩
    · exact ⟨_, hXm, rfl, h1, by simp only at h1 h2 ⊢; exact hfit e he h1 h2⟩
  · intro e he hr
    obtain ⟨c, hc, hu, h1, h2⟩ := HH.exact e he hr
    rcases (hmemL c).1 hc with h3 | rfl
    · exact ⟨c, hin_new c h3, hu, h1, h2⟩
    · exact ⟨_, hXm, rfl, h1, by
        simp only at h1 h2 ⊢; have := hfit e he (by omega) (by omega); omega⟩

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
  have hs := walk_sizes h.heap.heap.walk _ (show (⟨x, a, true⟩ : Chunk) ∈ cs₁ ++ [⟨x, a, true⟩] by simp)
  simp only at hs
  rw [show x + a + d = x + (a + d) by omega] at hroom htp hth hag ⊢
  exact h.setTop (a' := a + d) (by omega) (by omega) hroom hhdr hsz hlow hpi htp hth hag
    fun e _ _ h2 => by omega

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

theorem PHeapAt.perm {m : Mem} {H H' : List (Nat × Nat)} {top brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} (h : PHeapAt m H top brkv chunks bins) (hp : ∀ e, e ∈ H' ↔ e ∈ H) :
    PHeapAt m H' top brkv chunks bins := by
  obtain ⟨B, hpage, hbbl⟩ := h
  have HH := B.heap
  refine ⟨⟨{ HH with live := (fun e he => HH.live e ((hp e).1 he))
                     exact := (fun e he _ => HH.exact e ((hp e).1 he) ((hp e).1 he)) }, B.top_room⟩,
    hpage, hbbl⟩

theorem vsaFoot_perm {H H' : List (Nat × Nat)} (hp : ∀ e, e ∈ H' ↔ e ∈ H) {a : Nat}
    (h : vsaFoot H a) : vsaFoot H' a := by
  rcases h with hg | ⟨h1, h2, h3⟩
  · exact .inl hg
  · exact .inr ⟨h1, h2, fun e he => h3 e ((hp e).1 he)⟩

theorem mem_swap {a b : Nat × Nat} {H : List (Nat × Nat)} :
    ∀ e, e ∈ a :: b :: H ↔ e ∈ b :: a :: H := by
  intro e; simp only [List.mem_cons]
  constructor <;> intro h <;> rcases h with h | h | h <;> simp [h]

theorem Starts.swap {a b : Nat × Nat} {H : List (Nat × Nat)} (h : Starts (a :: b :: H)) :
    Starts (b :: a :: H) := by
  unfold Starts at *
  simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at *
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
  exact ⟨⟨Ne.symm h1, h3⟩, h2, h4⟩

theorem PHeapAt.payload_foot {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} (h : PHeapAt m H top brkv chunks bins)
    {c : Chunk} (hc : c ∈ chunks) (hno : ∀ e ∈ H, e.1 ≠ c.addr + 16) :
    ∀ a, c.addr + 16 ≤ a → a < c.addr + c.size + 8 → vsaFoot H a := by
  have HH := h.heap.heap
  have hb := HH.walk.chunk_bounds c hc
  have hbrk := HH.brk_le; have htle := HH.top_le; have hroom := h.heap.top_room
  unfold heapStart at hb
  intro a h1 h2
  refine .inr ⟨by show heapStart ≤ a; unfold heapStart; omega,
    by show a < heapEnd; unfold heapEnd at hbrk ⊢; omega, fun e he hin => ?_⟩
  obtain ⟨ce, hce, _, h3, h4⟩ := HH.exact e he he
  have hbe := HH.walk.chunk_bounds ce hce
  unfold InExt at hin
  rcases HH.walk.chunk_sep ce hce c hc with rfl | h5 | h5
  · exact hno e he h3.symm
  · omega
  · omega

theorem PHeapAt.addBlock {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} (h : PHeapAt m H top brkv chunks bins) {q n : Nat}
    {c : Chunk} (hc : c ∈ chunks) (hu : c.inuse = true) (hca : c.addr + 16 = q)
    (hn : n + 8 ≤ c.size) : PHeapAt m ((q, n) :: H) top brkv chunks bins := by
  obtain ⟨B, hpage, hbbl⟩ := h
  have HH := B.heap
  refine ⟨⟨{ HH with live := fun e he => ?_, exact := fun e he _ => ?_ }, B.top_room⟩, hpage, hbbl⟩
  · rcases List.mem_cons.mp he with rfl | he
    · exact ⟨c, hc, hu, by simp only; omega, by simp only; omega⟩
    · exact HH.live e he
  · rcases List.mem_cons.mp he with rfl | he
    · exact ⟨c, hc, hu, hca, hn⟩
    · exact HH.exact e he he

end VsaIris.VsaHeap
