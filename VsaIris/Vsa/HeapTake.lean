import VsaIris.Vsa.HeapRead

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.MallocFast

theorem bytes_of_read64_eq {m m' : Mem} {a v : Nat} (h : read64 m a = some v)
    (h' : read64 m' a = some v) : ∀ k, k < 8 → m'[a + k]? = m[a + k]? := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, e0, e1, e2, e3, e4, e5, e6, e7, hv⟩ := read64_bytes m a v h
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, f0, f1, f2, f3, f4, f5, f6, f7, hv'⟩ := read64_bytes m' a v h'
  have l0 := b0.isLt; have l1 := b1.isLt; have l2 := b2.isLt; have l3 := b3.isLt
  have l4 := b4.isLt; have l5 := b5.isLt; have l6 := b6.isLt; have l7 := b7.isLt
  have k0 := c0.isLt; have k1 := c1.isLt; have k2 := c2.isLt; have k3 := c3.isLt
  have k4 := c4.isLt; have k5 := c5.isLt; have k6 := c6.isLt; have k7 := c7.isLt
  have q0 : c0 = b0 := BitVec.eq_of_toNat_eq (by omega)
  have q1 : c1 = b1 := BitVec.eq_of_toNat_eq (by omega)
  have q2 : c2 = b2 := BitVec.eq_of_toNat_eq (by omega)
  have q3 : c3 = b3 := BitVec.eq_of_toNat_eq (by omega)
  have q4 : c4 = b4 := BitVec.eq_of_toNat_eq (by omega)
  have q5 : c5 = b5 := BitVec.eq_of_toNat_eq (by omega)
  have q6 : c6 = b6 := BitVec.eq_of_toNat_eq (by omega)
  have q7 : c7 = b7 := BitVec.eq_of_toNat_eq (by omega)
  intro k hk
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k
  · simpa [e0, f0] using congrArg some q0
  · rw [e1, f1, q1]
  · rw [e2, f2, q2]
  · rw [e3, f3, q3]
  · rw [e4, f4, q4]
  · rw [e5, f5, q5]
  · rw [e6, f6, q6]
  · rw [e7, f7, q7]
  · omega

section Geo

variable {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat} {chunks : List Chunk}
  {bins : Nat → List Nat}

theorem _root_.Vsa.Sim.DlHeap.HeapAt.aligned (h : HeapAt m H (fun e => e ∈ H) top brkv chunks bins) :
    (∀ c ∈ chunks, c.addr % 16 = 0) ∧ top % 16 = 0 :=
  walk_aligned h.walk (by unfold heapStart; decide)

theorem _root_.Vsa.Sim.DlHeap.HeapAt.chunk_eq (h : HeapAt m H (fun e => e ∈ H) top brkv chunks bins) {c c' : Chunk}
    (hc : c ∈ chunks) (hc' : c' ∈ chunks) (he : c.addr = c'.addr) : c = c' := by
  rcases h.walk.chunk_sep c hc c' hc' with h1 | h1 | h1
  · exact h1
  · have := (h.walk.chunk_bounds c hc).2.2; omega
  · have := (h.walk.chunk_bounds c' hc').2.2; omega

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

theorem _root_.Vsa.Sim.DlHeap.HeapAt.end_bnd (h : HeapAt m H (fun e => e ∈ H) top brkv chunks bins)
    {c : Chunk} (hc : c ∈ chunks) :
    c.addr + c.size = top ∨ ∃ d ∈ chunks, d.addr = c.addr + c.size := by
  obtain ⟨cs₁, cs₂, hsplit⟩ := List.append_of_mem hc
  have hw := h.walk
  rw [hsplit] at hw
  rcases (walk_next_of hw).2 with ⟨he, _⟩ | ⟨d, cs₃, rfl, hd⟩
  · exact .inl he
  · exact .inr ⟨d, by rw [hsplit]; simp, hd⟩

theorem walk_sizes {m : Mem} :
    ∀ {p top : Nat} {cs : List Chunk}, ChunkWalk m p top cs → ∀ c ∈ cs, c.size % 16 = 0 ∧ 32 ≤ c.size
  | _, _, [], ChunkWalk.top => fun _ h => nomatch h
  | _, _, _ :: _, ChunkWalk.chunk _ _ hmin hal _ rest => by
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨hal, hmin⟩
    · exact walk_sizes rest c hc

theorem _root_.Vsa.Sim.DlHeap.HeapAt.small_member (h : HeapAt m H (fun e => e ∈ H) top brkv chunks bins)
    {i q : Nat} (hi1 : 1 < i) (hi : i < 64) (hq : q ∈ bins i) :
    ∃ c ∈ chunks, c.addr = q ∧ c.inuse = false ∧ c.size = 8 * i ∧ i % 2 = 0 := by
  obtain ⟨c, hc, h1, h2, h3⟩ := h.bin_free i q (by omega) (by unfold numBins; omega) hq
  have hbi := h3 hi1
  obtain ⟨hs16, hs32⟩ := walk_sizes h.walk c hc
  unfold binIndex at hbi
  refine ⟨c, hc, h1, h2, ?_, ?_⟩ <;> (repeat' split at hbi) <;> omega

theorem _root_.Vsa.Sim.DlHeap.HeapAt.odd_empty (h : HeapAt m H (fun e => e ∈ H) top brkv chunks bins)
    {i : Nat} (hi1 : 1 < i) (hi : i < 64) (hodd : i % 2 = 1) : bins i = [] := by
  rcases hb : bins i with _ | ⟨q, qs⟩
  · rfl
  · obtain ⟨_, _, _, _, _, he⟩ := h.small_member hi1 hi (by rw [hb]; exact List.mem_cons_self)
    omega

theorem walk_header {m : Mem} :
    ∀ {p top : Nat} {cs : List Chunk}, ChunkWalk m p top cs → ∀ c ∈ cs,
      ∃ h, read64 m (c.addr + 8) = some h ∧ chunkSize h = c.size ∧ h % 4 < 2
  | _, _, [], ChunkWalk.top => fun _ h => nomatch h
  | _, _, _ :: _, ChunkWalk.chunk hh hlow _ _ _ rest => by
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨_, hh, rfl, hlow⟩
    · exact walk_header rest c hc

theorem _root_.Vsa.Sim.DlHeap.HeapAt.headers (h : HeapAt m H (fun e => e ∈ H) top brkv chunks bins)
    {c : Chunk} (hc : c ∈ chunks) :
    (∃ hc0, read64 m (c.addr + 8) = some hc0 ∧ chunkSize hc0 = c.size ∧ hc0 % 4 < 2) ∧
    (∃ hn, read64 m (c.addr + c.size + 8) = some hn ∧ prevInuse hn = c.inuse) := by
  refine ⟨walk_header h.walk c hc, ?_⟩
  obtain ⟨cs₁, cs₂, hsplit⟩ := List.append_of_mem hc
  have hw := h.walk
  rw [hsplit] at hw
  exact (walk_next_of hw).1

end Geo

abbrev FreeAt (chunks : List Chunk) (v sz : Nat) : Prop := (⟨v, sz, false⟩ : Chunk) ∈ chunks

theorem freeAt_of_member {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat}
    (h : HeapAt m H (fun e => e ∈ H) top brkv chunks bins) {j q : Nat}
    (hj0 : 0 < j) (hj : j < numBins) (hq : q ∈ bins j) : ∃ sz, FreeAt chunks q sz := by
  obtain ⟨c, hc, ha, hf⟩ := h.member hj0 hj hq
  obtain ⟨a, s, i⟩ := c
  simp only at ha hf
  subst ha; subst hf
  exact ⟨s, hc⟩

def TakeW (pred succ nx : Nat) (a : Nat) : Prop :=
  (pred + 16 ≤ a ∧ a < pred + 24) ∨ (succ + 24 ≤ a ∧ a < succ + 32) ∨ (nx + 8 ≤ a ∧ a < nx + 16)

theorem take_keep {m m' : Mem} {H : List (Nat × Nat)} {pred succ nx a : Nat}
    (hag : ∀ b, vsaFoot H b → ¬ TakeW pred succ nx b → m'[b]? = m[b]?)
    (hfoot : ∀ k, k < 8 → vsaFoot H (a + k)) (ha : a % 8 = 0) (hp : pred % 8 = 0)
    (hs : succ % 8 = 0) (hn : nx % 8 = 0)
    (h1 : a ≠ pred + 16) (h2 : a ≠ succ + 24) (h3 : a ≠ nx + 8) : read64 m' a = read64 m a :=
  read64_keep fun k hk => hag _ (hfoot k hk) (by unfold TakeW; omega)

theorem _root_.Vsa.Sim.DlHeap.HeapAt.node {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat}
    (h : HeapAt m H (fun e => e ∈ H) top brkv chunks bins) {i x : Nat} (hi0 : 0 < i)
    (hi : i < numBins) (hx : x = binAt i ∨ x ∈ bins i) :
    x % 16 = 0 ∧ (x = binAt i ∨ ∃ cx ∈ chunks, cx.addr = x ∧ cx.inuse = false ∧ x ∈ bins i) := by
  rcases hx with rfl | hx
  · exact ⟨(binAt_geo i hi).1, .inl rfl⟩
  · obtain ⟨cx, hcx, rfl, hf⟩ := h.member hi0 hi hx
    exact ⟨h.aligned.1 cx hcx, .inr ⟨cx, hcx, rfl, hf, hx⟩⟩

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
  obtain ⟨B, hpage, hbbl⟩ := h
  have HH := B.heap
  obtain ⟨hal, htop16⟩ := HH.aligned
  have hvmem : v ∈ bins i := by rw [hbin]; exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨c0, hc0, hc0a, hc0f⟩ := HH.member hi0 hi hvmem
  obtain rfl : c = c0 := HH.chunk_eq hc hc0 (hcv.trans hc0a.symm)
  subst hcv
  have hnd := HH.bins_nodup i
  rw [hbin] at hnd

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

  have hpredm := pred_mem (L := bins i) (fun x hx => by rw [hbin]; simp [hx]) hpred
  have hsuccm := succ_mem (L := bins i) (fun x hx => by rw [hbin]; simp [hx]) hsucc
  obtain ⟨hp16, hpnode⟩ := HH.node hi0 hi hpredm
  obtain ⟨hs16, hsnode⟩ := HH.node hi0 hi hsuccm
  have hnx16 : (c.addr + c.size) % 16 = 0 := by rw [← hda]; exact hal d hdmem
  have keep : ∀ a, (∀ k, k < 8 → vsaFoot H (a + k)) → a % 8 = 0 → a ≠ pred + 16 →
      a ≠ succ + 24 → a ≠ c.addr + c.size + 8 → read64 m' a = read64 m a :=
    fun a hf ha h1 h2 h3 => take_keep hag hf ha (by omega) (by omega) (by omega) h1 h2 h3

  have hloc : ∀ x, (x = binAt i ∨ ∃ cx ∈ chunks, cx.addr = x ∧ cx.inuse = false ∧ x ∈ bins i) →
      (0x8001ad10 + 16 ≤ x ∧ x + 32 ≤ 0x8001b520) ∨ (heapStart ≤ x ∧ x + 32 ≤ top) := by
    rintro x (rfl | ⟨cx, hcx, rfl, _, _⟩)
    · have := binAt_geo i hi; unfold binAt avAddr at *; exact .inl (by omega)
    · have := HH.walk.chunk_bounds cx hcx; exact .inr ⟨this.1, by omega⟩
  have hpl := hloc pred hpnode
  have hsl := hloc succ hsnode
  have hnxlo : heapStart + 32 ≤ c.addr + c.size := by omega
  obtain ⟨gS, gB, gP, gM, gI, gT⟩ := HH.keep_scal hag fun w hg hu => by
    unfold allocGlobal InRange at hg; unfold TakeW at hu; unfold heapStart topAddr avAddr at *; omega
  have kBb : read64 m' binblocksAddr = read64 m binblocksAddr :=
    rd_keep hag (fun k hk => .inl (.inl ⟨by unfold binblocksAddr avAddr; omega,
      by unfold binblocksAddr avAddr; omega⟩)) fun w hw => by
        unfold TakeW at hw; unfold heapStart binblocksAddr avAddr at *; omega

  have hkeep : ∀ q, (q = top ∨ ∃ c' ∈ chunks, c'.addr = q) → q ≠ c.addr + c.size →
      read64 m' (q + 8) = read64 m (q + 8) := by
    intro q hq hne
    have hq16 : q % 16 = 0 := by rcases hq with rfl | ⟨c', hc', rfl⟩; exact htop16; exact hal c' hc'
    refine keep _ (foot_header B hq) (by omega) (by omega) ?_ (by omega)
    have := HH.bnd_ne_node hi hsnode hq 16 (by omega) (by omega)
    omega

  have hwalk : ChunkWalk m' heapStart top (chunks.map (reflag (c.addr + c.size) true)) := by
    have := walk_reheader HH.walk (fun r hne hr => hkeep r hr hne) hhdr
      (fun _ _ => ⟨hd, hrd, hsz hd hrd⟩)
    rwa [hpi] at this

  have fdkeep : ∀ j x, 0 < j → j < numBins → (x = binAt j ∨ x ∈ bins j) → x ≠ pred →
      fdOf m' x = fdOf m x := by
    intro j x hj0 hj hx hne
    obtain ⟨hx16, -⟩ := HH.node hj0 hj hx
    refine B.keep_fd hag hj0 hj hx fun w hw => ?_
    unfold TakeW at hw; omega
  have bkkeep : ∀ j x, 0 < j → j < numBins → (x = binAt j ∨ x ∈ bins j) → x ≠ succ →
      bkOf m' x = bkOf m x := by
    intro j x hj0 hj hx hne
    obtain ⟨hx16, hxn⟩ := HH.node hj0 hj hx
    refine B.keep_bk hag hj0 hj hx fun w hw => ?_
    unfold TakeW at hw
    rcases hxn with rfl | ⟨cx, hcx, rfl, _, _⟩
    · have := binAt_geo j hj; unfold heapStart at hnxlo; omega
    · rcases HH.boundary_out hc (.inr ⟨cx, hcx, rfl⟩) with h1 | h1 <;> omega

  have hdisj : ∀ a ∈ pre, ∀ b ∈ post, a ≠ b := fun a ha b hb =>
    (List.nodup_append.mp hnd).2.2 a ha b (List.mem_cons_of_mem _ hb)
  have hvpre : c.addr ∉ pre := fun hm => (List.nodup_append.mp hnd).2.2 c.addr hm c.addr List.mem_cons_self rfl
  have hvpost : c.addr ∉ post := (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1
  have ring_i : BinList m' i (pre ++ post) :=
    binList_remove (HH.bins_list i hi0 hi) hbin (HH.bins_nodup i) hpred hsucc hfd hbk
      (fun x hx hne => fdkeep i x hi0 hi hx hne) (fun x hx hne => bkkeep i x hi0 hi hx hne)
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
  refine ⟨⟨{ sbrk_base := gS, brk := gB, brk_le := HH.brk_le, top_ptr := gT,
              top_le := HH.top_le, top_size := HH.top_size,
              top_header := (hkeep top (.inl rfl) (Ne.symm hnxtop)).trans HH.top_header,
              top_pad := gP, max_sbrked := gM, mallinfo := gI, first_prev := ?_,
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
              exact := ?_ }, B.top_room⟩, hpage, fun bb hbb => hbbl bb (by rw [← kBb]; exact hbb)⟩
  ·
    have hs := HH.walk.head_or_top
    have hne : heapStart ≠ c.addr + c.size := by omega
    rw [hkeep heapStart (by rcases hs with h1 | h1; exact .inl h1; exact .inr h1) hne]
    exact HH.first_prev
  ·
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
  ·
    intro j hj0 hj
    by_cases hji : j = i
    · subst hji; rw [updBins_same]; exact ring_i
    · rw [updBins_other _ _ hji]
      exact binList_keep (HH.bins_list j hj0 hj)
        (fun a ha => fdkeep j a hj0 hj ha (HH.nodes_ne hj0 hj hi0 hi hji ha hpredm))
        (fun b hb => bkkeep j b hj0 hj hb (HH.nodes_ne hj0 hj hi0 hi hji hb hsuccm))
  ·
    intro j
    by_cases hji : j = i
    · subst hji
      rw [updBins_same, List.nodup_append]
      exact ⟨(List.nodup_append.mp hnd).1, (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).2,
        fun a ha b hb => hdisj a ha b hb⟩
    · rw [updBins_other _ _ hji]; exact HH.bins_nodup j
  ·
    intro j q hj0 hj hq
    obtain ⟨c1, hc1, h1, h2, h3⟩ := HH.bin_free j q hj0 hj (hsub j q hq)
    refine ⟨reflag (c.addr + c.size) true c1, reflag_mem hc1, ?_⟩
    rw [reflag_keep c1 hc1 (h1 ▸ hne_v j q hj0 hj hq)]
    exact ⟨h1, h2, h3⟩
  ·
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
  ·
    by_cases h1 : (1 : Nat) = i
    · subst h1
      rw [updBins_same]
      have := HH.remainder
      rw [hbin] at this
      simp only [List.length_append, List.length_cons] at this ⊢
      omega
    · rw [updBins_other _ _ h1]; exact HH.remainder
  ·
    intro bb hbb j hj1 hj hne
    refine HH.binblocks bb (by rw [← kBb]; exact hbb) j hj1 hj ?_
    intro he
    apply hne
    by_cases hji : j = i
    · subst hji; rw [hbin] at he; simp at he
    · rw [updBins_other _ _ hji]; exact he
  ·
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨_, reflag_mem hc, hc_reflag, by simp [reflag_addr], by simp [reflag_addr, reflag_size]; omega⟩
    · obtain ⟨c1, hc1, hu, h1, h2⟩ := HH.live e he
      exact ⟨_, reflag_mem hc1, reflag_inuse_true hu, by rw [reflag_addr]; exact h1,
        by rw [reflag_addr, reflag_size]; exact h2⟩
  ·
    intro e he _
    rcases List.mem_cons.mp he with rfl | he'
    · exact ⟨_, reflag_mem hc, hc_reflag, by simp [reflag_addr], by simp [reflag_size]; omega⟩
    · obtain ⟨c1, hc1, hu, h1, h2⟩ := HH.exact e he' he'
      exact ⟨_, reflag_mem hc1, reflag_inuse_true hu, by rw [reflag_addr]; exact h1,
        by rw [reflag_size]; exact h2⟩

structure FreshAt (H : List (Nat × Nat)) (p n : Nat) : Prop where
  block : FreshBlock vsaLayoutP H p n
  start : ∀ e ∈ H, e.1 ≠ p

theorem PHeapAt.take_fresh {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} (h : PHeapAt m H top brkv chunks bins)
    {c : Chunk} (hc : c ∈ chunks) (hf : c.inuse = false) {n : Nat} (hn : n + 8 ≤ c.size) :
    FreshAt H (c.addr + 16) n ∧ (c.addr + 16) % 16 = 0 := by
  have HH := h.heap.heap
  have hb := HH.walk.chunk_bounds c hc
  have hbrk := HH.brk_le
  have htle := HH.top_le
  have hal := HH.aligned.1 c hc
  have hroom := h.heap.top_room
  refine ⟨⟨⟨?_, ?_, ?_, fun e he a ha hea => ?_⟩, fun e he heq => ?_⟩, by omega⟩
  rotate_right
  · obtain ⟨c1, hc1, hu, h1, _⟩ := HH.exact e he he
    have := HH.chunk_eq hc1 hc (by omega)
    subst this
    rw [hu] at hf; cases hf
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
