import VsaIris.Vsa.HeapTake
import VsaIris.Vsa.FreeFastHeap
import VsaIris.Vsa.MallocFastHeap

/-!
# Carving a remainder off a chunk

`_malloc_r` serves a request from a free chunk larger than `nb + MINSIZE` by
splitting it: the last remainder (`0x80004da0`) and the block walk's victim
(`0x80004d14`). The chunk is unlinked from its bin, its first `nb` bytes are
handed out, and the rest becomes a free chunk that is the only member of the
last-remainder bin 1.

The heap edit factors in two. The unlink with the victim marked in use is
`PHeapAt.take`, stated over a memory that the proof chooses (the machine never
writes the next chunk's `PREV_INUSE`, but the intermediate memory may set it).
`PHeapAt.carve` is the rest: an in-use chunk `v` of size `sz` shrinks to `nb`,
and `v + nb` becomes a free chunk of size `sz - nb` on the empty bin 1. Eight
words change: the two chunks' headers, the remainder's links, bin 1's links,
the remainder's footer and the next chunk's header (`PREV_INUSE` cleared).
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.MallocFast VsaIris.Sym

/-- The words a carve writes: `v`'s header, the remainder's header and links,
bin 1's links, the remainder's footer, and the next chunk's header. -/
def CarveW (v nb sz : Nat) (a : Nat) : Prop :=
  (v + 8 ≤ a ∧ a < v + 16) ∨ (v + nb + 8 ≤ a ∧ a < v + nb + 32) ∨
    (binAt 1 + 16 ≤ a ∧ a < binAt 1 + 32) ∨ (v + sz ≤ a ∧ a < v + sz + 16)

/-- The coalescing condition of a chunk list, as a named predicate. -/
def Coal (L : List Chunk) : Prop :=
  ∀ i (hi : i + 1 < L.length), L[i].inuse = true ∨ L[i + 1].inuse = true

theorem coal_cons_cons {x y : Chunk} {L : List Chunk} :
    Coal (x :: y :: L) ↔ (x.inuse = true ∨ y.inuse = true) ∧ Coal (y :: L) := by
  constructor
  · intro h
    refine ⟨h 0 (by simp), fun i hi => ?_⟩
    have := h (i + 1) (by simp at hi ⊢; omega)
    simpa using this
  · rintro ⟨h0, h⟩ i hi
    rcases i with _ | i
    · simpa using h0
    · have := h i (by simp at hi ⊢; omega)
      simpa using this

theorem coal_single (x : Chunk) : Coal [x] := fun i hi => by simp at hi

/-- Replacing a chunk by an in-use chunk and another one, where the chunk
after them is in use, keeps coalescing. -/
theorem coal_carve {a b c : Chunk} (ha : a.inuse = true) :
    ∀ {cs₁ cs₂ : List Chunk}, Coal (cs₁ ++ c :: cs₂) → (∀ d ∈ cs₂.head?, d.inuse = true) →
      Coal (cs₁ ++ a :: b :: cs₂)
  | [], [], _, _ => by
    simp only [List.nil_append]
    exact coal_cons_cons.2 ⟨.inl ha, coal_single b⟩
  | [], d :: cs₂, h, hd => by
    simp only [List.nil_append] at h ⊢
    have hd' : d.inuse = true := hd d rfl
    exact coal_cons_cons.2 ⟨.inl ha, coal_cons_cons.2 ⟨.inr hd', (coal_cons_cons.1 h).2⟩⟩
  | [x], cs₂, h, hd => by
    simp only [List.cons_append, List.nil_append] at h ⊢
    obtain ⟨hx, h'⟩ := coal_cons_cons.1 h
    exact coal_cons_cons.2 ⟨.inr ha, coal_carve ha (cs₁ := []) h' hd⟩
  | x :: y :: cs₁, cs₂, h, hd => by
    simp only [List.cons_append] at h ⊢
    obtain ⟨hx, h'⟩ := coal_cons_cons.1 h
    exact coal_cons_cons.2 ⟨hx, coal_carve ha (cs₁ := y :: cs₁) h' hd⟩

/-- The first chunk of a walk, named: its header, the header after it, and
the rest of the walk. -/
structure WalkHead (m : Mem) (p top : Nat) (c : Chunk) (cs : List Chunk) : Prop where
  addr : c.addr = p
  hdr : ∃ hh, read64 m (p + 8) = some hh ∧ chunkSize hh = c.size ∧ hh % 4 < 2
  min : 32 ≤ c.size
  al : c.size % 16 = 0
  next : ∃ h', read64 m (p + c.size + 8) = some h' ∧ prevInuse h' = c.inuse
  rest : ChunkWalk m (p + c.size) top cs

theorem walkHead {m : Mem} {p top : Nat} {c : Chunk} {cs : List Chunk}
    (h : ChunkWalk m p top (c :: cs)) : WalkHead m p top c cs := by
  cases h with
  | chunk hh hlow hmin hal hn rest => exact ⟨rfl, ⟨_, hh, rfl, hlow⟩, hmin, hal, ⟨_, hn, rfl⟩, rest⟩

/-- **Carve a remainder off an in-use chunk.** The in-use chunk `v` of size
`sz` shrinks to `nb`; `v + nb` becomes a free chunk of size `sz - nb`, the
only member of the empty bin 1. The previous chunk is in use (`hprev`), and
so is the next one, which is not the top (`hnext`, `hnt`). Live extents in
`v`'s payload end within its first `nb` bytes (`hext`). -/
theorem PHeapAt.carve {m m' : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {cs₁ cs₂ : List Chunk} {bins : Nat → List Nat} {v sz nb : Nat}
    (h : PHeapAt m H top brkv (cs₁ ++ ⟨v, sz, true⟩ :: cs₂) bins)
    (hnb16 : nb % 16 = 0) (hnb32 : 32 ≤ nb) (hsz : nb + 32 ≤ sz) (hb1 : bins 1 = [])
    (hprev : ∀ h0, read64 m (v + 8) = some h0 → h0 % 2 = 1)
    (hnext : ∀ d ∈ cs₂.head?, d.inuse = true) (hnt : v + sz ≠ top)
    (hext : ∀ e ∈ H, v + 16 ≤ e.1 → e.1 + e.2 ≤ v + sz + 8 → e.1 + e.2 ≤ v + nb + 8)
    (hvh : read64 m' (v + 8) = some (nb + 1))
    (hrh : read64 m' (v + nb + 8) = some (sz - nb + 1))
    (hrfd : fdOf m' (v + nb) = some (binAt 1)) (hrbk : bkOf m' (v + nb) = some (binAt 1))
    (hbfd : fdOf m' (binAt 1) = some (v + nb)) (hbbk : bkOf m' (binAt 1) = some (v + nb))
    (hft : read64 m' (v + sz) = some (sz - nb))
    (hnx : ∀ hd, read64 m (v + sz + 8) = some hd → ∃ hd', read64 m' (v + sz + 8) = some hd' ∧
      chunkSize hd' = chunkSize hd ∧ hd' % 4 < 2 ∧ prevInuse hd' = false)
    (hag : ∀ a, vsaFoot H a → ¬ CarveW v nb sz a → m'[a]? = m[a]?) :
    PHeapAt m' H top brkv (cs₁ ++ ⟨v, nb, true⟩ :: ⟨v + nb, sz - nb, false⟩ :: cs₂)
      (updBins bins 1 [v + nb]) := by
  obtain ⟨B, hpage, hbbl⟩ := h
  have HH := B.heap
  obtain ⟨hal, htop16⟩ := HH.aligned
  have hlo := HH.walk.le
  have hcb := HH.walk.chunk_bounds
  have hbrk := HH.brk_le
  have htle := HH.top_le
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
  obtain ⟨h', hnr, hnp⟩ := HV.next
  simp only at hhs hnr hnp
  -- the chunk after `v`
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
  have hW3b := HD.rest.chunk_bounds
  have hW3le := HD.rest.le
  have hW1b := W1.chunk_bounds
  have hbin1 := binAt_geo 1 (by unfold numBins; decide)
  -- words the carve does not write
  have keep : ∀ a, (∀ k, k < 8 → vsaFoot H (a + k)) →
      (a + 8 ≤ v + 8 ∨ v + sz + 16 ≤ a ∨ (v + 16 ≤ a ∧ a + 8 ≤ v + nb + 8)) →
      (a + 8 ≤ binAt 1 + 16 ∨ binAt 1 + 32 ≤ a) → read64 m' a = read64 m a := by
    intro a hf hr hb
    refine read64_keep fun k hk => hag _ (hf k hk) ?_
    unfold CarveW
    by_cases hlow : a < 0x8001c170
    · have := hf k hk
      rcases this with hg | ⟨h1, _⟩
      · unfold allocGlobal InRange at hg; unfold binAt avAddr at hbin1 hb ⊢; omega
      · unfold heapStart at h1; omega
    · unfold binAt avAddr at hb ⊢; omega
  -- the new walk
  have hdsz : chunkSize hd0 = d.size := hd0s
  obtain ⟨hd', hd'r, hd's, hd'l, hd'p⟩ := hnx hd0 hd0r
  have W3 : ChunkWalk m' (v + sz + d.size) top cs₃ := by
    refine HD.rest.transport_headers fun q hq => (keep _ ?_ ?_ ?_).symm
    · rcases hq with rfl | ⟨c, hc, rfl⟩
      · exact foot_header B (.inl rfl)
      · exact foot_header B (.inr ⟨c, by simp [hc], rfl⟩)
    · rcases hq with rfl | ⟨c, hc, rfl⟩
      · exact .inr (.inl (by omega))
      · have := hW3b c hc; exact .inr (.inl (by omega))
    · unfold binAt avAddr
      rcases hq with rfl | ⟨c, hc, rfl⟩
      · omega
      · have := hW3b c hc; omega
  have hnxf : ∀ k, k < 8 → vsaFoot H (v + sz + d.size + 8 + k) := by
    have hq : v + sz + d.size = top ∨ ∃ c ∈ cs₁ ++ ⟨v, sz, true⟩ :: d :: cs₃, c.addr = v + sz + d.size := by
      rcases HD.rest.head_or_top with he | ⟨c, hc, hca⟩
      · exact .inl he
      · exact .inr ⟨c, by simp [hc], hca⟩
    exact foot_header B hq
  have h2r' : read64 m' (v + sz + d.size + 8) = some h2 :=
    (keep _ hnxf (.inr (.inl (by omega))) (by unfold binAt avAddr; omega)).trans h2r
  have hdeq : (⟨v + sz, chunkSize hd', prevInuse h2⟩ : Chunk) = d := by
    rw [hd's, hdsz, h2p, ← hda]
  have Wd : ChunkWalk m' (v + sz) top (d :: cs₃) := by
    have w := ChunkWalk.chunk (m := m') (p := v + sz) (h := hd') (h' := h2) hd'r hd'l
      (by rw [hd's, hdsz]; exact hdmin) (by rw [hd's, hdsz]; exact hdal)
      (by rw [hd's, hdsz]; exact h2r') (by rw [hd's, hdsz]; exact W3)
    rwa [hdeq] at w
  have hcR : chunkSize (sz - nb + 1) = sz - nb := by unfold chunkSize; omega
  have WR : ChunkWalk m' (v + nb) top (⟨v + nb, sz - nb, false⟩ :: d :: cs₃) := by
    have w := ChunkWalk.chunk (m := m') (p := v + nb) (h := sz - nb + 1) (h' := hd') hrh
      (by omega) (by rw [hcR]; omega) (by rw [hcR]; omega)
      (by rw [hcR, show v + nb + (sz - nb) = v + sz by omega]; exact hd'r)
      (by rw [hcR, show v + nb + (sz - nb) = v + sz by omega]; exact Wd)
    rwa [hcR, hd'p] at w
  have hcV : chunkSize (nb + 1) = nb := by unfold chunkSize; omega
  have hpR : prevInuse (sz - nb + 1) = true := by
    unfold prevInuse; rw [beq_iff_eq]; omega
  have WV : ChunkWalk m' v top (⟨v, nb, true⟩ :: ⟨v + nb, sz - nb, false⟩ :: d :: cs₃) := by
    have w := ChunkWalk.chunk (m := m') (p := v) (h := nb + 1) (h' := sz - nb + 1) hvh
      (by omega) (by rw [hcV]; omega) (by rw [hcV]; omega) (by rw [hcV]; exact hrh)
      (by rw [hcV]; exact WR)
    rwa [hcV, hpR] at w
  have hwalk : ChunkWalk m' heapStart top
      (cs₁ ++ ⟨v, nb, true⟩ :: ⟨v + nb, sz - nb, false⟩ :: d :: cs₃) := by
    refine W1.extend (fun c hc => keep _ (foot_header B (.inr ⟨c, by simp [hc], rfl⟩)) ?_ ?_)
      (fun h1 hh1 => ⟨nb + 1, hvh, ?_⟩) WV
    · have := hW1b c hc; exact .inl (by omega)
    · have := hW1b c hc; unfold binAt avAddr; unfold heapStart at this; omega
    · have := hprev h1 hh1
      unfold prevInuse; rw [show (nb + 1) % 2 = 1 by omega, this]
  -- the old and new chunk lists
  have hmemL : ∀ c, c ∈ cs₁ ++ ⟨v, sz, true⟩ :: d :: cs₃ ↔
      c ∈ cs₁ ∨ c = ⟨v, sz, true⟩ ∨ c = d ∨ c ∈ cs₃ := by
    intro c; simp only [List.mem_append, List.mem_cons]
  have hmemL' : ∀ c, c ∈ cs₁ ++ ⟨v, nb, true⟩ :: ⟨v + nb, sz - nb, false⟩ :: d :: cs₃ ↔
      c ∈ cs₁ ∨ c = ⟨v, nb, true⟩ ∨ c = ⟨v + nb, sz - nb, false⟩ ∨ c = d ∨ c ∈ cs₃ := by
    intro c; simp only [List.mem_append, List.mem_cons]
  -- a free chunk of the old heap is before `v` or after `d`
  have hfree_loc : ∀ c ∈ cs₁ ++ ⟨v, sz, true⟩ :: d :: cs₃, c.inuse = false →
      (c ∈ cs₁ ∧ c.addr + c.size ≤ v) ∨ (c ∈ cs₃ ∧ v + sz + d.size ≤ c.addr) := by
    intro c hc hf
    rcases (hmemL c).1 hc with h1 | rfl | rfl | h1
    · exact .inl ⟨h1, (hW1b c h1).2.1⟩
    · cases hf
    · rw [hdin] at hf; cases hf
    · exact .inr ⟨h1, (hW3b c h1).1⟩
  have hfree_new : ∀ c ∈ cs₁ ++ ⟨v, sz, true⟩ :: d :: cs₃, c.inuse = false →
      c ∈ cs₁ ++ ⟨v, nb, true⟩ :: ⟨v + nb, sz - nb, false⟩ :: d :: cs₃ := by
    intro c hc hf
    rcases hfree_loc c hc hf with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp [h1]
  have hr_ne : ∀ c ∈ cs₁ ++ ⟨v, sz, true⟩ :: d :: cs₃, c.inuse = false → c.addr ≠ v + nb := by
    intro c hc hf he
    rcases hfree_loc c hc hf with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := (hW1b c h1).2.2; omega
    · omega
  -- globals the carve does not write
  have Kg : ∀ a, (∀ k, k < 8 → allocGlobal (a + k)) → (a + 8 ≤ binAt 1 + 16 ∨ binAt 1 + 32 ≤ a) →
      read64 m' a = read64 m a := by
    intro a hg hb
    refine keep a (fun k hk => .inl (hg k hk)) (.inl ?_) hb
    have := hg 0 (by omega); have := hg 7 (by omega)
    unfold allocGlobal InRange at *; omega
  have gAv : ∀ a, 0x8001ad10 ≤ a → a + 8 ≤ 0x8001b520 → ∀ k, k < 8 → allocGlobal (a + k) :=
    fun a h1 h2 k hk => .inl ⟨by omega, by omega⟩
  have gHi : ∀ a, 0x8001b990 ≤ a → a + 8 ≤ 0x8001b9b0 → ∀ k, k < 8 → allocGlobal (a + k) :=
    fun a h1 h2 k hk => .inr (.inr (.inr (.inl ⟨by omega, by omega⟩)))
  have kBb : read64 m' binblocksAddr = read64 m binblocksAddr :=
    Kg _ (gAv _ (by unfold binblocksAddr avAddr; omega) (by unfold binblocksAddr avAddr; omega))
      (by unfold binblocksAddr binAt avAddr; omega)
  have kTop : read64 m' topAddr = read64 m topAddr :=
    Kg _ (gAv _ (by unfold topAddr avAddr; omega) (by unfold topAddr avAddr; omega))
      (by unfold topAddr binAt avAddr; omega)
  -- links of old bin nodes other than bin 1's header
  have Klink : ∀ j x, 0 < j → j < numBins → j ≠ 1 → (x = binAt j ∨ x ∈ bins j) →
      fdOf m' x = fdOf m x ∧ bkOf m' x = bkOf m x := by
    intro j x hj0 hj hj1 hx
    have hgj := binAt_geo j hj
    rcases hx with rfl | hx
    · have hb : binAt j + 32 ≤ binAt 1 + 16 ∨ binAt 1 + 32 ≤ binAt j + 16 := by
        unfold binAt avAddr; omega
      exact ⟨Kg _ (gAv _ (by omega) (by omega)) (by omega),
        Kg _ (gAv _ (by omega) (by omega)) (by omega)⟩
    · obtain ⟨c, hc, rfl, hf⟩ := HH.member hj0 hj hx
      have hff := (foot_free B hc hf).1
      have hloc := hfree_loc c hc hf
      have hcs := (HH.walk.chunk_bounds c hc).2.2
      have hcl := (HH.walk.chunk_bounds c hc).1
      unfold heapStart at hcl
      refine ⟨keep _ (fun k hk => hff k (by omega)) ?_ (by unfold binAt avAddr; omega),
        keep _ (fun k hk => by have := hff (8 + k) (by omega); rwa [show c.addr + 16 + (8 + k) =
          c.addr + 24 + k by omega] at this) ?_ (by unfold binAt avAddr; omega)⟩
      · rcases hloc with ⟨_, h2⟩ | ⟨_, h2⟩
        · exact .inl (by omega)
        · exact .inr (.inl (by omega))
      · rcases hloc with ⟨_, h2⟩ | ⟨_, h2⟩
        · exact .inl (by omega)
        · exact .inr (.inl (by omega))
  have hsub : ∀ j q, j ≠ 1 → q ∈ updBins bins 1 [v + nb] j → q ∈ bins j := by
    intro j q hj hq; rwa [updBins_other _ _ hj] at hq
  have hRm : (⟨v + nb, sz - nb, false⟩ : Chunk) ∈
      cs₁ ++ ⟨v, nb, true⟩ :: ⟨v + nb, sz - nb, false⟩ :: d :: cs₃ := by simp
  have hVm : (⟨v, nb, true⟩ : Chunk) ∈
      cs₁ ++ ⟨v, nb, true⟩ :: ⟨v + nb, sz - nb, false⟩ :: d :: cs₃ := by simp
  refine ⟨⟨{ sbrk_base := ?_, brk := ?_, brk_le := HH.brk_le, top_ptr := kTop.trans HH.top_ptr
             top_le := HH.top_le, top_size := HH.top_size, top_header := ?_
             top_pad := ?_, max_sbrked := ?_, mallinfo := ?_, first_prev := ?_
             walk := hwalk, coalesced := ?_, footer := ?_
             bins_list := ?_, bins_nodup := ?_
             bin_free := ?_, free_binned := ?_, remainder := by rw [updBins_same]; exact Nat.le_refl _
             binblocks_present := by rw [kBb]; exact HH.binblocks_present
             binblocks := ?_
             live := ?_, exact := ?_ }, B.top_room⟩, hpage,
    fun bb hbb => hbbl bb (by rw [← kBb]; exact hbb)⟩
  · rw [Kg _ (fun k hk => .inr (.inr (.inl ⟨by unfold sbrkBaseAddr; omega,
      by unfold sbrkBaseAddr; omega⟩))) (by unfold sbrkBaseAddr binAt avAddr; omega)]
    exact HH.sbrk_base
  · rw [Kg _ (gHi _ (by unfold brkAddr; omega) (by unfold brkAddr; omega))
      (by unfold brkAddr binAt avAddr; omega)]
    exact HH.brk
  · rw [keep _ (foot_header B (.inl rfl)) (.inr (.inl (by omega))) (by unfold binAt avAddr; omega)]
    exact HH.top_header
  · rw [Kg _ (gHi _ (by unfold topPadAddr; omega) (by unfold topPadAddr; omega))
      (by unfold topPadAddr binAt avAddr; omega)]
    exact HH.top_pad
  · rw [Kg _ (gHi _ (by unfold maxSbrkedAddr; omega) (by unfold maxSbrkedAddr; omega))
      (by unfold maxSbrkedAddr binAt avAddr; omega)]
    exact HH.max_sbrked
  · rw [Kg _ (fun k hk => .inr (.inr (.inr (.inr (.inr ⟨by unfold mallinfoAddr; omega,
      by unfold mallinfoAddr; omega⟩))))) (by unfold mallinfoAddr binAt avAddr; omega)]
    exact HH.mallinfo
  · rcases W1.head_or_top with he | ⟨c, hc, hca⟩
    · rw [he, hvh]; simp only [Option.any, beq_iff_eq]; omega
    · have := hW1b c hc
      rw [← hca, keep _ (foot_header B (.inr ⟨c, by simp [hc], rfl⟩)) (.inl (by omega))
        (by unfold binAt avAddr; unfold heapStart at this; omega), hca]
      exact HH.first_prev
  · exact coal_carve rfl HH.coalesced (fun d' hd' => by simp at hd'; rw [← hd']; exact hdin)
  · intro c hc hf
    rcases (hmemL' c).1 hc with h1 | rfl | rfl | rfl | h1
    · have hcL : c ∈ cs₁ ++ ⟨v, sz, true⟩ :: d :: cs₃ := by simp [h1]
      have := hW1b c h1
      rw [keep _ (foot_free B hcL hf).2 (.inl (by omega))
        (by unfold binAt avAddr; unfold heapStart at this; omega)]
      exact HH.footer c hcL hf
    · cases hf
    · simp only; rw [show v + nb + (sz - nb) = v + sz by omega]; exact hft
    · rw [hdin] at hf; cases hf
    · have hcL : c ∈ cs₁ ++ ⟨v, sz, true⟩ :: d :: cs₃ := by simp [h1]
      have := hW3b c h1
      rw [keep _ (foot_free B hcL hf).2 (.inr (.inl (by omega))) (by unfold binAt avAddr; omega)]
      exact HH.footer c hcL hf
  · intro j hj0 hj
    rw [binList_iff_ring]
    by_cases hj1 : j = 1
    · subst hj1
      rw [updBins_same]
      refine ⟨⟨hbfd, hrbk, hrfd, hbbk, trivial⟩, fun x hx he => ?_⟩
      simp only [List.mem_singleton] at hx
      subst hx
      have := binAt_geo 1 hj
      omega
    · rw [updBins_other _ _ hj1]
      have hold := binList_iff_ring.1 (HH.bins_list j hj0 hj)
      refine ⟨?_, hold.2⟩
      have hr := hold.1
      unfold Ring at hr ⊢
      refine hr.transport fun a b hab => ?_
      have ⟨ha, hb⟩ := pair_mem hab
      have hnode : ∀ x ∈ binAt j :: bins j ++ [binAt j], x = binAt j ∨ x ∈ bins j := by
        intro x hx
        simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
          or_false] at hx
        rcases hx with h1 | h1 | h1
        · exact .inl h1
        · exact .inr h1
        · exact .inl h1
      exact ⟨(Klink j a hj0 hj hj1 (hnode a ha)).1, (Klink j b hj0 hj hj1 (hnode b hb)).2⟩
  · intro j
    by_cases hj1 : j = 1
    · subst hj1; rw [updBins_same]; simp
    · rw [updBins_other _ _ hj1]; exact HH.bins_nodup j
  · intro j q hj0 hj hq
    by_cases hj1 : j = 1
    · subst hj1
      rw [updBins_same, List.mem_singleton] at hq
      subst hq
      exact ⟨_, hRm, rfl, rfl, fun h => absurd h (by omega)⟩
    · obtain ⟨c, hc, h1, h2, h3⟩ := HH.bin_free j q hj0 hj (hsub j q hj1 hq)
      exact ⟨c, hfree_new c hc h2, h1, h2, h3⟩
  · intro c hc hf
    have hold : ∀ c ∈ cs₁ ++ ⟨v, sz, true⟩ :: d :: cs₃, c.inuse = false →
        ∃ i, 0 < i ∧ i < numBins ∧ c.addr ∈ updBins bins 1 [v + nb] i ∧
          ∀ j, 0 < j → j < numBins → c.addr ∈ updBins bins 1 [v + nb] j → j = i := by
      intro c hcL hf
      obtain ⟨i, hi0, hi, hm, huniq⟩ := HH.free_binned c hcL hf
      have hi1 : i ≠ 1 := fun he => by rw [he, hb1] at hm; cases hm
      refine ⟨i, hi0, hi, by rw [updBins_other _ _ hi1]; exact hm, fun j hj0 hj hm' => ?_⟩
      by_cases hj1 : j = 1
      · subst hj1
        rw [updBins_same, List.mem_singleton] at hm'
        exact absurd hm' (hr_ne c hcL hf)
      · exact huniq j hj0 hj (hsub j _ hj1 hm')
    rcases (hmemL' c).1 hc with h1 | rfl | rfl | rfl | h1
    · exact hold c (by simp [h1]) hf
    · cases hf
    · -- the remainder, on bin 1
      refine ⟨1, by omega, by unfold numBins; omega, by rw [updBins_same]; simp, ?_⟩
      intro j hj0 hj hm
      refine Classical.byContradiction fun hj1 => ?_
      obtain ⟨c', hc', h1', h2', _⟩ := HH.bin_free j _ hj0 hj (hsub j _ hj1 hm)
      exact hr_ne c' hc' h2' h1'
    · rw [hdin] at hf; cases hf
    · exact hold c (by simp [h1]) hf
  · intro bb hbb j hj1 hj hne
    have hj1' : j ≠ 1 := by omega
    rw [updBins_other _ _ hj1'] at hne
    exact HH.binblocks bb (by rw [← kBb]; exact hbb) j hj1 hj hne
  · intro e he
    obtain ⟨c, hc, hu, h1, h2⟩ := HH.live e he
    rcases (hmemL c).1 hc with h3 | rfl | rfl | h3
    · exact ⟨c, by simp [h3], hu, h1, h2⟩
    · exact ⟨_, hVm, rfl, h1, hext e he h1 h2⟩
    · exact ⟨c, by simp, hu, h1, h2⟩
    · exact ⟨c, by simp [h3], hu, h1, h2⟩
  · intro e he hr
    obtain ⟨c, hc, hu, h1, h2⟩ := HH.exact e he hr
    rcases (hmemL c).1 hc with h3 | rfl | rfl | h3
    · exact ⟨c, by simp [h3], hu, h1, h2⟩
    · have := hext e he (by simp only at h1; omega) (by simp only at h1 h2; omega)
      exact ⟨_, hVm, rfl, h1, by simp only at h1 ⊢; omega⟩
    · exact ⟨c, by simp, hu, h1, h2⟩
    · exact ⟨c, by simp [h3], hu, h1, h2⟩

/-- The neighbours of a free chunk: the chunk before it is in use (its header
has `PREV_INUSE`), and the one after is an in-use chunk, not the top. -/
structure FreeNbrs (m : Mem) (top v sz : Nat) (cs₂ : List Chunk) : Prop where
  prev : ∀ h0, read64 m (v + 8) = some h0 → h0 % 2 = 1
  not_top : v + sz ≠ top
  next : ∀ d ∈ cs₂.head?, d.inuse = true

theorem coal_after_free {c d : Chunk} (hc : c.inuse = false) :
    ∀ {cs₁ cs : List Chunk}, Coal (cs₁ ++ c :: d :: cs) → d.inuse = true
  | [], cs, h => by
    have := (coal_cons_cons.1 h).1; rw [hc] at this; simpa using this
  | x :: cs₁, cs, h => by
    rcases cs₁ with _ | ⟨y, cs₁⟩
    · exact coal_after_free hc (cs₁ := []) (coal_cons_cons.1 h).2
    · exact coal_after_free hc (cs₁ := y :: cs₁) (coal_cons_cons.1 h).2

theorem coal_before_free {b c : Chunk} (hc : c.inuse = false) :
    ∀ {cs₀ cs : List Chunk}, Coal (cs₀ ++ b :: c :: cs) → b.inuse = true
  | [], cs, h => by
    have := (coal_cons_cons.1 h).1; rw [hc] at this; simpa using this
  | x :: cs₀, cs, h => by
    rcases cs₀ with _ | ⟨y, cs₀⟩
    · exact coal_before_free hc (cs₀ := []) (coal_cons_cons.1 h).2
    · exact coal_before_free hc (cs₀ := y :: cs₀) (coal_cons_cons.1 h).2

theorem _root_.Vsa.Sim.DlHeap.HeapAt.freeNbrs {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {cs₁ cs₂ : List Chunk} {bins : Nat → List Nat} {v sz : Nat}
    (HH : HeapAt m H (fun e => e ∈ H) top brkv (cs₁ ++ ⟨v, sz, false⟩ :: cs₂) bins) :
    FreeNbrs m top v sz cs₂ := by
  have hC : Coal (cs₁ ++ ⟨v, sz, false⟩ :: cs₂) := HH.coalesced
  refine ⟨?_, ?_, ?_⟩
  · intro h0 hh0
    rcases List.eq_nil_or_concat cs₁ with rfl | ⟨cs₀, c, rfl⟩
    · have hv : v = heapStart := by
        have := (walkHead HH.walk).addr; exact this
      have := HH.first_prev
      rw [← hv, hh0] at this
      simpa using this
    · have hw := HH.walk
      simp only [List.concat_eq_append, List.append_assoc, List.singleton_append] at hw hC
      obtain ⟨⟨h, hr, hp⟩, hn⟩ := walk_next_of hw
      have hca : c.addr + c.size = v := by
        rcases hn with ⟨_, h1⟩ | ⟨d, cs₃, h1, h2⟩
        · cases h1
        · simp only [List.cons.injEq] at h1; rw [← h2, ← h1.1]
      rw [hca, hh0] at hr
      cases hr
      have := coal_before_free rfl hC
      rw [← hp] at this
      unfold prevInuse at this; simpa using this
  · intro he
    obtain ⟨⟨h, hr, hp⟩, _⟩ := walk_next_of HH.walk
    simp only at hr hp
    rw [he, HH.top_header] at hr
    cases hr
    have := HH.top_size
    unfold prevInuse at hp
    simp only [beq_eq_false_iff_ne, ne_eq] at hp
    omega
  · intro d hd
    rcases cs₂ with _ | ⟨d', cs₃⟩
    · cases hd
    · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hd
      subst hd
      exact coal_after_free rfl hC

/-- The footprint shrinks when a block becomes live. -/
theorem vsaFoot_of_cons {e : Nat × Nat} {H : List (Nat × Nat)} {a : Nat}
    (h : vsaFoot (e :: H) a) : vsaFoot H a := by
  rcases h with h | ⟨h1, h2, h3⟩
  · exact .inl h
  · exact .inr ⟨h1, h2, fun e' he' => h3 e' (List.mem_cons_of_mem _ he')⟩

/-- **Split a free chunk.** The free chunk `v` of size `sz` leaves its bin `i`,
its first `nb` bytes become the in-use chunk holding the block `(v + 16, n)`,
and the rest becomes a free chunk, the only member of bin 1 (empty once `v`
has left it). The machine writes the unlink (unless `v` came off bin 1, whose
links the carve rewrites), `v`'s header, the remainder's header, links and
footer, and bin 1's links; the next chunk's header is kept. -/
theorem PHeapAt.splitFree {m m' : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {cs₁ cs₂ : List Chunk} {bins : Nat → List Nat} {v sz : Nat}
    (h : PHeapAt m H top brkv (cs₁ ++ ⟨v, sz, false⟩ :: cs₂) bins)
    {i : Nat} (hi0 : 0 < i) (hi : i < numBins) {pre post : List Nat}
    (hbin : bins i = pre ++ v :: post)
    {nb n : Nat} (hnb16 : nb % 16 = 0) (hnb32 : 32 ≤ nb) (hsz : nb + 32 ≤ sz) (hn : n + 8 ≤ nb)
    (hb1 : updBins bins i (pre ++ post) 1 = [])
    {pred succ : Nat} (hpred : (binAt i :: pre).getLast? = some pred)
    (hsucc : (post ++ [binAt i]).head? = some succ)
    (hfd : i ≠ 1 → fdOf m' pred = some succ) (hbk : i ≠ 1 → bkOf m' succ = some pred)
    (hvh : read64 m' (v + 8) = some (nb + 1))
    (hrh : read64 m' (v + nb + 8) = some (sz - nb + 1))
    (hrfd : fdOf m' (v + nb) = some (binAt 1)) (hrbk : bkOf m' (v + nb) = some (binAt 1))
    (hbfd : fdOf m' (binAt 1) = some (v + nb)) (hbbk : bkOf m' (binAt 1) = some (v + nb))
    (hft : read64 m' (v + sz) = some (sz - nb))
    (hnx : read64 m' (v + sz + 8) = read64 m (v + sz + 8))
    (hag : ∀ a, vsaFoot H a → ¬ TakeW pred succ (v + sz) a → ¬ CarveW v nb sz a →
      m'[a]? = m[a]?) :
    PHeapAt m' ((v + 16, n) :: H) top brkv
      (cs₁ ++ ⟨v, nb, true⟩ :: ⟨v + nb, sz - nb, false⟩ :: cs₂)
      (updBins (updBins bins i (pre ++ post)) 1 [v + nb]) := by
  have B := h.heap
  have HH := B.heap
  have NB := HH.freeNbrs
  have hV : (⟨v, sz, false⟩ : Chunk) ∈ cs₁ ++ ⟨v, sz, false⟩ :: cs₂ := by simp
  have hVb := HH.walk.chunk_bounds _ hV
  obtain ⟨hal, htop16⟩ := HH.aligned
  have hv16 : v % 16 = 0 := hal _ hV
  have hsz16 := (walk_sizes HH.walk _ hV).1
  simp only at hVb hsz16
  have hbrk := HH.brk_le; have htle := HH.top_le
  unfold heapStart at hVb; unfold heapEnd at hbrk
  -- the next chunk's header in `m`
  obtain ⟨hd, hdr, hdp⟩ := (walk_next_of HH.walk).1
  simp only at hdr hdp
  have hdlt := Vsa.Sim.read64_lt _ _ _ hdr
  have hdev : hd % 2 = 0 := by
    unfold prevInuse at hdp; simp only [beq_eq_false_iff_ne, ne_eq] at hdp; omega
  obtain ⟨_, hdhdr⟩ := HH.headers hV
  have hd4 : hd % 4 < 2 := by
    obtain ⟨d, cs₃, rfl, hda⟩ : ∃ d cs₃, cs₂ = d :: cs₃ ∧ d.addr = v + sz := by
      rcases (walk_next_of HH.walk).2 with ⟨he, _⟩ | ⟨d, cs₃, h1, h2⟩
      · exact absurd he NB.not_top
      · exact ⟨d, cs₃, h1, h2⟩
    obtain ⟨hd0, hd0r, _, hd0l⟩ := walk_header HH.walk d (by simp)
    rw [hda, hdr] at hd0r; cases hd0r; exact hd0l
  -- the bin nodes around `v`
  have hvmem : v ∈ bins i := by rw [hbin]; exact List.mem_append_right _ List.mem_cons_self
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
  have hpb : pred + 32 ≤ top := by
    rcases hpnode with rfl | ⟨cx, hcx, rfl, _, _⟩
    · have := binAt_geo i hi; omega
    · have := HH.walk.chunk_bounds cx hcx; omega
  have hsb : succ + 32 ≤ top := by
    rcases hsnode with rfl | ⟨cx, hcx, rfl, _, _⟩
    · have := binAt_geo i hi; omega
    · have := HH.walk.chunk_bounds cx hcx; omega
  -- off bin 1, `v` was its only member
  have hone : i = 1 → pred = binAt 1 ∧ succ = binAt 1 := by
    intro hi1
    subst hi1
    have hl := HH.remainder
    rw [hbin] at hl
    simp only [List.length_append, List.length_cons] at hl
    obtain rfl : pre = [] := List.eq_nil_of_length_eq_zero (by omega)
    obtain rfl : post = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp only [List.getLast?_singleton, Option.some.injEq, List.nil_append,
      List.head?_cons] at hpred hsucc
    exact ⟨hpred.symm, hsucc.symm⟩
  have hvb : ∀ k, 0 < k → k < 32 → v ≠ pred + k ∧ v ≠ succ + k := fun k h1 h2 =>
    ⟨HH.bnd_ne_node hi hpnode (.inr ⟨_, hV, rfl⟩) k h1 h2,
      HH.bnd_ne_node hi hsnode (.inr ⟨_, hV, rfl⟩) k h1 h2⟩
  have hnb' : ∀ k, 0 < k → k < 32 → v + sz ≠ pred + k ∧ v + sz ≠ succ + k := by
    obtain ⟨d, cs₃, h1, h2⟩ : ∃ d cs₃, cs₂ = d :: cs₃ ∧ d.addr = v + sz := by
      rcases (walk_next_of HH.walk).2 with ⟨he, _⟩ | ⟨d, cs₃, h1, h2⟩
      · exact absurd he NB.not_top
      · exact ⟨d, cs₃, h1, h2⟩
    have hq : v + sz = top ∨ ∃ c ∈ cs₁ ++ ⟨v, sz, false⟩ :: cs₂, c.addr = v + sz :=
      .inr ⟨d, by rw [h1]; simp, h2⟩
    exact fun k h1 h2 => ⟨HH.bnd_ne_node hi hpnode hq k h1 h2, HH.bnd_ne_node hi hsnode hq k h1 h2⟩
  -- the virtual memory after the take: `v` unlinked and marked in use
  have hvnx := hvb 8 (by omega) (by omega)
  have hvnx16 := hvb 16 (by omega) (by omega)
  have hvnx' := hnb' 8 (by omega) (by omega)
  have hvnx2 := hnb' 16 (by omega) (by omega)
  have hsp : pred + 16 ≠ succ + 24 := by omega
  have hsucclt : succ < 2 ^ 64 := by omega
  have hpredlt : pred < 2 ^ 64 := by omega
  have e1 : fdOf (writeLog (writeLog (writeLog m [(pred + 16, 8, BitVec.ofNat 64 succ)])
      [(succ + 24, 8, BitVec.ofNat 64 pred)]) [(v + sz + 8, 8, BitVec.ofNat 64 (hd + 1))]) pred =
      some succ := by
    show read64 _ (pred + 16) = _
    rw [read64_store_miss _ _ (by omega), read64_store_miss _ _ (by omega), read64_store_hit,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsucclt]
  have e2 : bkOf (writeLog (writeLog (writeLog m [(pred + 16, 8, BitVec.ofNat 64 succ)])
      [(succ + 24, 8, BitVec.ofNat 64 pred)]) [(v + sz + 8, 8, BitVec.ofNat 64 (hd + 1))]) succ =
      some pred := by
    show read64 _ (succ + 24) = _
    rw [read64_store_miss _ _ (by omega), read64_store_hit, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hpredlt]
  have e3 : read64 (writeLog (writeLog (writeLog m [(pred + 16, 8, BitVec.ofNat 64 succ)])
      [(succ + 24, 8, BitVec.ofNat 64 pred)]) [(v + sz + 8, 8, BitVec.ofNat 64 (hd + 1))])
      (v + sz + 8) = some (hd + 1) := by
    rw [read64_store_hit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have e4 : ∀ a, ¬ TakeW pred succ (v + sz) a →
      (writeLog (writeLog (writeLog m [(pred + 16, 8, BitVec.ofNat 64 succ)])
        [(succ + 24, 8, BitVec.ofNat 64 pred)]) [(v + sz + 8, 8, BitVec.ofNat 64 (hd + 1))])[a]? =
      m[a]? := by
    intro a ha
    unfold TakeW at ha
    rw [writeLog_out, writeLog_out, writeLog_out] <;> simp only [OutL, and_true] <;> omega
  have H1 := h.take hi0 hi hbin hV rfl (n := n) (show n + 8 ≤ sz by omega) hpred hsucc e1 e2 e3
    (fun hd' hd'r => by
      rw [hdr] at hd'r; cases hd'r
      exact ⟨by unfold chunkSize; omega, by omega⟩)
    (by unfold prevInuse; rw [beq_iff_eq]; omega) (fun a _ ha => e4 a ha)
  -- only `v` ends at `v + sz`
  have hmap : (cs₁ ++ ⟨v, sz, false⟩ :: cs₂).map (reflag (v + sz) true) =
      cs₁ ++ ⟨v, sz, true⟩ :: cs₂ := by
    have hid : ∀ c ∈ cs₁ ++ cs₂, reflag (v + sz) true c = c := by
      intro c hc
      have hcL : c ∈ cs₁ ++ ⟨v, sz, false⟩ :: cs₂ := by
        rcases List.mem_append.mp hc with h1 | h1 <;> simp [h1]
      have hcb := HH.walk.chunk_bounds c hcL
      unfold reflag
      split
      · rename_i he
        exfalso
        rcases HH.walk.chunk_sep c hcL _ hV with rfl | h1 | h1
        · obtain ⟨mid, W1, W2⟩ := HH.walk.append_inv
          have := (walkHead W2).addr
          rcases List.mem_append.mp hc with h2 | h2
          · have := W1.chunk_bounds _ h2
            simp only at *; omega
          · have := (walkHead W2).rest.chunk_bounds _ h2
            simp only at *; omega
        · simp only at h1; omega
        · simp only at h1; omega
      · rfl
    rw [List.map_append, List.map_cons,
      List.map_congr_left (fun c hc => hid c (List.mem_append_left _ hc)),
      List.map_congr_left (l := cs₂) (fun c hc => hid c (List.mem_append_right _ hc))]
    simp [reflag]
  rw [hmap] at H1
  -- carve the remainder off, from the virtual memory to the machine's
  have hvh1 : ∀ h0, read64 (writeLog (writeLog (writeLog m [(pred + 16, 8, BitVec.ofNat 64 succ)])
      [(succ + 24, 8, BitVec.ofNat 64 pred)]) [(v + sz + 8, 8, BitVec.ofNat 64 (hd + 1))])
      (v + 8) = some h0 → h0 % 2 = 1 := by
    intro h0 hh0
    rw [read64_store_miss _ _ (by omega), read64_store_miss _ _ (by omega),
      read64_store_miss _ _ (by omega)] at hh0
    exact NB.prev h0 hh0
  refine H1.carve hnb16 hnb32 hsz hb1 hvh1 NB.next NB.not_top ?_ hvh hrh hrfd hrbk hbfd hbbk hft
    ?_ ?_
  · -- live extents in `v` are the new block
    intro e he h1 h2
    rcases List.mem_cons.mp he with rfl | he
    · simp only; omega
    · exfalso
      obtain ⟨c, hc, hu, h3, h4⟩ := HH.live e he
      have hcb := HH.walk.chunk_bounds c hc
      rcases HH.walk.chunk_sep c hc _ hV with rfl | h5 | h5
      · cases hu
      · simp only at h5; omega
      · simp only at h5; omega
  · intro hd' hd'r
    rw [e3] at hd'r; cases hd'r
    exact ⟨hd, by rw [hnx]; exact hdr, by unfold chunkSize; omega, hd4, hdp⟩
  · intro a ha hna
    have haH := vsaFoot_of_cons ha
    by_cases hT : TakeW pred succ (v + sz) a
    · unfold TakeW at hT
      unfold CarveW at hna
      rcases hT with hT | hT | hT
      · -- the predecessor's `fd`: bin 1's when `v` came off bin 1
        by_cases hi1 : i = 1
        · rw [(hone hi1).1] at hT
          exact absurd (.inr (.inr (.inl ⟨hT.1, by omega⟩))) hna
        · have := bytes_of_read64_eq e1 (hfd hi1) (a - (pred + 16)) (by omega)
          rwa [show pred + 16 + (a - (pred + 16)) = a by omega] at this
      · by_cases hi1 : i = 1
        · rw [(hone hi1).2] at hT
          exact absurd (.inr (.inr (.inl ⟨by omega, by omega⟩))) hna
        · have := bytes_of_read64_eq e2 (hbk hi1) (a - (succ + 24)) (by omega)
          rwa [show succ + 24 + (a - (succ + 24)) = a by omega] at this
      · omega
    · rw [hag a haH hT hna, e4 a hT]

end VsaIris.VsaHeap
