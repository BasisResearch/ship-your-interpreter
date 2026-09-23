import VsaIris.Vsa.HeapTake

/-!
# Moving a free chunk between bins

`_malloc_r` puts a last remainder that is too small back on its own bin
(`0x8000491c`) and `_free_r` frontlinks a coalesced chunk; both empty one bin
of its single member and link that member in at the head of another, setting
the member's block bit in `binblocks`.

`PHeapAt.moveBin` is that step at the heap: seven words change (bin `i`'s two
links, the victim's two links, bin `j`'s `fd`, the old head's `bk`, and the
bitmap), the walk and every footer are untouched, and the result is the shape
at `updBins (updBins bins i []) j (v :: bins j)`.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.MallocFast

/-- The seven words a bin move writes. -/
def MoveW (i j v oldfirst : Nat) (a : Nat) : Prop :=
  (binAt i + 16 ≤ a ∧ a < binAt i + 32) ∨ (v + 16 ≤ a ∧ a < v + 32) ∨
    (binAt j + 16 ≤ a ∧ a < binAt j + 24) ∨ (oldfirst + 24 ≤ a ∧ a < oldfirst + 32) ∨
    (binblocksAddr ≤ a ∧ a < binblocksAddr + 8)

/-- An aligned footprint word that is none of the seven written words is kept. -/
theorem move_keep {m m' : Mem} {H : List (Nat × Nat)} {i j v oldfirst a : Nat}
    (hag : ∀ b, vsaFoot H b → ¬ MoveW i j v oldfirst b → m'[b]? = m[b]?)
    (hfoot : ∀ k, k < 8 → vsaFoot H (a + k)) (ha : a % 8 = 0)
    (hbi : binAt i % 8 = 0) (hbj : binAt j % 8 = 0) (hv : v % 8 = 0) (ho : oldfirst % 8 = 0)
    (h1 : a ≠ binAt i + 16) (h2 : a ≠ binAt i + 24) (h3 : a ≠ v + 16) (h4 : a ≠ v + 24)
    (h5 : a ≠ binAt j + 16) (h6 : a ≠ oldfirst + 24) (h7 : a ≠ binblocksAddr) :
    read64 m' a = read64 m a := by
  refine read64_keep fun k hk => hag _ (hfoot k hk) ?_
  unfold binblocksAddr avAddr at h7
  unfold MoveW binblocksAddr avAddr
  omega

/-- The second element of a two-element infix of `c :: L` lies in `L`. -/
theorem infix_snd_mem {α : Type _} {a b c : α} {L : List α} (h : [a, b] <:+: c :: L) : b ∈ L := by
  obtain ⟨pre, post, he⟩ := h
  rcases pre with _ | ⟨x, pre'⟩
  · simp only [List.nil_append, List.cons_append, List.cons.injEq] at he
    rw [← he.2]; exact List.mem_cons_self
  · simp only [List.cons_append, List.cons.injEq] at he
    rw [← he.2]
    exact List.mem_append_left _ (List.mem_append_right _
      (List.mem_cons_of_mem a List.mem_cons_self))

/-- The first element of a two-element infix of `L ++ [z]` lies in `L`: a bin
list's header is its last node, so it never starts a linked pair. -/
theorem infix_fst_mem_init {α : Type _} {a b z : α} :
    ∀ {L : List α}, [a, b] <:+: L ++ [z] → a ∈ L
  | [], h => by
      exfalso
      have hl := h.length_le
      simp only [List.length_cons, List.length_nil, List.nil_append] at hl
      omega
  | x :: L', h => by
      obtain ⟨pre, post, he⟩ := h
      rcases pre with _ | ⟨y, pre'⟩
      · simp only [List.nil_append, List.cons_append, List.cons.injEq] at he
        rw [← he.1]; exact List.mem_cons_self
      · simp only [List.cons_append, List.cons.injEq] at he
        exact List.mem_cons_of_mem _ (infix_fst_mem_init ⟨pre', post, he.2⟩)

/-- **Move a free chunk between bins.** Emptying bin `i` of its single member
`v` and linking `v` in at the head of bin `j`, with `j`'s block bit set in
`binblocks`, gives the page-aligned heap at the moved bins. The walk, the
headers and the footers are untouched. -/
theorem PHeapAt.moveBin {m m' : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} (h : PHeapAt m H top brkv chunks bins)
    {i j v sz oldfirst bb' : Nat}
    (hi0 : 0 < i) (hi : i < numBins) (hj0 : 0 < j) (hj : j < numBins) (hji : j ≠ i) (hj1 : j ≠ 1)
    (hbin : bins i = [v]) (hfree : FreeAt chunks v sz) (hidx : 1 < j → binIndex sz = j)
    (hfirst : (bins j ++ [binAt j]).head? = some oldfirst)
    (hfdI : fdOf m' (binAt i) = some (binAt i)) (hbkI : bkOf m' (binAt i) = some (binAt i))
    (hfdV : fdOf m' v = some oldfirst) (hbkV : bkOf m' v = some (binAt j))
    (hfdJ : fdOf m' (binAt j) = some v) (hbkO : bkOf m' oldfirst = some v)
    (hbbr : read64 m' binblocksAddr = some bb') (hbblt : bb' < 2 ^ 32)
    (hbbset : bb' / 2 ^ (j / 4) % 2 = 1)
    (hbbkeep : ∀ bb, read64 m binblocksAddr = some bb →
      ∀ k, bb / 2 ^ k % 2 = 1 → bb' / 2 ^ k % 2 = 1)
    (hag : ∀ a, vsaFoot H a → ¬ MoveW i j v oldfirst a → m'[a]? = m[a]?) :
    PHeapAt m' H top brkv chunks (updBins (updBins bins i []) j (v :: bins j)) := by
  obtain ⟨B, hpage, hbbl⟩ := h
  have HH := B.heap
  have hlo := HH.walk.le
  have hcb := HH.walk.chunk_bounds
  have hbrk := HH.brk_le
  have htle := HH.top_le
  obtain ⟨hal, htop16⟩ := HH.aligned
  have hgi := binAt_geo i hi
  have hgj := binAt_geo j hj
  -- the victim
  have hvmem : v ∈ bins i := by rw [hbin]; exact List.mem_cons_self
  have hv16 : v % 16 = 0 := hal _ hfree
  have hvb := hcb _ hfree
  simp only at hv16 hvb
  have hvlo : heapStart ≤ v := hvb.1
  -- the old head of bin `j`
  have hofm : oldfirst ∈ bins j ∨ oldfirst = binAt j := by
    have := List.mem_of_mem_head? hfirst
    rcases List.mem_append.mp this with hm | hm
    · exact .inl hm
    · exact .inr (by simpa using hm)
  obtain ⟨ho16, honode⟩ := HH.node hj0 hj (hofm.symm.elim .inl .inr)
  -- the bins as rings
  have hringI := (binList_iff_ring.1 (HH.bins_list i hi0 hi)).1
  have hringJ := (binList_iff_ring.1 (HH.bins_list j hj0 hj)).1
  have hneJ := (binList_iff_ring.1 (HH.bins_list j hj0 hj)).2
  have hvJ : v ∉ bins j := fun hc => hji (HH.bin_unique hj0 hj hi0 hi hc hvmem)
  -- the words the move keeps
  have K : ∀ a, (∀ k, k < 8 → vsaFoot H (a + k)) → a % 8 = 0 →
      a ≠ binAt i + 16 → a ≠ binAt i + 24 → a ≠ v + 16 → a ≠ v + 24 →
      a ≠ binAt j + 16 → a ≠ oldfirst + 24 → a ≠ binblocksAddr →
      read64 m' a = read64 m a :=
    fun a hf ha h1 h2 h3 h4 h5 h6 h7 =>
      move_keep hag hf ha (by omega) (by omega) (by omega) (by omega) h1 h2 h3 h4 h5 h6 h7
  -- the old head lies in the arena or is bin `j`'s header
  have holoc : oldfirst = binAt j ∨ heapStart ≤ oldfirst := by
    rcases honode with h1 | ⟨cx, hcx, hxa, _, _⟩
    · exact .inl h1
    · exact .inr (by have := (hcb cx hcx).1; omega)
  -- globals below the arena
  have Kglob : ∀ a, (∀ k, k < 8 → allocGlobal (a + k)) → a % 8 = 0 → a + 8 ≤ heapStart →
      a ≠ binAt i + 16 → a ≠ binAt i + 24 → a ≠ binAt j + 16 → a ≠ oldfirst + 24 →
      a ≠ binblocksAddr → read64 m' a = read64 m a := by
    intro a hg ha hs h1 h2 h5 h6 h7
    have hvlo := hvb.1
    unfold heapStart at hs hvlo
    exact K a (fun k hk => .inl (hg k hk)) ha h1 h2 (by omega) (by omega) h5 h6 h7
  -- a boundary (a chunk's address or the top) keeps its header
  have Khdr : ∀ q, (q = top ∨ ∃ c ∈ chunks, c.addr = q) →
      read64 m' (q + 8) = read64 m (q + 8) := by
    intro q hq
    have hq16 : q % 16 = 0 := by
      rcases hq with rfl | ⟨c, hc, rfl⟩
      · exact htop16
      · exact hal c hc
    have hqlo : heapStart ≤ q := by
      rcases hq with rfl | ⟨c, hc, rfl⟩
      · exact hlo
      · exact (hcb c hc).1
    have hnv8 := HH.bnd_ne_node hi (.inr ⟨_, hfree, rfl, rfl, hvmem⟩) hq 8 (by omega) (by omega)
    have hnv16 := HH.bnd_ne_node hi (.inr ⟨_, hfree, rfl, rfl, hvmem⟩) hq 16 (by omega) (by omega)
    simp only at hnv8 hnv16
    have hno : q ≠ oldfirst + 16 := by
      rcases honode with rfl | ⟨cx, hcx, hxa, hxf, hxm⟩
      · have := binAt_geo j hj; unfold heapStart at hqlo; omega
      · exact HH.bnd_ne_node hj (.inr ⟨cx, hcx, hxa, hxf, hxm⟩) hq 16 (by omega) (by omega)
    unfold heapStart at hqlo hvlo
    exact K _ (foot_header B hq) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by unfold binblocksAddr avAddr; omega)
  -- a node's `fd` and `bk`, away from the six link words
  have Kfd : ∀ x, x % 16 = 0 → (∀ k, 16 ≤ k → k < 32 → vsaFoot H (x + k)) →
      x ≠ v → x ≠ binAt i → x ≠ binAt j → fdOf m' x = fdOf m x := by
    intro x hx16 hxf h1 h2 h3
    exact K _ (fun k hk => by
        have := hxf (16 + k) (by omega) (by omega)
        rwa [show x + (16 + k) = x + 16 + k by omega] at this)
      (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by unfold binblocksAddr avAddr; omega)
  have Kbk : ∀ x, x % 16 = 0 → avAddr + 16 ≤ x → (∀ k, 16 ≤ k → k < 32 → vsaFoot H (x + k)) →
      x ≠ v → x ≠ binAt i → x ≠ oldfirst → bkOf m' x = bkOf m x := by
    intro x hx16 hxlo hxf h1 h2 h3
    unfold avAddr at hxlo
    exact K _ (fun k hk => by
        have := hxf (24 + k) (by omega) (by omega)
        rwa [show x + (24 + k) = x + 24 + k by omega] at this)
      (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by unfold binblocksAddr avAddr; omega)
  -- a free chunk's footer
  have Kfoot : ∀ c ∈ chunks, c.inuse = false →
      read64 m' (c.addr + c.size) = read64 m (c.addr + c.size) := by
    intro c hc hf
    have hb := HH.end_bnd hc
    have hca := hal c hc
    have hsz := (walk_sizes HH.walk c hc).1
    have hcb1 := hcb c hc
    have hn16 := HH.bnd_ne_node hi (.inr ⟨_, hfree, rfl, rfl, hvmem⟩) hb 16 (by omega) (by omega)
    have hn24 := HH.bnd_ne_node hi (.inr ⟨_, hfree, rfl, rfl, hvmem⟩) hb 24 (by omega) (by omega)
    simp only at hn16 hn24
    have hno : c.addr + c.size ≠ oldfirst + 24 := by
      rcases honode with rfl | ⟨cx, hcx, hxa, hxf, hxm⟩
      · have := binAt_geo j hj; unfold heapStart at hcb1; omega
      · exact HH.bnd_ne_node hj (.inr ⟨cx, hcx, hxa, hxf, hxm⟩) hb 24 (by omega) (by omega)
    unfold heapStart at hcb1 hvlo
    exact K _ (foot_free B hc hf).2 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) hno (by unfold binblocksAddr avAddr; omega)
  -- node geometry
  have hnodeGeo : ∀ k, 0 < k → k < numBins → ∀ x ∈ bins k,
      x % 16 = 0 ∧ heapStart ≤ x ∧ (∀ o, 16 ≤ o → o < 32 → vsaFoot H (x + o)) := by
    intro k hk0 hk x hx
    obtain ⟨c, hc, hca, hf⟩ := HH.member hk0 hk hx
    subst hca
    exact ⟨hal c hc, (hcb c hc).1, B.node_foot hk0 hk (.inr hx)⟩
  -- the moved bins, by index
  have hbinsJ : updBins (updBins bins i []) j (v :: bins j) j = v :: bins j := updBins_same _ _ _
  have hbinsI : updBins (updBins bins i []) j (v :: bins j) i = [] := by
    rw [updBins_other _ _ (Ne.symm hji), updBins_same]
  have hbinsK : ∀ k, k ≠ i → k ≠ j → updBins (updBins bins i []) j (v :: bins j) k = bins k :=
    fun k h1 h2 => by rw [updBins_other _ _ h2, updBins_other _ _ h1]
  -- bin `j`'s old ring, split at its head
  obtain ⟨post, hpost⟩ : ∃ post, bins j ++ [binAt j] = oldfirst :: post :=
    List.head?_eq_some_iff.1 hfirst
  have hndJ : (bins j ++ [binAt j]).Nodup := by
    refine List.nodup_append.2 ⟨HH.bins_nodup j, by simp, fun x hx y hy => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    subst hy; exact hneJ x hx
  have hagJ : ∀ a b, [a, b] <:+: ([] ++ [binAt j]) ∨ [a, b] <:+: (oldfirst :: post) →
      fdOf m' a = fdOf m a ∧ bkOf m' b = bkOf m b := by
    rintro a b (hab | hab)
    · exfalso
      have hl := hab.length_le
      simp only [List.length_cons, List.length_nil, List.nil_append] at hl
      omega
    · have hab' : [a, b] <:+: bins j ++ [binAt j] := by rw [hpost]; exact hab
      have ha : a ∈ bins j := infix_fst_mem_init hab'
      have hb : b ∈ post := infix_snd_mem hab
      have hbm : b ∈ bins j ∨ b = binAt j := by
        have : b ∈ bins j ++ [binAt j] := by rw [hpost]; exact List.mem_cons_of_mem _ hb
        rcases List.mem_append.mp this with h1 | h1
        · exact .inl h1
        · exact .inr (by simpa using h1)
      obtain ⟨ha16, halo, haf⟩ := hnodeGeo j hj0 hj a ha
      have hbo : b ≠ oldfirst := by
        rw [hpost] at hndJ
        exact fun he => (List.nodup_cons.1 hndJ).1 (he ▸ hb)
      refine ⟨Kfd a ha16 haf (fun he => hvJ (he ▸ ha)) ?_ (hneJ a ha), ?_⟩
      · have := binAt_geo i hi; unfold heapStart at halo; omega
      rcases hbm with hbm | rfl
      · obtain ⟨hb16, hblo, hbf⟩ := hnodeGeo j hj0 hj b hbm
        refine Kbk b hb16 ?_ hbf (fun he => hvJ (he ▸ hbm)) ?_ hbo
        · have := binAt_geo i hi; unfold heapStart at hblo; unfold avAddr; omega
        · have := binAt_geo i hi; unfold heapStart at hblo; omega
      · refine Kbk (binAt j) hgj.1 (by unfold avAddr; unfold binAt avAddr at hgj ⊢; omega)
          (B.node_foot hj0 hj (.inl rfl)) ?_ ?_ hbo
        · have := hvb.1; unfold heapStart at *; omega
        · intro he; exact hji (by
            have : (16 : Nat) * j = 16 * i := by unfold binAt avAddr at he; omega
            omega)
  -- `oldfirst` is bin `j`'s header or one of its members, never another bin's
  have hoNe : ∀ k, 0 < k → k < numBins → k ≠ j → ∀ x ∈ bins k, x ≠ oldfirst := by
    intro k hk0 hk hkj x hx
    rcases hofm with hm | rfl
    · exact fun he => hkj (HH.bin_unique hk0 hk hj0 hj (he ▸ hx) hm)
    · obtain ⟨_, hxlo, _⟩ := hnodeGeo k hk0 hk x hx
      have := binAt_geo j hj
      unfold heapStart at hxlo
      omega
  have hbinlist : ∀ k, 0 < k → k < numBins →
      BinList m' k (updBins (updBins bins i []) j (v :: bins j) k) := by
    intro k hk0 hk
    by_cases hkj : k = j
    · subst hkj
      rw [hbinsJ]
      refine binList_iff_ring.2 ⟨?_, ?_⟩
      · show Links m' (binAt k :: (v :: bins k) ++ [binAt k])
        have hold : Links m ([] ++ binAt k :: oldfirst :: post) := by
          have hr : Ring m (binAt k) (bins k) := hringJ
          unfold Ring at hr
          rw [show binAt k :: bins k ++ [binAt k] = binAt k :: (bins k ++ [binAt k]) from rfl,
            hpost] at hr
          exact hr
        have hnew := links_link (pre := []) (post := post) hold hfdJ hbkV hfdV hbkO hagJ
        rw [show binAt k :: (v :: bins k) ++ [binAt k] =
          [] ++ binAt k :: v :: oldfirst :: post by
            simp only [List.nil_append, List.cons_append, List.cons.injEq, true_and]
            exact hpost]
        exact hnew
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · have := hvb.1; have := binAt_geo k hk; unfold heapStart at *; omega
        · exact hneJ x hx
    · by_cases hki : k = i
      · subst hki
        rw [hbinsI]
        exact binList_iff_ring.2 ⟨ring_nil_iff.2 ⟨hfdI, hbkI⟩, fun x hx => nomatch hx⟩
      · rw [hbinsK k hki hkj]
        obtain ⟨first, hf1, hchain⟩ := HH.bins_list k hk0 hk
        have hgk := binAt_geo k hk
        have hgi' := binAt_geo i hi
        have hgj' := binAt_geo j hj
        have hvlo' := hvb.1
        have hhdr : binAt k ≠ v ∧ binAt k ≠ binAt i ∧ binAt k ≠ binAt j ∧ binAt k ≠ oldfirst := by
          refine ⟨by unfold heapStart at hvlo'; omega, ?_, ?_, ?_⟩
          · intro he; exact hki (by unfold binAt avAddr at he; omega)
          · intro he; exact hkj (by unfold binAt avAddr at he; omega)
          · rcases hofm with hm | rfl
            · obtain ⟨_, holo, _⟩ := hnodeGeo j hj0 hj oldfirst hm
              unfold heapStart at holo; omega
            · intro he; exact hkj (by unfold binAt avAddr at he; omega)
        refine ⟨first, ?_, hchain.transport_links ?_ ?_⟩
        · show read64 m' (binAt k + 16) = some first
          rw [show read64 m' (binAt k + 16) = read64 m (binAt k + 16) from
            Kfd _ hgk.1 (B.node_foot hk0 hk (.inl rfl)) hhdr.1 hhdr.2.1 hhdr.2.2.1]
          exact hf1
        · exact (Kbk _ hgk.1 (by unfold binAt avAddr; omega)
            (B.node_foot hk0 hk (.inl rfl)) hhdr.1 hhdr.2.1 hhdr.2.2.2).symm
        · intro x hx
          obtain ⟨hx16, hxlo, hxf⟩ := hnodeGeo k hk0 hk x hx
          have hxv : x ≠ v := fun he => hki (HH.bin_unique hk0 hk hi0 hi (he ▸ hx) hvmem)
          have hxi : x ≠ binAt i := by unfold heapStart at hxlo; omega
          have hxj : x ≠ binAt j := by unfold heapStart at hxlo; omega
          exact ⟨(Kbk x hx16 (by unfold avAddr; unfold heapStart at hxlo; omega) hxf hxv hxi
              (hoNe k hk0 hk hkj x hx)).symm,
            (Kfd x hx16 hxf hxv hxi hxj).symm⟩
  -- globals above the bin array, and `av->top`
  have hoLoc : oldfirst + 32 ≤ 0x8001b520 ∨ heapStart ≤ oldfirst := by
    rcases hofm with hm | rfl
    · obtain ⟨_, holo, _⟩ := hnodeGeo j hj0 hj oldfirst hm
      exact .inr holo
    · have := binAt_geo j hj; exact .inl (by omega)
  have Kout : ∀ a, (∀ k, k < 8 → allocGlobal (a + k)) → a % 8 = 0 →
      0x8001b520 ≤ a → a + 8 ≤ 0x8001c170 → read64 m' a = read64 m a := by
    intro a hg ha h1 h2
    have hgi2 := binAt_geo i hi; have hgj2 := binAt_geo j hj
    refine Kglob a hg ha (by unfold heapStart; omega) (by omega) (by omega) (by omega) ?_
      (by unfold binblocksAddr avAddr; omega)
    rcases hoLoc with ho | ho
    · omega
    · unfold heapStart at ho; omega
  have Ktop : read64 m' topAddr = read64 m topAddr := by
    have hgi2 := binAt_geo i hi; have hgj2 := binAt_geo j hj
    refine Kglob topAddr (fun k hk => .inl ⟨by unfold topAddr avAddr; omega,
        by unfold topAddr avAddr; omega⟩) (by unfold topAddr avAddr; omega)
      (by unfold topAddr avAddr heapStart; omega) ?_ ?_ ?_ ?_
      (by unfold topAddr binblocksAddr avAddr; omega)
    · intro he; exact absurd he (by unfold topAddr binAt avAddr; omega)
    · intro he; exact absurd he (by unfold topAddr binAt avAddr; omega)
    · intro he; exact absurd he (by unfold topAddr binAt avAddr; omega)
    · rcases hoLoc with ho | ho
      · rcases hofm with hm | rfl
        · unfold topAddr avAddr; omega
        · unfold topAddr binAt avAddr; omega
      · unfold topAddr avAddr heapStart at *; omega
  have hglob : ∀ a, 0x8001b520 ≤ a → a + 8 ≤ 0x8001c170 →
      (∀ k, k < 8 → allocGlobal (a + k)) → a % 8 = 0 → read64 m' a = read64 m a :=
    fun a h1 h2 hg ha => Kout a hg ha h1 h2
  refine ⟨⟨{ sbrk_base := ?_, brk := ?_, brk_le := hbrk, top_ptr := by rw [Ktop]; exact HH.top_ptr
             top_le := htle, top_size := HH.top_size
             top_header := by rw [Khdr top (.inl rfl)]; exact HH.top_header
             top_pad := ?_, max_sbrked := ?_, mallinfo := ?_, first_prev := ?_
             walk := HH.walk.transport_headers (fun q hq => (Khdr q hq).symm)
             coalesced := HH.coalesced
             footer := fun c hc hf => by rw [Kfoot c hc hf]; exact HH.footer c hc hf
             bins_list := hbinlist, bins_nodup := ?_, bin_free := ?_, free_binned := ?_
             remainder := ?_, binblocks_present := by rw [hbbr]; rfl
             binblocks := ?_, live := HH.live, exact := HH.exact }, B.top_room⟩, hpage, ?_⟩
  · rw [hglob sbrkBaseAddr (by unfold sbrkBaseAddr; omega) (by unfold sbrkBaseAddr; omega)
      (fun k hk => .inr (.inr (.inl ⟨by unfold sbrkBaseAddr; omega,
        by unfold sbrkBaseAddr; omega⟩))) (by unfold sbrkBaseAddr; omega)]
    exact HH.sbrk_base
  · rw [hglob brkAddr (by unfold brkAddr; omega) (by unfold brkAddr; omega)
      (fun k hk => .inr (.inr (.inr (.inl ⟨by unfold brkAddr; omega,
        by unfold brkAddr; omega⟩)))) (by unfold brkAddr; omega)]
    exact HH.brk
  · rw [hglob topPadAddr (by unfold topPadAddr; omega) (by unfold topPadAddr; omega)
      (fun k hk => .inr (.inr (.inr (.inl ⟨by unfold topPadAddr; omega,
        by unfold topPadAddr; omega⟩)))) (by unfold topPadAddr; omega)]
    exact HH.top_pad
  · rw [hglob maxSbrkedAddr (by unfold maxSbrkedAddr; omega) (by unfold maxSbrkedAddr; omega)
      (fun k hk => .inr (.inr (.inr (.inl ⟨by unfold maxSbrkedAddr; omega,
        by unfold maxSbrkedAddr; omega⟩)))) (by unfold maxSbrkedAddr; omega)]
    exact HH.max_sbrked
  · rw [hglob mallinfoAddr (by unfold mallinfoAddr; omega) (by unfold mallinfoAddr; omega)
      (fun k hk => .inr (.inr (.inr (.inr (.inr ⟨by unfold mallinfoAddr; omega,
        by unfold mallinfoAddr; omega⟩))))) (by unfold mallinfoAddr; omega)]
    exact HH.mallinfo
  · rw [Khdr heapStart (by
      rcases HH.walk.head_or_top with he | he
      · exact .inl he
      · exact .inr he)]
    exact HH.first_prev
  · intro k
    by_cases hkj : k = j
    · subst hkj; rw [hbinsJ]; exact List.nodup_cons.2 ⟨hvJ, HH.bins_nodup k⟩
    · by_cases hki : k = i
      · subst hki; rw [hbinsI]; exact List.nodup_nil
      · rw [hbinsK k hki hkj]; exact HH.bins_nodup k
  · intro k q hk0 hk hq
    by_cases hkj : k = j
    · subst hkj; rw [hbinsJ] at hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨⟨q, sz, false⟩, hfree, rfl, rfl, fun h1 => hidx h1⟩
      · exact HH.bin_free k q hk0 hk hq
    · by_cases hki : k = i
      · subst hki; rw [hbinsI] at hq; cases hq
      · rw [hbinsK k hki hkj] at hq; exact HH.bin_free k q hk0 hk hq
  · intro c hc hf
    by_cases hcv : c.addr = v
    · refine ⟨j, hj0, hj, by rw [hbinsJ, hcv]; exact List.mem_cons_self, ?_⟩
      intro k hk0 hk hmem
      by_cases hkj : k = j
      · exact hkj
      · by_cases hki : k = i
        · subst hki; rw [hbinsI] at hmem; cases hmem
        · rw [hbinsK k hki hkj, hcv] at hmem
          exact absurd (HH.bin_unique hk0 hk hi0 hi hmem hvmem) hki
    · obtain ⟨k, hk0, hk, hmem, huniq⟩ := HH.free_binned c hc hf
      have hki : k ≠ i := by
        intro he; subst he; rw [hbin] at hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        exact hcv hmem
      refine ⟨k, hk0, hk, ?_, ?_⟩
      · by_cases hkj : k = j
        · subst hkj; rw [hbinsJ]; exact List.mem_cons_of_mem _ hmem
        · rw [hbinsK k hki hkj]; exact hmem
      · intro k' hk0' hk' hmem'
        by_cases hkj' : k' = j
        · subst hkj'; rw [hbinsJ] at hmem'
          rcases List.mem_cons.mp hmem' with he | hmem'
          · exact absurd he hcv
          · exact huniq k' hk0' hk' hmem'
        · by_cases hki' : k' = i
          · subst hki'; rw [hbinsI] at hmem'; cases hmem'
          · rw [hbinsK k' hki' hkj'] at hmem'; exact huniq k' hk0' hk' hmem'
  · by_cases h1i : i = 1
    · subst h1i; rw [hbinsI]; exact Nat.zero_le 1
    · rw [hbinsK 1 (fun he => h1i he.symm) (fun he => hj1 he.symm)]; exact HH.remainder
  · intro bb hbb k hk1 hk hne
    rw [hbbr] at hbb; cases hbb
    by_cases hkj : k = j
    · subst hkj; exact hbbset
    · by_cases hki : k = i
      · subst hki; rw [hbinsI] at hne; exact absurd rfl hne
      · rw [hbinsK k hki hkj] at hne
        obtain ⟨bb0, hbb0⟩ := Option.isSome_iff_exists.1 HH.binblocks_present
        exact hbbkeep bb0 hbb0 (k / 4) (HH.binblocks bb0 hbb0 k hk1 hk hne)
  · intro bb hbb
    rw [hbbr] at hbb; cases hbb; exact hbblt

end VsaIris.VsaHeap
