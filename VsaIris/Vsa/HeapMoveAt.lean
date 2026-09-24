import VsaIris.Vsa.HeapMove

/-!
# Moving a free chunk into a bin at any position

`PHeapAt.moveBin` links the moved chunk in at the head of its new bin. A large
bin is kept sorted by size, so `_malloc_r` re-binning a large last remainder
(`0x80004c70`) links it in before the first member no larger than it, walking
the bin to find that point. `PHeapAt.moveBinAt` is the move at any insertion
point: between `pred` (the header or a member) and its successor `succ`. The
words written are bin `i`'s links, the chunk's links, `pred`'s `fd`, `succ`'s
`bk` and the bitmap.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.MallocFast

/-- The seven words a move to an insertion point writes. -/
def MoveAtW (i v pred succ : Nat) (a : Nat) : Prop :=
  (binAt i + 16 ≤ a ∧ a < binAt i + 32) ∨ (v + 16 ≤ a ∧ a < v + 32) ∨
    (pred + 16 ≤ a ∧ a < pred + 24) ∨ (succ + 24 ≤ a ∧ a < succ + 32) ∨
    (binblocksAddr ≤ a ∧ a < binblocksAddr + 8)

/-- **Move a free chunk into a bin at an insertion point.** Emptying bin `i`
of its single member `v` and linking `v` in between `pred` and `succ` of bin
`j`, with `j`'s block bit set in `binblocks`, gives the page-aligned heap at
the moved bins. -/
theorem PHeapAt.moveBinAt {m m' : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} (h : PHeapAt m H top brkv chunks bins)
    {i j v sz pred succ bb' : Nat} {pre' post' : List Nat}
    (hi0 : 0 < i) (hi : i < numBins) (hj0 : 0 < j) (hj : j < numBins) (hji : j ≠ i) (hj1 : j ≠ 1)
    (hbin : bins i = [v]) (hfree : FreeAt chunks v sz) (hidx : 1 < j → binIndex sz = j)
    (hpos : bins j = pre' ++ post')
    (hpred : (binAt j :: pre').getLast? = some pred) (hsucc : (post' ++ [binAt j]).head? = some succ)
    (hfdI : fdOf m' (binAt i) = some (binAt i)) (hbkI : bkOf m' (binAt i) = some (binAt i))
    (hfdV : fdOf m' v = some succ) (hbkV : bkOf m' v = some pred)
    (hfdP : fdOf m' pred = some v) (hbkS : bkOf m' succ = some v)
    (hbbr : read64 m' binblocksAddr = some bb') (hbblt : bb' < 2 ^ 32)
    (hbbset : bb' / 2 ^ (j / 4) % 2 = 1)
    (hbbkeep : ∀ bb, read64 m binblocksAddr = some bb →
      ∀ k, bb / 2 ^ k % 2 = 1 → bb' / 2 ^ k % 2 = 1)
    (hag : ∀ a, vsaFoot H a → ¬ MoveAtW i v pred succ a → m'[a]? = m[a]?) :
    PHeapAt m' H top brkv chunks (updBins (updBins bins i []) j (pre' ++ v :: post')) := by
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
  obtain ⟨hp16, hpnode⟩ := HH.node hj0 hj hpm
  obtain ⟨hs16, hsnode⟩ := HH.node hj0 hj hsm
  -- the bins as rings
  have hringJ := (binList_iff_ring.1 (HH.bins_list j hj0 hj)).1
  have hneJ := (binList_iff_ring.1 (HH.bins_list j hj0 hj)).2
  have hvJ : v ∉ bins j := fun hc => hji (HH.bin_unique hj0 hj hi0 hi hc hvmem)
  -- node geometry
  have hnodeGeo : ∀ k, 0 < k → k < numBins → ∀ x ∈ bins k,
      x % 16 = 0 ∧ heapStart ≤ x ∧ (∀ o, 16 ≤ o → o < 32 → vsaFoot H (x + o)) := by
    intro k hk0 hk x hx
    obtain ⟨c, hc, hca, hf⟩ := HH.member hk0 hk hx
    subst hca
    exact ⟨hal c hc, (hcb c hc).1, B.node_foot hk0 hk (.inr hx)⟩
  -- a node of bin `j` lies in the arena or is bin `j`'s header
  have hjloc : ∀ x, (x = binAt j ∨ x ∈ bins j) → x = binAt j ∨ heapStart ≤ x := by
    rintro x (h1 | h1)
    · exact .inl h1
    · exact .inr (hnodeGeo j hj0 hj x h1).2.1
  have hploc := hjloc pred hpm
  have hsloc := hjloc succ hsm
  have hpv : pred ≠ v := by
    rcases hpm with rfl | h1
    · unfold heapStart at hvlo; omega
    · exact fun he => hvJ (he ▸ h1)
  have hsv : succ ≠ v := by
    rcases hsm with rfl | h1
    · unfold heapStart at hvlo; omega
    · exact fun he => hvJ (he ▸ h1)
  have hpi : pred ≠ binAt i := by
    rcases hploc with rfl | h1
    · intro he; exact hji (by unfold binAt avAddr at he; omega)
    · unfold heapStart at h1; omega
  have hsi : succ ≠ binAt i := by
    rcases hsloc with rfl | h1
    · intro he; exact hji (by unfold binAt avAddr at he; omega)
    · unfold heapStart at h1; omega
  -- the words the move keeps
  have K : ∀ a, (∀ k, k < 8 → vsaFoot H (a + k)) → a % 8 = 0 →
      a ≠ binAt i + 16 → a ≠ binAt i + 24 → a ≠ v + 16 → a ≠ v + 24 →
      a ≠ pred + 16 → a ≠ succ + 24 → a ≠ binblocksAddr →
      read64 m' a = read64 m a := by
    intro a hf ha h1 h2 h3 h4 h5 h6 h7
    refine read64_keep fun k hk => hag _ (hf k hk) ?_
    unfold binblocksAddr avAddr at h7
    unfold MoveAtW binblocksAddr avAddr
    omega
  -- globals below the arena
  have Kglob : ∀ a, (∀ k, k < 8 → allocGlobal (a + k)) → a % 8 = 0 → a + 8 ≤ heapStart →
      a ≠ binAt i + 16 → a ≠ binAt i + 24 → a ≠ pred + 16 → a ≠ succ + 24 →
      a ≠ binblocksAddr → read64 m' a = read64 m a := by
    intro a hg ha hs h1 h2 h5 h6 h7
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
    have hnp := HH.bnd_ne_node hj hpnode hq 8 (by omega) (by omega)
    have hns := HH.bnd_ne_node hj hsnode hq 16 (by omega) (by omega)
    unfold heapStart at hqlo hvlo
    exact K _ (foot_header B hq) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by unfold binblocksAddr avAddr; omega)
  -- a node's `fd` and `bk`, away from the link words the move writes
  have Kfd : ∀ x, x % 16 = 0 → (∀ k, 16 ≤ k → k < 32 → vsaFoot H (x + k)) →
      x ≠ v → x ≠ binAt i → x ≠ pred → fdOf m' x = fdOf m x := by
    intro x hx16 hxf h1 h2 h3
    exact K _ (fun k hk => by
        have := hxf (16 + k) (by omega) (by omega)
        rwa [show x + (16 + k) = x + 16 + k by omega] at this)
      (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by unfold binblocksAddr avAddr; omega)
  have Kbk : ∀ x, x % 16 = 0 → avAddr + 16 ≤ x → (∀ k, 16 ≤ k → k < 32 → vsaFoot H (x + k)) →
      x ≠ v → x ≠ binAt i → x ≠ succ → bkOf m' x = bkOf m x := by
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
    have hnp := HH.bnd_ne_node hj hpnode hb 16 (by omega) (by omega)
    have hns := HH.bnd_ne_node hj hsnode hb 24 (by omega) (by omega)
    unfold heapStart at hcb1 hvlo
    exact K _ (foot_free B hc hf).2 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by unfold binblocksAddr avAddr; omega)
  -- the moved bins, by index
  have hbinsJ : updBins (updBins bins i []) j (pre' ++ v :: post') j = pre' ++ v :: post' :=
    updBins_same _ _ _
  have hbinsI : updBins (updBins bins i []) j (pre' ++ v :: post') i = [] := by
    rw [updBins_other _ _ (Ne.symm hji), updBins_same]
  have hbinsK : ∀ k, k ≠ i → k ≠ j → updBins (updBins bins i []) j (pre' ++ v :: post') k = bins k :=
    fun k h1 h2 => by rw [updBins_other _ _ h2, updBins_other _ _ h1]
  -- bin `j`'s old ring, split at the insertion point
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.1 hpred
  obtain ⟨zs, hzs⟩ := List.head?_eq_some_iff.1 hsucc
  have hnd := HH.bins_nodup j
  rw [hpos] at hnd
  have hbj_ne : ∀ x ∈ pre' ++ post', x ≠ binAt j := fun x hx => hneJ x (by rw [hpos]; exact hx)
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
  have hnodeJ : ∀ x, x ∈ binAt j :: pre' ∨ x ∈ post' ++ [binAt j] → x = binAt j ∨ x ∈ bins j := by
    rintro x (hx | hx)
    · rcases List.mem_cons.mp hx with h1 | h1
      · exact .inl h1
      · exact .inr (by rw [hpos]; exact List.mem_append_left _ h1)
    · rcases List.mem_append.mp hx with h1 | h1
      · exact .inr (by rw [hpos]; exact List.mem_append_right _ h1)
      · exact .inl (List.mem_singleton.mp h1)
  have hfdkeepJ : ∀ a, (a = binAt j ∨ a ∈ bins j) → a ≠ pred → fdOf m' a = fdOf m a := by
    intro a ha hne
    rcases ha with rfl | ha
    · exact Kfd _ hgj.1 (B.node_foot hj0 hj (.inl rfl))
        (by have := hvb.1; unfold heapStart at *; omega)
        (by intro he; exact hji (by unfold binAt avAddr at he; omega)) hne
    · obtain ⟨ha16, halo, haf⟩ := hnodeGeo j hj0 hj a ha
      exact Kfd a ha16 haf (fun he => hvJ (he ▸ ha))
        (by unfold heapStart at halo; omega) hne
  have hbkkeepJ : ∀ b, (b = binAt j ∨ b ∈ bins j) → b ≠ succ → bkOf m' b = bkOf m b := by
    intro b hb hne
    rcases hb with rfl | hb
    · exact Kbk _ hgj.1 (by unfold binAt avAddr; unfold binAt avAddr at hgj; omega)
        (B.node_foot hj0 hj (.inl rfl))
        (by have := hvb.1; unfold heapStart at *; omega)
        (by intro he; exact hji (by unfold binAt avAddr at he; omega)) hne
    · obtain ⟨hb16, hblo, hbf⟩ := hnodeGeo j hj0 hj b hb
      exact Kbk b hb16 (by unfold avAddr; unfold heapStart at hblo; omega) hbf
        (fun he => hvJ (he ▸ hb)) (by unfold heapStart at hblo; omega) hne
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
      refine ⟨hfdkeepJ a (hnodeJ a (.inl ha)) hane, hbkkeepJ b (hnodeJ b (.inl hb)) ?_⟩
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
      refine ⟨hfdkeepJ a (hnodeJ a (.inr ha)) ?_, hbkkeepJ b (hnodeJ b (.inr hb)) hbne⟩
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
  have hoNe : ∀ k, 0 < k → k < numBins → k ≠ j → ∀ x ∈ bins k, x ≠ pred ∧ x ≠ succ := by
    intro k hk0 hk hkj x hx
    have hne : ∀ y, (y = binAt j ∨ y ∈ bins j) → x ≠ y := by
      rintro y (rfl | hy) he
      · obtain ⟨_, hxlo, _⟩ := hnodeGeo k hk0 hk x hx
        unfold heapStart at hxlo; subst he; omega
      · subst he; exact hkj (HH.bin_unique hk0 hk hj0 hj hx hy)
    exact ⟨hne pred hpm, hne succ hsm⟩
  have hbinlist : ∀ k, 0 < k → k < numBins →
      BinList m' k (updBins (updBins bins i []) j (pre' ++ v :: post') k) := by
    intro k hk0 hk
    by_cases hkj : k = j
    · subst hkj
      rw [hbinsJ]
      refine binList_iff_ring.2 ⟨ring_j, ?_⟩
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hbj_ne x (List.mem_append_left _ hx)
      · rcases List.mem_cons.mp hx with rfl | hx
        · have := hvb.1; have := binAt_geo k hk; unfold heapStart at *; omega
        · exact hbj_ne x (List.mem_append_right _ hx)
    · by_cases hki : k = i
      · subst hki
        rw [hbinsI]
        exact binList_iff_ring.2 ⟨ring_nil_iff.2 ⟨hfdI, hbkI⟩, fun x hx => nomatch hx⟩
      · rw [hbinsK k hki hkj]
        obtain ⟨first, hf1, hchain⟩ := HH.bins_list k hk0 hk
        have hgk := binAt_geo k hk
        have hvlo' := hvb.1
        have hhdr : binAt k ≠ v ∧ binAt k ≠ binAt i ∧ binAt k ≠ pred ∧ binAt k ≠ succ := by
          have hjne : ∀ y, (y = binAt j ∨ y ∈ bins j) → binAt k ≠ y := by
            rintro y (rfl | hy) he
            · exact hkj (by unfold binAt avAddr at he; omega)
            · obtain ⟨_, hylo, _⟩ := hnodeGeo j hj0 hj y hy
              unfold heapStart at hylo; omega
          refine ⟨by unfold heapStart at hvlo'; omega, ?_, hjne pred hpm, hjne succ hsm⟩
          intro he; exact hki (by unfold binAt avAddr at he; omega)
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
          exact ⟨(Kbk x hx16 (by unfold avAddr; unfold heapStart at hxlo; omega) hxf hxv hxi
              (hoNe k hk0 hk hkj x hx).2).symm,
            (Kfd x hx16 hxf hxv hxi (hoNe k hk0 hk hkj x hx).1).symm⟩
  -- globals above the bin array, and `av->top`
  have hnloc : ∀ y, (y = binAt j ∨ heapStart ≤ y) → y + 32 ≤ 0x8001b520 ∨ heapStart ≤ y := by
    rintro y (rfl | h1)
    · exact .inl (by omega)
    · exact .inr h1
  have hpl := hnloc pred hploc
  have hsl := hnloc succ hsloc
  have Kout : ∀ a, (∀ k, k < 8 → allocGlobal (a + k)) → a % 8 = 0 →
      0x8001b520 ≤ a → a + 8 ≤ 0x8001c170 → read64 m' a = read64 m a := by
    intro a hg ha h1 h2
    refine Kglob a hg ha (by unfold heapStart; omega) (by omega) (by omega) ?_ ?_
      (by unfold binblocksAddr avAddr; omega)
    · rcases hpl with hp | hp
      · omega
      · unfold heapStart at hp; omega
    · rcases hsl with hs | hs
      · omega
      · unfold heapStart at hs; omega
  have Ktop : read64 m' topAddr = read64 m topAddr := by
    refine Kglob topAddr (fun k hk => .inl ⟨by unfold topAddr avAddr; omega,
        by unfold topAddr avAddr; omega⟩) (by unfold topAddr avAddr; omega)
      (by unfold topAddr avAddr heapStart; omega) ?_ ?_ ?_ ?_
      (by unfold topAddr binblocksAddr avAddr; omega)
    · intro he; exact absurd he (by unfold topAddr binAt avAddr; omega)
    · intro he; exact absurd he (by unfold topAddr binAt avAddr; omega)
    · rcases hploc with rfl | hp
      · unfold topAddr binAt avAddr; omega
      · unfold topAddr avAddr heapStart at *; omega
    · rcases hsloc with rfl | hs
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
    · subst hkj; rw [hbinsJ]
      rw [List.nodup_append]
      have hvpost : v ∉ post' := fun hm => hvJ (by rw [hpos]; exact List.mem_append_right _ hm)
      refine ⟨(List.nodup_append.mp hnd).1,
        List.nodup_cons.2 ⟨hvpost, (List.nodup_append.mp hnd).2.1⟩, ?_⟩
      intro a ha b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact fun he => hvJ (by rw [hpos, ← he]; exact List.mem_append_left _ ha)
      · exact hdisj a ha b hb
    · by_cases hki : k = i
      · subst hki; rw [hbinsI]; exact List.nodup_nil
      · rw [hbinsK k hki hkj]; exact HH.bins_nodup k
  · intro k q hk0 hk hq
    by_cases hkj : k = j
    · subst hkj; rw [hbinsJ] at hq
      rcases List.mem_append.mp hq with hq | hq
      · exact HH.bin_free k q hk0 hk (by rw [hpos]; exact List.mem_append_left _ hq)
      · rcases List.mem_cons.mp hq with rfl | hq
        · exact ⟨⟨q, sz, false⟩, hfree, rfl, rfl, fun h1 => hidx h1⟩
        · exact HH.bin_free k q hk0 hk (by rw [hpos]; exact List.mem_append_right _ hq)
    · by_cases hki : k = i
      · subst hki; rw [hbinsI] at hq; cases hq
      · rw [hbinsK k hki hkj] at hq; exact HH.bin_free k q hk0 hk hq
  · have hjmem : ∀ x, x ∈ pre' ++ v :: post' ↔ x = v ∨ x ∈ bins j := by
      intro x; rw [hpos]; simp only [List.mem_append, List.mem_cons]
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
    by_cases hcv : c.addr = v
    · refine ⟨j, hj0, hj, by rw [hbinsJ, hjmem]; exact .inl hcv, ?_⟩
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
        · subst hkj; rw [hbinsJ, hjmem]; exact .inr hmem
        · rw [hbinsK k hki hkj]; exact hmem
      · intro k' hk0' hk' hmem'
        by_cases hkj' : k' = j
        · subst hkj'; rw [hbinsJ, hjmem] at hmem'
          rcases hmem' with he | hmem'
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
