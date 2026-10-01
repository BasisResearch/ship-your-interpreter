import VsaIris.OmegaHint
import VsaIris.Vsa.HeapTake

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.MallocFast

def MoveAtW (i v pred succ : Nat) (a : Nat) : Prop :=
  (binAt i + 16 ≤ a ∧ a < binAt i + 32) ∨ (v + 16 ≤ a ∧ a < v + 32) ∨
    (pred + 16 ≤ a ∧ a < pred + 24) ∨ (succ + 24 ≤ a ∧ a < succ + 32) ∨
    (binblocksAddr ≤ a ∧ a < binblocksAddr + 8)

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

  have hvmem : v ∈ bins i := by rw [hbin]; exact List.mem_cons_self
  have hv16 : v % 16 = 0 := hal _ hfree
  have hvb := hcb _ hfree
  simp only at hv16 hvb
  have hvlo : heapStart ≤ v := hvb.1
  have hpm := pred_mem (L := bins j) (fun x hx => by rw [hpos]; simp [hx]) hpred
  have hsm := succ_mem (L := bins j) (fun x hx => by rw [hpos]; simp [hx]) hsucc
  obtain ⟨hp16, hpnode⟩ := HH.node hj0 hj hpm
  obtain ⟨hs16, hsnode⟩ := HH.node hj0 hj hsm
  have hneJ := (binList_iff_ring.1 (HH.bins_list j hj0 hj)).2
  have hvJ : v ∉ bins j := fun hc => hji (HH.bin_unique hj0 hj hi0 hi hc hvmem)
  have hploc := HH.node_loc hj0 hj hpm
  have hsloc := HH.node_loc hj0 hj hsm

  have K : ∀ a, (∀ k, k < 8 → vsaFoot H (a + k)) → a % 8 = 0 →
      a ≠ binAt i + 16 → a ≠ binAt i + 24 → a ≠ v + 16 → a ≠ v + 24 →
      a ≠ pred + 16 → a ≠ succ + 24 → a ≠ binblocksAddr →
      read64 m' a = read64 m a := by
    intro a hf ha h1 h2 h3 h4 h5 h6 h7
    refine read64_keep fun k hk => hag _ (hf k hk) ?_
    unfold binblocksAddr avAddr at h7
    unfold MoveAtW binblocksAddr avAddr
    omega

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

  have Kfd : ∀ k x, 0 < k → k < numBins → (x = binAt k ∨ x ∈ bins k) → x ≠ v → x ≠ binAt i →
      x ≠ pred → fdOf m' x = fdOf m x := by
    intro k x hk0 hk hx h1 h2 h3
    obtain ⟨hx16, -⟩ := HH.node hk0 hk hx
    have hxl := HH.node_loc hk0 hk hx
    refine B.keep_fd hag hk0 hk hx fun w hw => ?_
    have := binAt_geo k hk
    unfold MoveAtW binblocksAddr at hw; unfold heapStart binAt avAddr at *; omega
  have Kbk : ∀ k x, 0 < k → k < numBins → (x = binAt k ∨ x ∈ bins k) → x ≠ v → x ≠ binAt i →
      x ≠ succ → bkOf m' x = bkOf m x := by
    intro k x hk0 hk hx h1 h2 h3
    obtain ⟨hx16, -⟩ := HH.node hk0 hk hx
    have hxl := HH.node_loc hk0 hk hx
    refine B.keep_bk hag hk0 hk hx fun w hw => ?_
    have := binAt_geo k hk
    unfold MoveAtW binblocksAddr at hw; unfold heapStart binAt avAddr at *; omega

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

  have hbinsJ : updBins (updBins bins i []) j (pre' ++ v :: post') j = pre' ++ v :: post' :=
    updBins_same _ _ _
  have hbinsI : updBins (updBins bins i []) j (pre' ++ v :: post') i = [] := by
    rw [updBins_other _ _ (Ne.symm hji), updBins_same]
  have hbinsK : ∀ k, k ≠ i → k ≠ j → updBins (updBins bins i []) j (pre' ++ v :: post') k = bins k :=
    fun k h1 h2 => by rw [updBins_other _ _ h2, updBins_other _ _ h1]

  have hnd := HH.bins_nodup j
  rw [hpos] at hnd
  have hdisj : ∀ a ∈ pre', ∀ b ∈ post', a ≠ b := fun a ha b hb =>
    (List.nodup_append.mp hnd).2.2 a ha b hb
  have hbinlist : ∀ k, 0 < k → k < numBins →
      BinList m' k (updBins (updBins bins i []) j (pre' ++ v :: post') k) := by
    intro k hk0 hk
    by_cases hkj : k = j
    · subst hkj
      rw [hbinsJ]
      have hvi : ∀ x, (x = binAt k ∨ x ∈ bins k) → x ≠ v := fun x hx => HH.nodes_ne hk0 hk hi0 hi hji hx (.inr hvmem)
      have hii : ∀ x, (x = binAt k ∨ x ∈ bins k) → x ≠ binAt i := fun x hx => HH.nodes_ne hk0 hk hi0 hi hji hx (.inl rfl)
      exact binList_insert (HH.bins_list k hk0 hk) hpos (HH.bins_nodup k)
        (fun he => hvi _ (.inl rfl) he.symm) hpred hsucc hfdP hbkV hfdV hbkS
        (fun x hx hne => Kfd k x hk0 hk hx (hvi x hx) (hii x hx) hne)
        (fun x hx hne => Kbk k x hk0 hk hx (hvi x hx) (hii x hx) hne)
    · by_cases hki : k = i
      · subst hki
        rw [hbinsI]
        exact binList_iff_ring.2 ⟨ring_nil_iff.2 ⟨hfdI, hbkI⟩, fun x hx => nomatch hx⟩
      · rw [hbinsK k hki hkj]
        have hO : ∀ x, (x = binAt k ∨ x ∈ bins k) → x ≠ v := fun x hx => HH.nodes_ne hk0 hk hi0 hi hki hx (.inr hvmem)
        have hI : ∀ x, (x = binAt k ∨ x ∈ bins k) → x ≠ binAt i := fun x hx => HH.nodes_ne hk0 hk hi0 hi hki hx (.inl rfl)
        have hJ : ∀ x, (x = binAt k ∨ x ∈ bins k) → ∀ y, (y = binAt j ∨ y ∈ bins j) → x ≠ y :=
          fun x hx y hy => HH.nodes_ne hk0 hk hj0 hj hkj hx hy
        exact binList_keep (HH.bins_list k hk0 hk)
          (fun x hx => Kfd k x hk0 hk hx (hO x hx) (hI x hx) (hJ x hx _ hpm))
          (fun x hx => Kbk k x hk0 hk hx (hO x hx) (hI x hx) (hJ x hx _ hsm))

  obtain ⟨gS, gB, gP, gM, gI, gT⟩ := HH.keep_scal hag fun w hg hu => by
    unfold allocGlobal InRange at hg; unfold MoveAtW at hu
    unfold binAt binblocksAddr topAddr heapStart avAddr at *; omega
  refine ⟨⟨{ sbrk_base := gS, brk := gB, brk_le := hbrk, top_ptr := gT
             top_le := htle, top_size := HH.top_size
             top_header := by rw [Khdr top (.inl rfl)]; exact HH.top_header
             top_pad := gP, max_sbrked := gM, mallinfo := gI, first_prev := ?_
             walk := HH.walk.transport_headers (fun q hq => (Khdr q hq).symm)
             coalesced := HH.coalesced
             footer := fun c hc hf => by rw [Kfoot c hc hf]; exact HH.footer c hc hf
             bins_list := hbinlist, bins_nodup := ?_, bin_free := ?_, free_binned := ?_
             remainder := ?_, binblocks_present := by rw [hbbr]; rfl
             binblocks := ?_, live := HH.live, exact := HH.exact }, B.top_room⟩, hpage, ?_⟩
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
