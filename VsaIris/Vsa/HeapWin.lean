import VsaIris.Vsa.HeapTake

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.MallocFast

section Win

variable {m m' : Mem} {H : List (Nat × Nat)} {top brkv : Nat} {chunks : List Chunk}
  {bins : Nat → List Nat} {U : Nat → Prop}

theorem win_read64 (hag : ∀ w, vsaFoot H w → ¬ U w → m'[w]? = m[w]?) {a : Nat}
    (hf : ∀ k, k < 8 → vsaFoot H (a + k)) (hu : ∀ k, k < 8 → ¬ U (a + k)) :
    read64 m' a = read64 m a :=
  read64_keep fun k hk => hag _ (hf k hk) (hu k hk)

private theorem win_glob (hag : ∀ w, vsaFoot H w → ¬ U w → m'[w]? = m[w]?)
    (hG : ∀ w, allocGlobal w → U w → topAddr ≤ w ∧ w < topAddr + 8) (a : Nat)
    (hg : ∀ k, k < 8 → allocGlobal (a + k)) (ht : a + 8 ≤ topAddr ∨ topAddr + 8 ≤ a) :
    read64 m' a = read64 m a :=
  win_read64 hag (fun k hk => .inl (hg k hk)) fun k hk hu => by
    have := hG _ (hg k hk) hu; omega

theorem _root_.Vsa.Sim.DlHeap.HeapAt.keep_globals {R : Nat × Nat → Prop} (h : HeapAt m H R top brkv chunks bins)
    (hag : ∀ w, vsaFoot H w → ¬ U w → m'[w]? = m[w]?)
    (hG : ∀ w, allocGlobal w → U w → topAddr ≤ w ∧ w < topAddr + 8) :
    read64 m' sbrkBaseAddr = some heapStart ∧ read64 m' brkAddr = some brkv ∧
    read64 m' topPadAddr = some 0 ∧ (read64 m' maxSbrkedAddr).isSome ∧
    (read64 m' mallinfoAddr).isSome ∧ read64 m' binblocksAddr = read64 m binblocksAddr ∧
    ∀ i, 0 < i → i < numBins →
      read64 m' (binAt i + 16) = read64 m (binAt i + 16) ∧
      read64 m' (binAt i + 24) = read64 m (binAt i + 24) := by
  have K := win_glob hag hG
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun i h0 h1 => ⟨?_, ?_⟩⟩
  · rw [K _ (fun k hk => .inr (.inr (.inl ⟨by unfold sbrkBaseAddr; omega, by unfold sbrkBaseAddr; omega⟩)))
      (by unfold sbrkBaseAddr topAddr avAddr; omega)]; exact h.sbrk_base
  · rw [K _ (fun k hk => .inr (.inr (.inr (.inl ⟨by unfold brkAddr; omega, by unfold brkAddr; omega⟩))))
      (by unfold brkAddr topAddr avAddr; omega)]; exact h.brk
  · rw [K _ (fun k hk => .inr (.inr (.inr (.inl ⟨by unfold topPadAddr; omega, by unfold topPadAddr; omega⟩))))
      (by unfold topPadAddr topAddr avAddr; omega)]; exact h.top_pad
  · rw [K _ (fun k hk => .inr (.inr (.inr (.inl ⟨by unfold maxSbrkedAddr; omega,
      by unfold maxSbrkedAddr; omega⟩)))) (by unfold maxSbrkedAddr topAddr avAddr; omega)]; exact h.max_sbrked
  · rw [K _ (fun k hk => .inr (.inr (.inr (.inr (.inr ⟨by unfold mallinfoAddr; omega,
      by unfold mallinfoAddr; omega⟩))))) (by unfold mallinfoAddr topAddr avAddr; omega)]; exact h.mallinfo
  · exact K _ (fun k hk => .inl ⟨by unfold binblocksAddr avAddr; omega, by unfold binblocksAddr avAddr; omega⟩)
      (by unfold binblocksAddr topAddr avAddr; omega)
  · exact K _ (fun k hk => .inl ⟨by unfold binAt avAddr; omega, by unfold binAt avAddr; unfold numBins at h1; omega⟩)
      (by unfold binAt topAddr avAddr; omega)
  · exact K _ (fun k hk => .inl ⟨by unfold binAt avAddr; omega, by unfold binAt avAddr; unfold numBins at h1; omega⟩)
      (by unfold binAt topAddr avAddr; omega)

theorem BlockHeapAt.keep_hdr (B : BlockHeapAt m H top brkv chunks bins)
    (hag : ∀ w, vsaFoot H w → ¬ U w → m'[w]? = m[w]?) {q : Nat}
    (hq : q = top ∨ ∃ c ∈ chunks, c.addr = q) (hu : ∀ w, U w → w < q + 8 ∨ q + 16 ≤ w) :
    read64 m' (q + 8) = read64 m (q + 8) :=
  win_read64 hag (foot_header B hq) fun k hk h => by have := hu _ h; omega

theorem BlockHeapAt.keep_free (B : BlockHeapAt m H top brkv chunks bins)
    (hag : ∀ w, vsaFoot H w → ¬ U w → m'[w]? = m[w]?)
    (hG : ∀ w, allocGlobal w → U w → topAddr ≤ w ∧ w < topAddr + 8)
    (hF : ∀ c ∈ chunks, c.inuse = false → ∀ w, U w →
      (w < c.addr + 16 ∨ c.addr + 32 ≤ w) ∧ (w < c.addr + c.size ∨ c.addr + c.size + 8 ≤ w)) :
    (∀ i, 0 < i → i < numBins → BinList m' i (bins i)) ∧
    ∀ c ∈ chunks, c.inuse = false → read64 m' (c.addr + c.size) = some c.size := by
  have HH := B.heap
  have G := (HH.keep_globals hag hG).2.2.2.2.2.2
  have hl : ∀ c ∈ chunks, c.inuse = false →
      read64 m' (c.addr + 16) = read64 m (c.addr + 16) ∧
      read64 m' (c.addr + 24) = read64 m (c.addr + 24) ∧
      read64 m' (c.addr + c.size) = read64 m (c.addr + c.size) := by
    intro c hc hf
    obtain ⟨hl, hft⟩ := foot_free B hc hf
    refine ⟨win_read64 hag (fun k hk => hl k (by omega)) fun k hk h => ?_,
      win_read64 hag (fun k hk => ?_) fun k hk h => ?_,
      win_read64 hag hft fun k hk h => ?_⟩
    · have := (hF c hc hf _ h).1; omega
    · have := hl (k + 8) (by omega)
      rwa [show c.addr + 16 + (k + 8) = c.addr + 24 + k by omega] at this
    · have := (hF c hc hf _ h).1; omega
    · have := (hF c hc hf _ h).2; omega
  refine ⟨fun i h0 h1 => ?_, fun c hc hf => (hl c hc hf).2.2.trans (HH.footer c hc hf)⟩
  obtain ⟨first, hfirst, hchain⟩ := HH.bins_list i h0 h1
  refine ⟨first, (G i h0 h1).1 ▸ hfirst, hchain.transport_links (G i h0 h1).2.symm ?_⟩
  intro x hx
  obtain ⟨c, hc, rfl, hf, _⟩ := HH.bin_free i x h0 h1 hx
  exact ⟨(hl c hc hf).2.1.symm, (hl c hc hf).1.symm⟩

theorem _root_.Vsa.Sim.DlHeap.HeapAt.drop_inuse {cs₁ cs₂ : List Chunk} {x a : Nat}
    (h : HeapAt m H (fun e => e ∈ H) top brkv (cs₁ ++ ⟨x, a, true⟩ :: cs₂) bins)
    (hno : ∀ e ∈ H, e.1 ≠ x + 16) :
    (∀ i q, 0 < i → i < numBins → q ∈ bins i →
      ∃ c ∈ cs₁ ++ cs₂, c.addr = q ∧ c.inuse = false ∧ (1 < i → binIndex c.size = i)) ∧
    (∀ c ∈ cs₁ ++ cs₂, c.inuse = false → ∃ i, 0 < i ∧ i < numBins ∧ c.addr ∈ bins i ∧
      ∀ j, 0 < j → j < numBins → c.addr ∈ bins j → j = i) ∧
    (∀ e ∈ H, ∃ c ∈ cs₁ ++ cs₂, c.inuse = true ∧
      c.addr + 16 ≤ e.1 ∧ e.1 + e.2 ≤ c.addr + c.size + 8) ∧
    (∀ e ∈ H, e ∈ H → ∃ c ∈ cs₁ ++ cs₂, c.inuse = true ∧ c.addr + 16 = e.1 ∧ e.2 + 8 ≤ c.size) := by
  have hin : ∀ c, c ∈ cs₁ ++ ⟨x, a, true⟩ :: cs₂ ↔ c = ⟨x, a, true⟩ ∨ c ∈ cs₁ ++ cs₂ := by
    intro c; simp only [List.mem_append, List.mem_cons]; exact or_left_comm
  have hE : ∀ e ∈ H, ∃ c ∈ cs₁ ++ cs₂, c.inuse = true ∧ c.addr + 16 = e.1 ∧ e.2 + 8 ≤ c.size := by
    intro e he
    obtain ⟨c, hc, hu, h1, h2⟩ := h.exact e he he
    rcases (hin c).1 hc with rfl | h3
    · exact absurd h1.symm (hno e he)
    · exact ⟨c, h3, hu, h1, h2⟩
  refine ⟨fun i q h0 h1 hq => ?_, fun c hc hf => h.free_binned c ((hin c).2 (.inr hc)) hf,
    fun e he => ?_, fun e he _ => hE e he⟩
  · obtain ⟨c, hc, h1, h2, h3⟩ := h.bin_free i q h0 h1 hq
    rcases (hin c).1 hc with rfl | h4
    · cases h2
    · exact ⟨c, h4, h1, h2, h3⟩
  · obtain ⟨c, hc, hu, h1, h2⟩ := hE e he
    exact ⟨c, hc, hu, by omega, by omega⟩

end Win

end VsaIris.VsaHeap
