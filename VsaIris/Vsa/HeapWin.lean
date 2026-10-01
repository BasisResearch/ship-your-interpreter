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

def volGlobal (w : Nat) : Prop :=
  (topAddr ≤ w ∧ w < topAddr + 8) ∨ (brkAddr ≤ w ∧ w < topPadAddr) ∨
    (mallinfoAddr ≤ w ∧ w < mallinfoAddr + 8) ∨ (0x8001ba08 ≤ w ∧ w < 0x8001ba0c) ∨
    (0x8001b538 ≤ w ∧ w < 0x8001b53c)

theorem win_glob (hag : ∀ w, vsaFoot H w → ¬ U w → m'[w]? = m[w]?)
    (hV : ∀ w, allocGlobal w → U w → volGlobal w) (a : Nat)
    (hg : ∀ k, k < 8 → allocGlobal (a + k)) (ht : ∀ k, k < 8 → ¬ volGlobal (a + k)) :
    read64 m' a = read64 m a :=
  win_read64 hag (fun k hk => .inl (hg k hk)) fun k hk hu => ht k hk (hV _ (hg k hk) hu)

syntax "win_g" : tactic
macro_rules
  | `(tactic| win_g) => `(tactic| (
      intro k hk
      simp only [allocGlobal, volGlobal, InRange, sbrkBaseAddr, brkAddr, topPadAddr, maxSbrkedAddr,
        mallinfoAddr, binblocksAddr, topAddr, avAddr, binAt] at hk ⊢
      omega))

theorem _root_.Vsa.Sim.DlHeap.HeapAt.keep_stable {R : Nat × Nat → Prop}
    (h : HeapAt m H R top brkv chunks bins) (hag : ∀ w, vsaFoot H w → ¬ U w → m'[w]? = m[w]?)
    (hV : ∀ w, allocGlobal w → U w → volGlobal w) :
    read64 m' sbrkBaseAddr = some heapStart ∧ read64 m' topPadAddr = some 0 ∧
    read64 m' binblocksAddr = read64 m binblocksAddr ∧
    ∀ i, 0 < i → i < numBins →
      read64 m' (binAt i + 16) = read64 m (binAt i + 16) ∧
      read64 m' (binAt i + 24) = read64 m (binAt i + 24) := by
  have K := win_glob hag hV
  refine ⟨?_, ?_, K _ (by win_g) (by win_g), fun i h0 h1 => ?_⟩
  · rw [K _ (by win_g) (by win_g)]; exact h.sbrk_base
  · rw [K _ (by win_g) (by win_g)]; exact h.top_pad
  · unfold numBins at h1; exact ⟨K _ (by win_g) (by win_g), K _ (by win_g) (by win_g)⟩

theorem _root_.Vsa.Sim.DlHeap.HeapAt.keep_globals {R : Nat × Nat → Prop} (h : HeapAt m H R top brkv chunks bins)
    (hag : ∀ w, vsaFoot H w → ¬ U w → m'[w]? = m[w]?)
    (hG : ∀ w, allocGlobal w → U w → topAddr ≤ w ∧ w < topAddr + 8) :
    read64 m' sbrkBaseAddr = some heapStart ∧ read64 m' brkAddr = some brkv ∧
    read64 m' topPadAddr = some 0 ∧ (read64 m' maxSbrkedAddr).isSome ∧
    (read64 m' mallinfoAddr).isSome ∧ read64 m' binblocksAddr = read64 m binblocksAddr ∧
    ∀ i, 0 < i → i < numBins →
      read64 m' (binAt i + 16) = read64 m (binAt i + 16) ∧
      read64 m' (binAt i + 24) = read64 m (binAt i + 24) := by
  have hV : ∀ w, allocGlobal w → U w → volGlobal w := fun w g u => .inl (hG w g u)
  have K : ∀ a, (∀ k, k < 8 → allocGlobal (a + k)) → a + 8 ≤ topAddr ∨ topAddr + 8 ≤ a →
      read64 m' a = read64 m a := fun a hg ht =>
    win_read64 hag (fun k hk => .inl (hg k hk)) fun k hk hu => by have := hG _ (hg k hk) hu; omega
  obtain ⟨gS, gP, gB, gL⟩ := h.keep_stable hag hV
  refine ⟨gS, ?_, gP, ?_, ?_, gB, gL⟩
  · rw [K _ (by win_g) (by unfold brkAddr topAddr avAddr; omega)]; exact h.brk
  · rw [K _ (by win_g) (by unfold maxSbrkedAddr topAddr avAddr; omega)]; exact h.max_sbrked
  · rw [K _ (by win_g) (by unfold mallinfoAddr topAddr avAddr; omega)]; exact h.mallinfo

theorem BlockHeapAt.keep_hdr (B : BlockHeapAt m H top brkv chunks bins)
    (hag : ∀ w, vsaFoot H w → ¬ U w → m'[w]? = m[w]?) {q : Nat}
    (hq : q = top ∨ ∃ c ∈ chunks, c.addr = q) (hu : ∀ w, U w → w < q + 8 ∨ q + 16 ≤ w) :
    read64 m' (q + 8) = read64 m (q + 8) :=
  win_read64 hag (foot_header B hq) fun k hk h => by have := hu _ h; omega

theorem BlockHeapAt.keep_freeV (B : BlockHeapAt m H top brkv chunks bins)
    (hag : ∀ w, vsaFoot H w → ¬ U w → m'[w]? = m[w]?)
    (hV : ∀ w, allocGlobal w → U w → volGlobal w)
    (hF : ∀ c ∈ chunks, c.inuse = false → ∀ w, U w →
      (w < c.addr + 16 ∨ c.addr + 32 ≤ w) ∧ (w < c.addr + c.size ∨ c.addr + c.size + 8 ≤ w)) :
    (∀ i, 0 < i → i < numBins → BinList m' i (bins i)) ∧
    ∀ c ∈ chunks, c.inuse = false → read64 m' (c.addr + c.size) = some c.size := by
  have HH := B.heap
  have G := (HH.keep_stable hag hV).2.2.2
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

theorem BlockHeapAt.keep_free (B : BlockHeapAt m H top brkv chunks bins)
    (hag : ∀ w, vsaFoot H w → ¬ U w → m'[w]? = m[w]?)
    (hG : ∀ w, allocGlobal w → U w → topAddr ≤ w ∧ w < topAddr + 8)
    (hF : ∀ c ∈ chunks, c.inuse = false → ∀ w, U w →
      (w < c.addr + 16 ∨ c.addr + 32 ≤ w) ∧ (w < c.addr + c.size ∨ c.addr + c.size + 8 ≤ w)) :
    (∀ i, 0 < i → i < numBins → BinList m' i (bins i)) ∧
    ∀ c ∈ chunks, c.inuse = false → read64 m' (c.addr + c.size) = some c.size :=
  B.keep_freeV hag (fun w g u => .inl (hG w g u)) hF

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

theorem free_mid {cs₁ xs ys cs₂ : List Chunk} {c : Chunk} (hc : c ∈ cs₁ ++ (xs ++ cs₂))
    (hf : c.inuse = false) (hx : ∀ d ∈ xs, d.inuse = true) : c ∈ cs₁ ++ (ys ++ cs₂) := by
  simp only [List.mem_append] at hc ⊢
  rcases hc with h | h | h
  · exact .inl h
  · rw [hx c h] at hf; cases hf
  · exact .inr (.inr h)

theorem _root_.Vsa.Sim.DlHeap.HeapAt.free_to {R : Nat × Nat → Prop} {cs : List Chunk}
    (h : HeapAt m H R top brkv chunks bins) (h1 : ∀ c ∈ chunks, c.inuse = false → c ∈ cs)
    (h2 : ∀ c ∈ cs, c.inuse = false → c ∈ chunks) :
    (∀ i q, 0 < i → i < numBins → q ∈ bins i →
      ∃ c ∈ cs, c.addr = q ∧ c.inuse = false ∧ (1 < i → binIndex c.size = i)) ∧
    (∀ c ∈ cs, c.inuse = false → ∃ i, 0 < i ∧ i < numBins ∧ c.addr ∈ bins i ∧
      ∀ j, 0 < j → j < numBins → c.addr ∈ bins j → j = i) :=
  ⟨fun i q h0 hi hq => let ⟨c, hc, ha, hf, hb⟩ := h.bin_free i q h0 hi hq; ⟨c, h1 c hc hf, ha, hf, hb⟩,
    fun c hc hf => h.free_binned c (h2 c hc hf) hf⟩

end Win

end VsaIris.VsaHeap
