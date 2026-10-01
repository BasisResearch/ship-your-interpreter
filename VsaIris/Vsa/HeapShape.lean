import Vsa.Sim.DlHeap
import Vsa.Sim.ReprSurvival
import VsaIris.DlHeap

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap

def InRange (lo hi a : Nat) : Prop := lo ≤ a ∧ a < hi

def allocGlobal (a : Nat) : Prop :=
  InRange 0x8001ad10 0x8001b520 a ∨ InRange 0x8001b538 0x8001b53c a ∨
  InRange 0x8001b960 0x8001b970 a ∨ InRange 0x8001b990 0x8001b9b0 a ∨
  InRange 0x8001ba08 0x8001ba0c a ∨ InRange 0x8001ba18 0x8001ba68 a

theorem allocGlobal_off_arena (a : Nat) (h : allocGlobal a) :
    a < heapStart ∨ heapEnd ≤ a := by
  unfold allocGlobal InRange at h
  unfold heapStart
  omega

def vsaFoot (H : List (Nat × Nat)) (a : Nat) : Prop :=
  allocGlobal a ∨ (heapStart ≤ a ∧ a < heapEnd ∧ ∀ e ∈ H, ¬ InExt e a)

structure BlockHeapAt (m : Mem) (H : List (Nat × Nat)) (top brkv : Nat)
    (chunks : List Chunk) (bins : Nat → List Nat) : Prop where
  heap : HeapAt m H (fun e => e ∈ H) top brkv chunks bins
  top_room : top + 16 ≤ brkv


theorem _root_.Vsa.Sim.DlHeap.ChunkWalk.head_or_top {m : Mem} {p top : Nat} {cs : List Chunk}
    (h : ChunkWalk m p top cs) : p = top ∨ ∃ c ∈ cs, c.addr = p := by
  cases h with
  | top => exact .inl rfl
  | chunk => exact .inr ⟨_, List.mem_cons_self, rfl⟩

theorem _root_.Vsa.Sim.DlHeap.ChunkWalk.chunk_bounds {m : Mem} {p top : Nat} {cs : List Chunk}
    (h : ChunkWalk m p top cs) : ∀ c ∈ cs, p ≤ c.addr ∧ c.addr + c.size ≤ top ∧ 32 ≤ c.size := by
  induction h with
  | top => intro c hc; cases hc
  | chunk _ _ hmin _ _ rest ih =>
    intro c hc
    have hle := rest.le
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨Nat.le_refl _, hle, hmin⟩
    · have := ih c hc
      omega

theorem _root_.Vsa.Sim.DlHeap.ChunkWalk.chunk_sep {m : Mem} {p top : Nat} {cs : List Chunk}
    (h : ChunkWalk m p top cs) : ∀ c ∈ cs, ∀ c' ∈ cs,
      c = c' ∨ c.addr + c.size ≤ c'.addr ∨ c'.addr + c'.size ≤ c.addr := by
  induction h with
  | top => intro c hc; cases hc
  | chunk _ _ _ _ _ rest ih =>
    have hb := rest.chunk_bounds
    intro c hc c' hc'
    rcases List.mem_cons.mp hc with rfl | hc <;> rcases List.mem_cons.mp hc' with rfl | hc'
    · exact .inl rfl
    · exact .inr (.inl (hb c' hc').1)
    · exact .inr (.inr (hb c hc).1)
    · exact ih c hc c' hc'

theorem _root_.Vsa.Sim.DlHeap.ChunkWalk.transport_headers {m m' : Mem} {p top : Nat} {cs : List Chunk}
    (h : ChunkWalk m p top cs)
    (hd : ∀ q, (q = top ∨ ∃ c ∈ cs, c.addr = q) → read64 m (q + 8) = read64 m' (q + 8)) :
    ChunkWalk m' p top cs := by
  induction h with
  | top => exact .top
  | @chunk p top h h' cs hh hlow hmin hal hn rest ih =>
    have hp := hd p (.inr ⟨_, List.mem_cons_self, rfl⟩)
    have hnext := hd (p + chunkSize h) (by
      rcases rest.head_or_top with he | ⟨c, hc, hca⟩
      · exact .inl he
      · exact .inr ⟨c, List.mem_cons_of_mem _ hc, hca⟩)
    refine .chunk (hp ▸ hh) hlow hmin hal (hnext ▸ hn) (ih fun q hq => hd q ?_)
    rcases hq with hq | ⟨c, hc, hca⟩
    · exact .inl hq
    · exact .inr ⟨c, List.mem_cons_of_mem _ hc, hca⟩

theorem _root_.Vsa.Sim.DlHeap.BinChain.transport_links {m m' : Mem} {b q prev : Nat} {qs : List Nat}
    (h : BinChain m b q prev qs)
    (hb : read64 m (b + 24) = read64 m' (b + 24))
    (hq : ∀ x ∈ qs, read64 m (x + 24) = read64 m' (x + 24) ∧
      read64 m (x + 16) = read64 m' (x + 16)) :
    BinChain m' b q prev qs := by
  induction h with
  | close hc => exact .close (hb ▸ hc)
  | link hne hp hn rest ih =>
    have hx := hq _ List.mem_cons_self
    exact .link hne (hx.1 ▸ hp) (hx.2 ▸ hn)
      (ih fun x hx' => hq x (List.mem_cons_of_mem _ hx'))

section Reads

variable {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat} {chunks : List Chunk}
  {bins : Nat → List Nat}

theorem foot_of_arena (h : HeapAt m H (fun e => e ∈ H) top brkv chunks bins) {a : Nat}
    (hlo : heapStart ≤ a) (hhi : a < heapEnd)
    (hout : ∀ c ∈ chunks, c.inuse = true → ¬ (c.addr + 16 ≤ a ∧ a < c.addr + c.size + 8)) :
    vsaFoot H a := by
  refine .inr ⟨hlo, hhi, fun e he hin => ?_⟩
  obtain ⟨c, hc, hu, h1, h2⟩ := h.live e he
  unfold InExt at hin
  exact hout c hc hu ⟨by omega, by omega⟩

theorem foot_header (h : BlockHeapAt m H top brkv chunks bins) {q : Nat}
    (hq : q = top ∨ ∃ c ∈ chunks, c.addr = q) : ∀ k, k < 8 → vsaFoot H (q + 8 + k) := by
  intro k hk
  have hb := h.heap.walk.chunk_bounds
  have hs := h.heap.walk.chunk_sep
  have hroom := h.top_room
  have hbrk := h.heap.brk_le
  have hle := h.heap.walk.le
  refine foot_of_arena h.heap ?_ ?_ ?_
  · rcases hq with rfl | ⟨c, hc, rfl⟩
    · omega
    · have := hb c hc; omega
  · rcases hq with rfl | ⟨c, hc, rfl⟩
    · omega
    · have := hb c hc; omega
  · intro c hc _ hin
    rcases hq with rfl | ⟨c', hc', rfl⟩
    · have := hb c hc; omega
    · have := hb c hc
      have := hb c' hc'
      rcases hs c hc c' hc' with rfl | hsep | hsep <;> omega

theorem foot_free (h : BlockHeapAt m H top brkv chunks bins) {c' : Chunk}
    (hc' : c' ∈ chunks) (hfree : c'.inuse = false) :
    (∀ k, k < 16 → vsaFoot H (c'.addr + 16 + k)) ∧
    (∀ k, k < 8 → vsaFoot H (c'.addr + c'.size + k)) := by
  have hb := h.heap.walk.chunk_bounds
  have hs := h.heap.walk.chunk_sep
  have hroom := h.top_room
  have hbrk := h.heap.brk_le
  have hle := h.heap.walk.le
  have hb' := hb c' hc'
  have key : ∀ a, c'.addr + 16 ≤ a → a < c'.addr + c'.size + 8 → vsaFoot H a := by
    intro a h1 h2
    refine foot_of_arena h.heap (by omega) (by omega) ?_
    intro c hc hu hin
    have := hb c hc
    rcases hs c hc c' hc' with rfl | hsep | hsep
    · rw [hu] at hfree; cases hfree
    · omega
    · omega
  exact ⟨fun k hk => key _ (by omega) (by omega), fun k hk => key _ (by omega) (by omega)⟩

end Reads

def vsaRead (H : List (Nat × Nat)) (a : Nat) : Prop :=
  vsaFoot H a ∧ ¬ InRange 0x8001b538 0x8001b53c a ∧ ¬ InRange 0x8001ba08 0x8001ba0c a

def NotErr (a : Nat) : Prop :=
  a + 8 ≤ 0x8001b538 ∨ (0x8001b53c ≤ a ∧ a + 8 ≤ 0x8001ba08) ∨ 0x8001ba0c ≤ a

private theorem read64_of_foot {H : List (Nat × Nat)} {m m' : Mem}
    (hag : AgreeP (vsaRead H) m m') {a : Nat} (hf : ∀ k, k < 8 → vsaFoot H (a + k))
    (hn : NotErr a) : read64 m a = read64 m' a :=
  read64_agreeP hag fun k hk => ⟨hf k hk, by unfold InRange NotErr at *; omega,
    by unfold InRange NotErr at *; omega⟩

private theorem global_read {H : List (Nat × Nat)} {a : Nat}
    (hg : ∀ k, k < 8 → allocGlobal (a + k)) : ∀ k, k < 8 → vsaFoot H (a + k) :=
  fun k hk => .inl (hg k hk)

theorem BlockHeapAt.transport_read {m m' : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat}
    (h : BlockHeapAt m H top brkv chunks bins) (hag : AgreeP (vsaRead H) m m') :
    BlockHeapAt m' H top brkv chunks bins := by
  have hH := h.heap
  have hlo : heapStart ≤ top := hH.walk.le
  have hcb := hH.walk.chunk_bounds
  have G : ∀ a lo hi, InRange lo hi a → (lo = 0x8001ad10 ∧ hi = 0x8001b520 ∨
      lo = 0x8001b960 ∧ hi = 0x8001b970 ∨ lo = 0x8001b990 ∧ hi = 0x8001b9b0 ∨
      lo = 0x8001ba18 ∧ hi = 0x8001ba68) → allocGlobal a := by
    intro a lo hi hr hlh
    unfold allocGlobal
    rcases hlh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .inl hr
    · exact .inr (.inr (.inl hr))
    · exact .inr (.inr (.inr (.inl hr)))
    · exact .inr (.inr (.inr (.inr (.inr hr))))
  have gAv : ∀ a, 0x8001ad10 ≤ a → a + 8 ≤ 0x8001b520 → read64 m a = read64 m' a :=
    fun a h1 h2 => read64_of_foot hag (global_read fun k hk =>
      G _ _ _ ⟨by omega, by omega⟩ (.inl ⟨rfl, rfl⟩)) (.inl (by omega))
  have gSbrk : read64 m sbrkBaseAddr = read64 m' sbrkBaseAddr :=
    read64_of_foot hag (global_read fun k hk =>
      G _ _ _ ⟨by unfold sbrkBaseAddr; omega, by unfold sbrkBaseAddr; omega⟩
        (.inr (.inl ⟨rfl, rfl⟩))) (.inr (.inl (by unfold sbrkBaseAddr; omega)))
  have gBrk : ∀ a, 0x8001b990 ≤ a → a + 8 ≤ 0x8001b9b0 → read64 m a = read64 m' a :=
    fun a h1 h2 => read64_of_foot hag (global_read fun k hk =>
      G _ _ _ ⟨by omega, by omega⟩ (.inr (.inr (.inl ⟨rfl, rfl⟩)))) (.inr (.inl (by omega)))
  have gMi : read64 m mallinfoAddr = read64 m' mallinfoAddr :=
    read64_of_foot hag (global_read fun k hk =>
      G _ _ _ ⟨by unfold mallinfoAddr; omega, by unfold mallinfoAddr; omega⟩
        (.inr (.inr (.inr ⟨rfl, rfl⟩)))) (.inr (.inr (by unfold mallinfoAddr; omega)))
  have gTop : read64 m topAddr = read64 m' topAddr :=
    gAv _ (by unfold topAddr avAddr; omega) (by unfold topAddr avAddr; omega)
  have gBb : read64 m binblocksAddr = read64 m' binblocksAddr :=
    gAv _ (by unfold binblocksAddr avAddr; omega) (by unfold binblocksAddr avAddr; omega)
  have gBrk0 : read64 m brkAddr = read64 m' brkAddr :=
    gBrk _ (by unfold brkAddr; omega) (by unfold brkAddr; omega)
  have gPad : read64 m topPadAddr = read64 m' topPadAddr :=
    gBrk _ (by unfold topPadAddr; omega) (by unfold topPadAddr; omega)
  have gMax : read64 m maxSbrkedAddr = read64 m' maxSbrkedAddr :=
    gBrk _ (by unfold maxSbrkedAddr; omega) (by unfold maxSbrkedAddr; omega)
  have gBin16 : ∀ i, i < numBins → read64 m (binAt i + 16) = read64 m' (binAt i + 16) :=
    fun i hi => gAv _ (by unfold binAt avAddr; omega)
      (by unfold binAt avAddr; unfold numBins at hi; omega)
  have gBin24 : ∀ i, i < numBins → read64 m (binAt i + 24) = read64 m' (binAt i + 24) :=
    fun i hi => gAv _ (by unfold binAt avAddr; omega)
      (by unfold binAt avAddr; unfold numBins at hi; omega)
  have hdr : ∀ q, (q = top ∨ ∃ c ∈ chunks, c.addr = q) →
      read64 m (q + 8) = read64 m' (q + 8) :=
    fun q hq => read64_of_foot hag (foot_header h hq) (.inr (.inr (by
      unfold heapStart at hlo
      rcases hq with rfl | ⟨c, hc, rfl⟩
      · omega
      · have := (hcb c hc).1; unfold heapStart at this; omega)))
  have hfreeRd : ∀ c ∈ chunks, c.inuse = false →
      read64 m (c.addr + 16) = read64 m' (c.addr + 16) ∧
      read64 m (c.addr + 24) = read64 m' (c.addr + 24) ∧
      read64 m (c.addr + c.size) = read64 m' (c.addr + c.size) := by
    intro c hc hf
    obtain ⟨hl, hft⟩ := foot_free h hc hf
    have hca := (hcb c hc).1
    unfold heapStart at hca
    refine ⟨read64_of_foot hag (fun k hk => hl k (by omega)) (.inr (.inr (by omega))),
      read64_of_foot hag (fun k hk => ?_) (.inr (.inr (by omega))),
      read64_of_foot hag hft (.inr (.inr (by omega)))⟩
    have := hl (k + 8) (by omega)
    rwa [show c.addr + 16 + (k + 8) = c.addr + 24 + k by omega] at this
  have hstart : read64 m (heapStart + 8) = read64 m' (heapStart + 8) :=
    hdr _ (by
      rcases hH.walk.head_or_top with he | he
      · exact .inl he
      · exact .inr he)
  refine ⟨?_, h.top_room⟩
  exact
    { sbrk_base := gSbrk ▸ hH.sbrk_base
      brk := gBrk0 ▸ hH.brk
      brk_le := hH.brk_le
      top_ptr := gTop ▸ hH.top_ptr
      top_le := hH.top_le
      top_size := hH.top_size
      top_header := hdr top (.inl rfl) ▸ hH.top_header
      top_pad := gPad ▸ hH.top_pad
      max_sbrked := gMax ▸ hH.max_sbrked
      mallinfo := gMi ▸ hH.mallinfo
      first_prev := hstart ▸ hH.first_prev
      walk := hH.walk.transport_headers hdr
      coalesced := hH.coalesced
      footer := fun c hc hf => by
        obtain ⟨_, _, hft⟩ := hfreeRd c hc hf
        exact hft ▸ hH.footer c hc hf
      bins_list := by
        intro i h0 h1
        obtain ⟨first, hfirst, hchain⟩ := hH.bins_list i h0 h1
        refine ⟨first, gBin16 i h1 ▸ hfirst, hchain.transport_links (gBin24 i h1) ?_⟩
        intro x hx
        obtain ⟨c, hc, rfl, hf, _⟩ := hH.bin_free i x h0 h1 hx
        exact ⟨(hfreeRd c hc hf).2.1, (hfreeRd c hc hf).1⟩
      bins_nodup := hH.bins_nodup
      bin_free := hH.bin_free
      free_binned := hH.free_binned
      remainder := hH.remainder
      binblocks_present := gBb ▸ hH.binblocks_present
      binblocks := fun bb hbb => hH.binblocks bb (gBb ▸ hbb)
      live := hH.live
      exact := hH.exact }

theorem BlockHeapAt.block_arena {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} (h : BlockHeapAt m H top brkv chunks bins)
    {e : Nat × Nat} (he : e ∈ H) {a : Nat} (ha : InExt e a) :
    heapStart ≤ a ∧ a < heapEnd := by
  obtain ⟨c, hc, _, h1, h2⟩ := h.heap.live e he
  have := h.heap.walk.chunk_bounds c hc
  have := h.top_room
  have := h.heap.brk_le
  unfold InExt at ha
  omega

def ImgOn (S : Nat → Prop) (img : Nat → BitVec 8) (m : Mem) : Prop :=
  ∀ a, S a → m[a]? = some (img a)


def inuseBlocks (chunks : List Chunk) : List (Nat × Nat) :=
  chunks.filterMap fun c => if c.inuse then some (c.addr + 16, c.size - 8) else none

theorem mem_inuseBlocks {chunks : List Chunk} {e : Nat × Nat} :
    e ∈ inuseBlocks chunks ↔ ∃ c ∈ chunks, c.inuse = true ∧ e = (c.addr + 16, c.size - 8) := by
  unfold inuseBlocks
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨c, hc, h⟩
    by_cases hu : c.inuse = true
    · simp only [hu, ite_true, Option.some.injEq] at h
      exact ⟨c, hc, hu, h.symm⟩
    · simp [hu] at h
  · rintro ⟨c, hc, hu, rfl⟩
    exact ⟨c, hc, by simp [hu]⟩

theorem blockHeapAt_of_heapAt {m : Mem} {exts : List (Nat × Nat)}
    {reallocs : Nat × Nat → Prop} {top brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} (h : HeapAt m exts reallocs top brkv chunks bins)
    (hroom : top + 16 ≤ brkv) :
    BlockHeapAt m (inuseBlocks chunks) top brkv chunks bins ∧
      ∀ e ∈ exts, ∃ b ∈ inuseBlocks chunks, ∀ a, InExt e a → InExt b a := by
  have hb := h.walk.chunk_bounds
  refine ⟨⟨{ h with
      live := ?_
      exact := ?_ }, hroom⟩, ?_⟩
  · intro e he
    obtain ⟨c, hc, hu, rfl⟩ := mem_inuseBlocks.1 he
    have := hb c hc
    exact ⟨c, hc, hu, by simp, by simp; omega⟩
  · intro e he _
    obtain ⟨c, hc, hu, rfl⟩ := mem_inuseBlocks.1 he
    have := hb c hc
    exact ⟨c, hc, hu, rfl, by simp; omega⟩
  · intro e he
    obtain ⟨c, hc, hu, h1, h2⟩ := h.live e he
    have := hb c hc
    refine ⟨(c.addr + 16, c.size - 8), mem_inuseBlocks.2 ⟨c, hc, hu, rfl⟩, fun a ha => ?_⟩
    unfold InExt at ha ⊢
    simp only at ha ⊢
    omega

end VsaIris.VsaHeap
