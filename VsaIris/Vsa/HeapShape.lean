import Vsa.Sim.DlHeap
import Vsa.Sim.ReprSurvival
import VsaIris.DlHeap

/-!
# `isHeap`'s heap shape is VSA's `DlHeap.HeapAt`

`VsaIris.DlLayout` leaves the allocator's globals, arena and heap shape
abstract. This module instantiates them for the fixed binary:

* `allocGlobal`: every byte outside the arena that `_malloc_r`, `_free_r`,
  `_realloc_r`, `_sbrk_r` and `_sbrk` read or write (symbol table of
  `c/while-riscv-htif.elf`; the lock hooks are `ret`);
* the arena `[_end, __heap_end)` (`DlHeap.heapStart`/`heapEnd`);
* `Shape`: `DlHeap.HeapAt` read off the owned byte image, with every live
  extent an exact chunk payload (`BlockHeapAt`).

The main result is `BlockHeapAt.transport`: `HeapAt` depends only on the bytes
of `vsaFoot H`, the allocator globals plus the arena bytes outside the live
extents `H`. So `isHeap vsaLayout H`, which owns exactly `vsaFoot H`, owns
everything `HeapAt` constrains, and its frame is relative to the live extents:
the correction `PROOF_CLOSURE_PLAN.md` §2 records for `MallocContract`.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap

/-- `lo ≤ a < hi`. -/
def InRange (lo hi a : Nat) : Prop := lo ≤ a ∧ a < hi

/-- The allocator's globals outside the arena:
`__malloc_av_` (all 258 words, `[0x8001ad10, 0x8001b520)`), the `_errno`
word of `_impure_data` (`_malloc_r`'s ENOMEM store through the reent
pointer), `__malloc_sbrk_base` and `__malloc_trim_threshold`, `brk.0`,
`__malloc_max_total_mem`, `__malloc_max_sbrked_mem`, `__malloc_top_pad`,
`errno` (`_sbrk_r` clears it on every call) and
`__malloc_current_mallinfo`. -/
def allocGlobal (a : Nat) : Prop :=
  InRange 0x8001ad10 0x8001b520 a ∨ InRange 0x8001b538 0x8001b53c a ∨
  InRange 0x8001b960 0x8001b970 a ∨ InRange 0x8001b990 0x8001b9b0 a ∨
  InRange 0x8001ba08 0x8001ba0c a ∨ InRange 0x8001ba18 0x8001ba68 a

theorem allocGlobal_off_arena (a : Nat) (h : allocGlobal a) :
    a < heapStart ∨ heapEnd ≤ a := by
  unfold allocGlobal InRange at h
  unfold heapStart
  omega

/-- The allocator's footprint at live extents `H`: its globals and every arena
byte outside the live extents. This is `VsaIris.heapFoot vsaLayout H`
(`heapFoot_vsaLayout`). -/
def vsaFoot (H : List (Nat × Nat)) (a : Nat) : Prop :=
  allocGlobal a ∨ (heapStart ≤ a ∧ a < heapEnd ∧ ∀ e ∈ H, ¬ InExt e a)

/-- The heap shape with live blocks `H`: `HeapAt` where every live extent is
an exact in-use chunk payload (dlmalloc's `free`/`realloc` need exactly this
of their argument, so every block the Iris specs hand out is one), plus room
for the top chunk's header below the break (dlmalloc keeps `top` at least
`MINSIZE`). -/
structure BlockHeapAt (m : Mem) (H : List (Nat × Nat)) (top brkv : Nat)
    (chunks : List Chunk) (bins : Nat → List Nat) : Prop where
  heap : HeapAt m H (fun e => e ∈ H) top brkv chunks bins
  top_room : top + 16 ≤ brkv

def BlockHeap (m : Mem) (H : List (Nat × Nat)) : Prop :=
  ∃ top brkv chunks bins, BlockHeapAt m H top brkv chunks bins

/-! ## Chunk-walk geometry -/

/-- The walk starts at a chunk or is empty at the top. -/
theorem _root_.Vsa.Sim.DlHeap.ChunkWalk.head_or_top {m : Mem} {p top : Nat} {cs : List Chunk}
    (h : ChunkWalk m p top cs) : p = top ∨ ∃ c ∈ cs, c.addr = p := by
  cases h with
  | top => exact .inl rfl
  | chunk => exact .inr ⟨_, List.mem_cons_self, rfl⟩

/-- Every chunk lies in `[p, top)` and has at least the minimum size. -/
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

/-- Two chunks of one walk are the same chunk or do not overlap. -/
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

/-- Transport of the walk: it reads only the chunk headers and the top header. -/
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

/-- Transport of a bin list: it reads the head's `bk` word and each member's
`fd`/`bk` words. -/
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

/-! ## Every byte `HeapAt` reads is in `vsaFoot` -/

section Reads

variable {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat} {chunks : List Chunk}
  {bins : Nat → List Nat}

/-- An arena byte outside every in-use chunk's usable payload is in the
footprint, because every live extent lies in such a payload. -/
theorem foot_of_arena (h : HeapAt m H (fun e => e ∈ H) top brkv chunks bins) {a : Nat}
    (hlo : heapStart ≤ a) (hhi : a < heapEnd)
    (hout : ∀ c ∈ chunks, c.inuse = true → ¬ (c.addr + 16 ≤ a ∧ a < c.addr + c.size + 8)) :
    vsaFoot H a := by
  refine .inr ⟨hlo, hhi, fun e he hin => ?_⟩
  obtain ⟨c, hc, hu, h1, h2⟩ := h.live e he
  unfold InExt at hin
  exact hout c hc hu ⟨by omega, by omega⟩

/-- The header word of any chunk, or of the top chunk, is in the footprint. -/
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

/-- The `fd`/`bk` words and the footer of a free chunk are in the footprint. -/
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

/-! ## Locality -/

private theorem read64_of_foot {H : List (Nat × Nat)} {m m' : Mem}
    (hag : AgreeP (vsaFoot H) m m') {a : Nat} (hf : ∀ k, k < 8 → vsaFoot H (a + k)) :
    read64 m a = read64 m' a :=
  read64_agreeP hag hf

private theorem global_read {H : List (Nat × Nat)} {a : Nat}
    (hg : ∀ k, k < 8 → allocGlobal (a + k)) : ∀ k, k < 8 → vsaFoot H (a + k) :=
  fun k hk => .inl (hg k hk)

/-- **`HeapAt` reads only the allocator's footprint.** Two memories that agree
on `vsaFoot H` satisfy the same block-heap shape. Every other byte, in
particular every byte of a live extent, is unconstrained by the allocator. -/
theorem BlockHeapAt.transport {m m' : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat}
    (h : BlockHeapAt m H top brkv chunks bins) (hag : AgreeP (vsaFoot H) m m') :
    BlockHeapAt m' H top brkv chunks bins := by
  have hH := h.heap
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
      G _ _ _ ⟨by omega, by omega⟩ (.inl ⟨rfl, rfl⟩))
  have gSbrk : read64 m sbrkBaseAddr = read64 m' sbrkBaseAddr :=
    read64_of_foot hag (global_read fun k hk =>
      G _ _ _ ⟨by unfold sbrkBaseAddr; omega, by unfold sbrkBaseAddr; omega⟩
        (.inr (.inl ⟨rfl, rfl⟩)))
  have gBrk : ∀ a, 0x8001b990 ≤ a → a + 8 ≤ 0x8001b9b0 → read64 m a = read64 m' a :=
    fun a h1 h2 => read64_of_foot hag (global_read fun k hk =>
      G _ _ _ ⟨by omega, by omega⟩ (.inr (.inr (.inl ⟨rfl, rfl⟩))))
  have gMi : read64 m mallinfoAddr = read64 m' mallinfoAddr :=
    read64_of_foot hag (global_read fun k hk =>
      G _ _ _ ⟨by unfold mallinfoAddr; omega, by unfold mallinfoAddr; omega⟩
        (.inr (.inr (.inr ⟨rfl, rfl⟩))))
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
    fun q hq => read64_of_foot hag (foot_header h hq)
  have hfreeRd : ∀ c ∈ chunks, c.inuse = false →
      read64 m (c.addr + 16) = read64 m' (c.addr + 16) ∧
      read64 m (c.addr + 24) = read64 m' (c.addr + 24) ∧
      read64 m (c.addr + c.size) = read64 m' (c.addr + c.size) := by
    intro c hc hf
    obtain ⟨hl, hft⟩ := foot_free h hc hf
    refine ⟨read64_of_foot hag (fun k hk => hl k (by omega)),
      read64_of_foot hag (fun k hk => ?_), read64_of_foot hag hft⟩
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
      footer := fun c hc hf => (hfreeRd c hc hf).2.2 ▸ hH.footer c hc hf
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

theorem BlockHeap.transport {m m' : Mem} {H : List (Nat × Nat)} (h : BlockHeap m H)
    (hag : AgreeP (vsaFoot H) m m') : BlockHeap m' H := by
  obtain ⟨top, brkv, chunks, bins, h⟩ := h
  exact ⟨top, brkv, chunks, bins, h.transport hag⟩

/-- Every byte of a live block is an arena byte: the arena is partitioned into
the live blocks and the allocator's arena bytes. -/
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

/-- The footprint and the live blocks split the allocator's region exactly. -/
theorem vsaFoot_iff {H : List (Nat × Nat)} {a : Nat} (harena : heapStart ≤ a ∧ a < heapEnd) :
    vsaFoot H a ↔ ∀ e ∈ H, ¬ InExt e a := by
  constructor
  · rintro (hg | ⟨_, _, h⟩)
    · rcases allocGlobal_off_arena a hg with h | h <;> omega
    · exact h
  · intro h; exact .inr ⟨harena.1, harena.2, h⟩

/-! ## The layout -/

/-- Memory `m` holds the image `img` on `S`. -/
def ImgOn (S : Nat → Prop) (img : Nat → BitVec 8) (m : Mem) : Prop :=
  ∀ a, S a → m[a]? = some (img a)

/-- The heap shape of the owned image: some memory holding `img` on the
footprint has the block-heap shape. By `BlockHeapAt.transport`, that is the
same as EVERY such memory having it (`imgShape_iff`). -/
def imgShape (img : Nat → BitVec 8) (H : List (Nat × Nat)) : Prop :=
  ∃ m, ImgOn (vsaFoot H) img m ∧ BlockHeap m H

/-- **The fixed binary's dlmalloc layout.** -/
def vsaLayout : DlLayout where
  global := allocGlobal
  lo := heapStart
  hi := heapEnd
  global_off_arena := allocGlobal_off_arena
  Shape := imgShape

theorem heapFoot_vsaLayout (H : List (Nat × Nat)) : heapFoot vsaLayout H = vsaFoot H := rfl

/-- The owned image has the heap shape exactly when the actual memory does. -/
theorem imgShape_iff {img : Nat → BitVec 8} {H : List (Nat × Nat)} {m : Mem}
    (hm : ImgOn (vsaFoot H) img m) : vsaLayout.Shape img H ↔ BlockHeap m H := by
  constructor
  · rintro ⟨m0, hm0, hs⟩
    exact hs.transport fun a ha => (hm0 a ha).trans (hm a ha).symm
  · exact fun hs => ⟨m, hm, hs⟩

/-- `MemAgree` against a total byte read (`readByte = getD 0`) gives `ImgOn`
where the bytes are present. -/
theorem imgOn_of_getD {S : Nat → Prop} {img : Nat → BitVec 8} {m : Mem}
    (hpres : ∀ a, S a → (m[a]?).isSome) (hval : ∀ a, S a → (m[a]?).getD 0 = img a) :
    ImgOn S img m := by
  intro a ha
  have hp := hpres a ha
  have hv := hval a ha
  cases hma : m[a]? with
  | none => rw [hma] at hp; cases hp
  | some b => rw [hma] at hv; simp at hv; rw [hv]

end VsaIris.VsaHeap
