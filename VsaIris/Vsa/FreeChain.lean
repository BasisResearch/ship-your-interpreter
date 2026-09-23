import VsaIris.Vsa.FreeFastSegs
import VsaIris.Vsa.FreeFastHeap
import VsaIris.Vsa.MallocSmallChain

/-!
# `free` on the fast heap: freeing the chunk below the top

`vsaFreeTop` is the heap shape `free`'s top-merge path accepts. It is the fast
heap, as for `malloc`, where the freed block is the payload of the last chunk,
no other live block starts there, and the merged top stays below
`__malloc_trim_threshold`. The run chains `segFWrap`, `segFPro`, the lock call
at `0x80007368`, `segFBody` (the merge stores), `segFEpi`, and the unlock
hook's tail call back to the caller. `FastAt.merge` gives the heap after.
`freeRoomRun_fast` is the resulting `FreeRoomRun`.
-/

namespace VsaIris.MallocFast

open Vsa.Sim Vsa.MemRepr Vsa.Sim.DlHeap VsaIris.Inst VsaIris.VsaHeap
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Iris

/-- The witness data of the freeing shape. -/
structure FreeWit where
  m : Mem
  top : Nat
  brkv : Nat
  cs : List Chunk
  c : Chunk
  bins : Nat → List Nat
  thr : Nat

/-- The fast heap with the block `(q, n)` the payload of its last chunk `W.c`,
below the top, with the merged top below the trim threshold. -/
structure FreeTopAt (W : FreeWit) (q n : Nat) (H : List (Nat × Nat)) (maxReq k : Nat) : Prop where
  fast : FastAt W.m ((q, n) :: H) maxReq k W.top W.brkv (W.cs ++ [W.c]) W.bins
  payload : W.c.addr + 16 = q
  distinct : ∀ e ∈ H, e.1 ≠ q
  thr_read : read64 W.m trimAddr = some W.thr
  below : W.brkv - W.c.addr < W.thr

/-- `free`'s top-merge precondition on the owned image, with `k` credits. -/
def vsaFreeTop (maxReq : Nat) : RoomPred := fun img Hq k =>
  match Hq with
  | [] => False
  | (q, n) :: H => ∃ W : FreeWit, ImgOn (vsaFoot ((q, n) :: H)) img W.m ∧ FreeTopAt W q n H maxReq k

theorem roomLocal_freeTop (maxReq : Nat) : RoomLocal vsaLayout (vsaFreeTop maxReq) := by
  rintro (_ | ⟨⟨q, n⟩, H⟩) img img' k h hp
  · exact hp
  · obtain ⟨W, hm, hf⟩ := hp
    exact ⟨W, fun a ha => (hm a ha).trans (by rw [h a ha]), hf⟩

/-- An empty walk starts at the top. -/
theorem _root_.Vsa.Sim.DlHeap.ChunkWalk.nil_eq {m : Mem} {p t : Nat} (h : ChunkWalk m p t []) :
    p = t := by
  cases h; rfl

/-- In a walk of in-use chunks ending at `top`, the top's header has
`PREV_INUSE`. -/
theorem _root_.Vsa.Sim.DlHeap.ChunkWalk.top_prev {m : Mem} {p top : Nat} {cs : List Chunk}
    (h : ChunkWalk m p top cs) (hin : ∀ c ∈ cs, c.inuse = true) (hne : cs ≠ [])
    {v : Nat} (hv : read64 m (top + 8) = some v) : prevInuse v = true := by
  induction h with
  | top => exact absurd rfl hne
  | @chunk p top hh h' cs hh0 hlow hmin hal hn rest ih =>
    rcases rest.head_or_top with he | ⟨c, hc, _⟩
    · rw [← he] at hv
      rw [hn] at hv
      cases hv
      exact hin _ List.mem_cons_self
    · exact ih (fun c hc => hin c (List.mem_cons_of_mem _ hc)) (List.ne_nil_of_mem hc) hv

/-- The heap reads of the top merge, named. -/
structure FreeReads (W : FreeWit) : Prop where
  top_ptr : read64 W.m topAddr = some W.top
  hdr : read64 W.m (W.c.addr + 8) = some (W.c.size + 1)
  thdr : read64 W.m (W.top + 8) = some (W.brkv - W.top + 1)
  thr : read64 W.m trimAddr = some W.thr

/-- The merge's geometry and the reads of the top merge. -/
theorem FreeTopAt.facts {W : FreeWit} {q n : Nat} {H : List (Nat × Nat)} {maxReq k : Nat}
    (h : FreeTopAt W q n H maxReq k) :
    FreeGeo W.c.addr W.top W.c.size (W.brkv - W.top) W.thr ∧ FreeReads W := by
  have hH := h.fast.heap.heap
  obtain ⟨mid, wcs, wc⟩ := hH.walk.append_inv
  obtain ⟨hca, hctop, hh, Rh, hsz, hlow, hmin, hal⟩ := wc.single
  subst hca
  have hwl := wcs.le
  have hbrk := hH.brk_le
  have htsz := hH.top_size
  have htle := hH.top_le
  have hroom := h.fast.heap.top_room
  have hthr := read64_lt _ _ _ h.thr_read
  have hbel := h.below
  -- the chunk's header has `PREV_INUSE`
  have hpi : prevInuse hh = true := by
    rcases List.eq_nil_or_concat W.cs with he | ⟨L, b, hL⟩
    · have hfp := hH.first_prev
      rw [he] at wcs
      have he' : heapStart = W.c.addr := wcs.nil_eq
      rw [he', Rh] at hfp
      simpa [Option.any, prevInuse] using hfp
    · exact wcs.top_prev (fun c hc => h.fast.fast.inuse c (List.mem_append_left _ hc))
        (by rw [hL]; simp) Rh
  have hhv : hh = W.c.size + 1 := by
    unfold prevInuse at hpi; unfold chunkSize at hsz
    rw [beq_iff_eq] at hpi
    omega
  -- the chunk's address is aligned: the walk starts at an aligned `heapStart`
  have hal16 : W.c.addr % 16 = 0 := by
    have key : ∀ {p t : Nat} {cs : List Chunk}, ChunkWalk W.m p t cs → p % 16 = 0 → t % 16 = 0 := by
      intro p t cs w hp
      induction w with
      | top => exact hp
      | chunk _ _ _ hal' _ _ ih => exact ih (by omega)
    exact key wcs (by unfold heapStart; decide)
  refine ⟨{ c_lo := wcs.le, c16 := hal16, c_top := hctop, csz16 := hal, tsz16 := htsz,
             top_hi := by omega, top_room := by omega, below := by omega, thr_lt := hthr },
    { top_ptr := hH.top_ptr, hdr := by rw [← hhv]; exact Rh, thdr := hH.top_header,
      thr := h.thr_read }⟩

/-- The body's reflected write log is the merge's two stores. -/
theorem fbody_log {sp a0 a1 a2 a3 a4 a5 a6 a7 t1 s0 r : BitVec 64} {f : Nat → BitVec 8}
    {c top csz tsz thr brkv : Nat} (G : FreeGeo c top csz tsz thr) (V : FBodyVals f sp c top csz tsz thr)
    (hb : top + tsz = brkv) :
    (segOut segFBody (fbodyL sp a0 a1 a2 a3 a4 a5 a6 a7 t1 s0 r) (fbodyLds f sp c top)).log =
      mergeLog c brkv := by
  have E := V.eqs G
  have hclo := G.c_lo; have hct := G.c_top; have hcs := G.csz16
  have hts := G.tsz16; have hthi := G.top_hi
  unfold heapStart at hclo; unfold heapEnd at hthi
  simp only [segOut, segFBody, evalBlocks, evalBlock, SegEvalState.init, wlogM, wentryM, widthOfM,
    eaddrM]
  seg_norm
  simp only [fbodyLds, List.tail_cons, List.nil_append, List.append_nil]
  have hsum : ((bytesVal .ld (wordOf f (c + 8)) &&& sign_extend (m := 64) (0xffe#12)) +
      (bytesVal .ld (wordOf f (top + 8)) &&& sign_extend (m := 64) (0xffc#12))).toNat = csz + tsz := by
    rw [BitVec.toNat_add, E.a5, E.t, Nat.mod_eq_of_lt (by omega)]
  have e1 : (bytesVal .ld (wordOf f (sp.toNat + 8)) + sign_extend (m := 64) (0xff0#12) +
      sign_extend (m := 64) (0x008#12)).toNat = c + 8 := by
    rw [add_imm _ _ 8 (by decide) (by rw [E.a4]; omega), E.a4]
  have v1 : (bytesVal .ld (wordOf f (c + 8)) &&& sign_extend (m := 64) (0xffe#12)) +
      (bytesVal .ld (wordOf f (top + 8)) &&& sign_extend (m := 64) (0xffc#12)) |||
      sign_extend (m := 64) (0x001#12) = BitVec.ofNat 64 (brkv - c + 1) := by
    rw [or_one_even _ (by rw [hsum]; omega)]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hsum, ofNat_toNat_lt (by omega)]
    simp only [BitVec.toNat_ofNat]
    omega
  have v2 : bytesVal .ld (wordOf f (sp.toNat + 8)) + sign_extend (m := 64) (0xff0#12) =
      BitVec.ofNat 64 c := by
    apply BitVec.eq_of_toNat_eq; rw [E.a4, ofNat_toNat_lt (by omega)]
  rw [e1, v1, v2]
  simp only [mergeLog, List.cons.injEq, and_true, true_and, Prod.mk.injEq]
  decide

/-- The freed block ends within its chunk (below the top's header), and every
other live block ends below the freed chunk's header. -/
theorem FreeTopAt.extents {W : FreeWit} {q n : Nat} {H : List (Nat × Nat)} {maxReq k : Nat}
    (h : FreeTopAt W q n H maxReq k) :
    q + n ≤ W.top + 8 ∧ ∀ e ∈ H, e.1 + e.2 ≤ W.c.addr + 8 := by
  have hH := h.fast.heap.heap
  obtain ⟨mid, wcs, wc⟩ := hH.walk.append_inv
  obtain ⟨hca, hctop, hh, Rh, hsz, hlow, hmin, hal⟩ := wc.single
  subst hca
  have hb := wcs.chunk_bounds
  have hq := h.payload
  refine ⟨?_, fun e he => ?_⟩
  · obtain ⟨c', hc', _, h1, h2⟩ := hH.exact (q, n) List.mem_cons_self List.mem_cons_self
    rcases List.mem_append.mp hc' with hc' | hc'
    · have := hb c' hc'; simp only at h1; omega
    · simp only [List.mem_singleton] at hc'; subst hc'; simp only at h1; omega
  · obtain ⟨c', hc', _, h1, h2⟩ := hH.exact e (List.mem_cons_of_mem _ he) (List.mem_cons_of_mem _ he)
    rcases List.mem_append.mp hc' with hc' | hc'
    · have := hb c' hc'; omega
    · simp only [List.mem_singleton] at hc'; subst hc'
      exact absurd (h1.symm.trans hq) (h.distinct e he)

/-- `FastAt` reads only the footprint. -/
theorem _root_.VsaIris.VsaHeap.FastAt.transport {m m' : Mem} {H : List (Nat × Nat)} {maxReq k top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat}
    (h : FastAt m H maxReq k top brkv chunks bins) (hag : AgreeP (vsaFoot H) m m') :
    FastAt m' H maxReq k top brkv chunks bins where
  heap := h.heap.transport hag
  fast := { inuse := h.fast.inuse, bins_empty := h.fast.bins_empty
            binblocks := by
              rw [← read64_agreeP (P := vsaFoot H) hag (fun j hj => .inl (.inl ⟨by
                unfold binblocksAddr avAddr; omega, by unfold binblocksAddr avAddr; omega⟩))]
              exact h.fast.binblocks }
  reserve := h.reserve.transport_foot hag

/-- Everything fixed across one `free` run. -/
structure FreeIn (live : Nat → Prop) (maxReq headroom : Nat) (H : List (Nat × Nat))
    (q : BitVec 64) (n : Nat) (s r : BitVec 64) (saved : List (Nat × BitVec 64))
    (rv0 : Nat → BitVec 64) (mv0 : Nat → BitVec 8) (k : Nat) (W : FreeWit) : Prop where
  text : ∀ p ∈ pathText, live p.1
  sp : SpOKFast headroom s
  ral : r.toNat % 4 = 0
  saved_keys : saved.map Prod.fst = vsaSaved
  entry : EntryRegs rv0 freeEntryBV r q s saved
  top : FreeTopAt W q.toNat n H maxReq k
  img : ImgOn (vsaFoot ((q.toNat, n) :: H)) mv0 W.m
  disj : ∀ a, stackWin s headroom a →
    ¬ (heapFoot vsaLayout ((q.toNat, n) :: H) a ∨ InExt (q.toNat, n) a)

/-- The block's bytes laid over the witness memory. -/
abbrev MtB1 (W : FreeWit) (q : BitVec 64) (n : Nat) (mv0 : Nat → BitVec 8) : Mem :=
  stackBase W.m q.toNat n mv0

/-- The tracking memory at `free`'s entry. -/
abbrev MtF0 (W : FreeWit) (q : BitVec 64) (n : Nat) (s : BitVec 64) (headroom : Nat)
    (mv0 : Nat → BitVec 8) : Mem :=
  stackBase (MtB1 W q n mv0) (s.toNat - headroom) headroom mv0

/-- `free`'s prologue stores: `s0`, `q`, `ra`. -/
abbrev fproLog (s s0v q r : BitVec 64) : List WEntry :=
  [(s.toNat - 32 + 16, 8, s0v), (s.toNat - 32 + 8, 8, q), (s.toNat - 32 + 24, 8, r)]

abbrev MtFP (W : FreeWit) (q : BitVec 64) (n : Nat) (s : BitVec 64) (headroom : Nat)
    (mv0 : Nat → BitVec 8) (s0v r : BitVec 64) : Mem :=
  writeLog (MtF0 W q n s headroom mv0) (fproLog s s0v q r)

abbrev MtFB (W : FreeWit) (q : BitVec 64) (n : Nat) (s : BitVec 64) (headroom : Nat)
    (mv0 : Nat → BitVec 8) (s0v r : BitVec 64) : Mem :=
  writeLog (MtFP W q n s headroom mv0 s0v r) (mergeLog W.c.addr W.brkv)

/-- A byte of an 8-byte word that is not `a` puts `a` outside the word. -/
theorem out8 {b a : Nat} (h : ∀ i, i < 8 → b + i ≠ a) : a < b ∨ b + 8 ≤ a := by
  refine Classical.byContradiction fun hc => ?_
  exact h (a - b) (by omega) (by omega)

section FreeStages

variable {live : Nat → Prop} {maxReq headroom : Nat} {H : List (Nat × Nat)} {q : BitVec 64} {n : Nat}
  {s r : BitVec 64} {saved : List (Nat × BitVec 64)} {rv0 : Nat → BitVec 64} {mv0 : Nat → BitVec 8}
  {k : Nat} {W : FreeWit}

theorem FreeIn.frame_owned (C : FreeIn live maxReq headroom H q n s r saved rv0 mv0 k W)
    {j : Nat} (hj : j < 32) : freeBytes vsaLayout H q n s headroom (s.toNat - 32 + j) := by
  have := C.sp.head; have := C.sp.room
  exact .inl ⟨by simp only; omega, by simp only; omega⟩

/-- An allocator or block byte is outside the stack window. -/
theorem FreeIn.off_stack (C : FreeIn live maxReq headroom H q n s r saved rv0 mv0 k W) {a : Nat}
    (ha : heapFoot vsaLayout ((q.toNat, n) :: H) a ∨ InExt (q.toNat, n) a) :
    ¬ (s.toNat - headroom ≤ a ∧ a < s.toNat) := fun h =>
  C.disj a ⟨h.1, by have := C.sp.room; simp only; omega⟩ ha

/-- On allocator and block bytes, the tracking memory after the prologue is
the block overlay. -/
theorem FreeIn.mtFP_foot (C : FreeIn live maxReq headroom H q n s r saved rv0 mv0 k W)
    {a : Nat} (ha : heapFoot vsaLayout ((q.toNat, n) :: H) a ∨ InExt (q.toNat, n) a) (s0v : BitVec 64) :
    (MtFP W q n s headroom mv0 s0v r)[a]? = (MtB1 W q n mv0)[a]? := by
  have hs := C.off_stack ha
  have := C.sp.head; have := C.sp.room
  have h0 : (MtF0 W q n s headroom mv0)[a]? = (MtB1 W q n mv0)[a]? := by
    rw [stackBase_get, ite_eq_right]
    rintro ⟨h1, h2⟩
    exact hs ⟨h1, by omega⟩
  rw [← h0]
  refine writeLog_out _ _ _ ?_
  simp only [OutL]
  refine ⟨?_, ?_, ?_, trivial⟩ <;> omega

/-- The freed block lies in the arena. -/
theorem FreeIn.block_arena (C : FreeIn live maxReq headroom H q n s r saved rv0 mv0 k W) :
    heapStart + 16 ≤ q.toNat ∧ q.toNat + n + 8 ≤ heapEnd := by
  obtain ⟨G, _⟩ := C.top.facts
  have hx := C.top.extents.1
  have hp := C.top.payload
  have := G.c_lo; have := G.top_hi; have := G.top_room
  omega

/-- On allocator bytes, the block overlay is the witness memory. -/
theorem FreeIn.mtB1_heap (C : FreeIn live maxReq headroom H q n s r saved rv0 mv0 k W)
    {a : Nat} (ha : heapFoot vsaLayout ((q.toNat, n) :: H) a) : (MtB1 W q n mv0)[a]? = W.m[a]? := by
  rw [stackBase_get, ite_eq_right]
  rintro ⟨h1, h2⟩
  rcases ha with hg | ⟨_, _, h3⟩
  · have := allocGlobal_off_arena a hg
    have := C.block_arena
    omega
  · exact h3 (q.toNat, n) List.mem_cons_self ⟨h1, h2⟩

/-- A `w`-byte stack frame as loaded owned bytes. -/
abbrev frameLDn (f : Nat → BitVec 8) (sp : BitVec 64) (w : Nat) : List (Nat × DFrac × BitVec 8) :=
  (List.range w).map fun k => (sp.toNat + k, DFrac.own 1, f (sp.toNat + k))

/-- An 8-byte word as loaded owned bytes. -/
abbrev wordLD (f : Nat → BitVec 8) (a : Nat) : List (Nat × DFrac × BitVec 8) :=
  (List.range 8).map fun k => (a + k, DFrac.own 1, f (a + k))

theorem pin_range {f : Nat → BitVec 8} {m : Mem} {LD : List (Nat × DFrac × BitVec 8)} {b w : Nat}
    (h : ∀ p ∈ LD, (m[p.1]?).getD 0 = p.2.2)
    (hsub : ∀ k, k < w → (b + k, DFrac.own 1, f (b + k)) ∈ LD) :
    ∀ k, k < w → (m[b + k]?).getD 0 = f (b + k) := fun k hk => h _ (hsub k hk)

theorem mem_rangeLD {f : Nat → BitVec 8} {b w k : Nat} (hk : k < w) :
    (b + k, DFrac.own 1, f (b + k)) ∈ (List.range w).map fun k => (b + k, DFrac.own 1, f (b + k)) :=
  List.mem_map_of_mem (f := fun k => (b + k, DFrac.own 1, f (b + k))) (List.mem_range.2 hk)

theorem fepi_sp (sp a0 s0 r : BitVec 64) (f : Nat → BitVec 8) :
    finReg segFEpi (fepiL sp a0 s0 r) [wordOf f (sp.toNat + 16), wordOf f (sp.toNat + 24)] 2 =
      sp + sign_extend (m := 64) (0x020#12) := by
  simp only [finReg, segOut, segFEpi, evalBlocks_regs, runChain, SegEvalState.init]
  seg_norm

theorem fepi_s0 (sp a0 s0 r : BitVec 64) (f : Nat → BitVec 8) :
    finReg segFEpi (fepiL sp a0 s0 r) [wordOf f (sp.toNat + 16), wordOf f (sp.toNat + 24)] 8 =
      bytesVal .ld (wordOf f (sp.toNat + 16)) := by
  simp only [finReg, segOut, segFEpi, evalBlocks_regs, runChain, SegEvalState.init]
  seg_norm

theorem fepi_ra (sp a0 s0 r : BitVec 64) (f : Nat → BitVec 8) :
    finReg segFEpi (fepiL sp a0 s0 r) [wordOf f (sp.toNat + 16), wordOf f (sp.toNat + 24)] 1 =
      bytesVal .ld (wordOf f (sp.toNat + 24)) := by
  simp only [finReg, segOut, segFEpi, evalBlocks_regs, runChain, SegEvalState.init]
  seg_norm
  simp only [List.tail_cons]

/-- Back from the epilogue, at the unlock hook's tail call. -/
structure FSt5 (s r : BitVec 64) (rv0 : Nat → BitVec 64) (Mt : Mem) (S : Nat → Prop)
    (rv : Nat → BitVec 64) (mv : Nat → BitVec 8) : Prop where
  pc : rv VsaIris.PC = 0x80005070#64
  sp : rv 2 = s
  ra : rv 1 = r
  s0 : rv 8 = rv0 8
  keep : KeepS rv rv0
  img : ∀ a, S a → mv a = imgM Mt a

/-- Stage 5 of `free`: the unlock hook returns to the caller. -/
theorem fst5 (C : FreeIn live maxReq headroom H q n s r saved rv0 mv0 k W)
    {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    (h : FSt5 s r rv0 (MtFB W q n s headroom mv0 (rv0 8) r) (freeBytes vsaLayout H q n s headroom) rv mv) :
    LocalRun (vsaModel live) roR pathText mRegs (freeBytes vsaLayout H q n s headroom)
      (FreeRoomEnd vsaLayout (vsaRoomFast maxReq) H r s saved k) 2 rv mv := by
  refine unlock_hook C.text C.ral (fun rv' mv' hpc hU hI => ?_) h.pc h.ra h.img
  have hsp' : rv' 2 = s := (hU 2 (by decide) (by decide) (by decide)).trans h.sp
  have hra' : rv' 1 = r := (hU 1 (by decide) (by decide) (by decide)).trans h.ra
  have hs0' : rv' 8 = rv0 8 := (hU 8 (by decide) (by decide) (by decide)).trans h.s0
  have hkeep : ∀ q, q = 9 ∨ q = 18 ∨ q = 19 → rv' q = rv0 q := by
    rintro q (rfl | rfl | rfl)
    · exact (hU 9 (by decide) (by decide) (by decide)).trans h.keep.s1
    · exact (hU 18 (by decide) (by decide) (by decide)).trans h.keep.s2
    · exact (hU 19 (by decide) (by decide) (by decide)).trans h.keep.s3
  -- the heap after the merge
  have hag : AgreeP (vsaFoot ((q.toNat, n) :: H)) W.m (MtB1 W q n mv0) :=
    fun a ha => (C.mtB1_heap ha).symm
  have hM := FastAt.merge (C.top.fast.transport hag) C.top.payload C.top.distinct
  have himg' : ImgOn (vsaFoot H) mv'
      (mergeMem (MtB1 W q n mv0) W.c.addr W.brkv) := by
    intro a ha
    have ha' : heapFoot vsaLayout ((q.toNat, n) :: H) a ∨ InExt (q.toNat, n) a :=
      heapFoot_sub_return vsaLayout H _ _ a ha
    have hval := hI a (.inr ha')
    have hmt : (MtFB W q n s headroom mv0 (rv0 8) r)[a]? =
        (mergeMem (MtB1 W q n mv0) W.c.addr W.brkv)[a]? :=
      pointwise_congr (pointwise_writeLog _) (C.mtFP_foot ha' (rv0 8))
    have hpres : ((MtB1 W q n mv0)[a]?).isSome := by
      rcases ha' with hh | hb
      · rw [C.mtB1_heap hh, C.img a hh]; rfl
      · rw [stackBase_get, ite_eq_left ⟨hb.1, hb.2⟩]; rfl
    have hpres' := writeLog_present _ (mergeLog W.c.addr W.brkv) a hpres
    rw [hval]
    unfold imgM
    rw [hmt]
    cases hm : (mergeMem (MtB1 W q n mv0) W.c.addr W.brkv)[a]? with
    | none => rw [hm] at hpres'; cases hpres'
    | some b => rfl
  show FreeRoomEnd vsaLayout (vsaRoomFast maxReq) H r s saved k rv' mv'
  refine ⟨⟨hpc, hra', hsp', fun p hp => ?_⟩, ⟨_, himg', _, _, _, _, hM.heap⟩,
    ⟨_, _, _, _, _, himg', hM⟩⟩
  have hk : p.1 ∈ vsaSaved := by
    rw [← C.saved_keys]; exact List.mem_map_of_mem hp
  have := C.entry.saved p hp
  simp only [vsaSaved, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with h8 | h9 | h18 | h19
  · rw [h8, hs0', ← h8]; exact this
  all_goals first
    | (rw [h9, hkeep 9 (by decide), ← h9]; exact this)
    | (rw [h18, hkeep 18 (by decide), ← h18]; exact this)
    | (rw [h19, hkeep 19 (by decide), ← h19]; exact this)

/-- The freed chunk's header word is allocator footprint. -/
theorem FreeIn.hdr_foot (C : FreeIn live maxReq headroom H q n s r saved rv0 mv0 k W)
    {i : Nat} (hi : i < 8) : heapFoot vsaLayout ((q.toNat, n) :: H) (W.c.addr + 8 + i) := by
  obtain ⟨G, _⟩ := C.top.facts
  obtain ⟨hx1, hx2⟩ := C.top.extents
  have hp := C.top.payload
  have := G.c_lo; have := G.top_hi; have := G.c_top; have := G.top_room
  refine .inr ⟨by show heapStart ≤ _; omega, by show _ < heapEnd; unfold heapStart heapEnd at *; omega,
    fun e he hin => ?_⟩
  unfold InExt at hin
  rcases List.mem_cons.mp he with rfl | he
  · simp only at hin; omega
  · have := hx2 e he; omega

/-- The top chunk's header word is allocator footprint. -/
theorem FreeIn.thdr_foot (C : FreeIn live maxReq headroom H q n s r saved rv0 mv0 k W)
    {i : Nat} (hi : i < 8) : heapFoot vsaLayout ((q.toNat, n) :: H) (W.top + 8 + i) := by
  obtain ⟨G, _⟩ := C.top.facts
  obtain ⟨hx1, hx2⟩ := C.top.extents
  have hp := C.top.payload
  have := G.c_lo; have := G.top_hi; have := G.c_top; have := G.top_room
  refine .inr ⟨by show heapStart ≤ _; omega, by show _ < heapEnd; unfold heapStart heapEnd at *; omega,
    fun e he hin => ?_⟩
  unfold InExt at hin
  rcases List.mem_cons.mp he with rfl | he
  · simp only at hin; omega
  · have := hx2 e he; omega

/-- The saved frame words, read back through the merge. -/
theorem FreeIn.mtFB_frame (C : FreeIn live maxReq headroom H q n s r saved rv0 mv0 k W)
    {o : Nat} (ho : o + 8 ≤ 32) (s0v : BitVec 64) :
    read64 (MtFB W q n s headroom mv0 s0v r) (s.toNat - 32 + o) =
      read64 (MtFP W q n s headroom mv0 s0v r) (s.toNat - 32 + o) := by
  have hfr := fun j (hj : j < 32) => C.frame_owned hj
  have hoff : ∀ b, (∀ i, i < 8 → heapFoot vsaLayout ((q.toNat, n) :: H) (b + i)) →
      ∀ j, j < 8 → s.toNat - 32 + o + j < b ∨ b + 8 ≤ s.toNat - 32 + o + j := fun b hb j hj =>
    out8 fun i hi e => by
      have := C.off_stack (a := b + i) (.inl (hb i hi))
      have := C.sp.head; have := C.sp.room
      omega
  obtain ⟨G, R⟩ := C.top.facts
  have hx := C.top.extents
  refine read64_logOut fun j hj => ?_
  simp only [mergeLog, OutL]
  refine ⟨hoff _ (fun i hi => C.hdr_foot hi) j hj, hoff _ (fun i hi => .inl (.inl ⟨by
    unfold topAddr avAddr; omega, by unfold topAddr avAddr; omega⟩)) j hj, trivial⟩

/-- Allocator words read from the tracking memory are the witness's. -/
theorem FreeIn.mtFP_read (C : FreeIn live maxReq headroom H q n s r saved rv0 mv0 k W)
    {a : Nat} (ha : ∀ j, j < 8 → heapFoot vsaLayout ((q.toNat, n) :: H) (a + j)) (s0v : BitVec 64) :
    read64 (MtFP W q n s headroom mv0 s0v r) a = read64 W.m a :=
  (read64_agreeP (P := fun b => heapFoot vsaLayout ((q.toNat, n) :: H) b)
    (fun b hb => ((C.mtFP_foot (.inl hb) s0v).trans (C.mtB1_heap hb)).symm) ha).symm

/-- A word of the tracked image, read back. -/
theorem FreeIn.word {Mt : Mem} {mv : Nat → BitVec 8} {S : Nat → Prop} {a : Nat} {v : BitVec 64}
    (himg : ∀ b, S b → mv b = imgM Mt b) (hS : ∀ j, j < 8 → S (a + j))
    (hr : read64 Mt a = some v.toNat) : bytesVal .ld (wordOf mv a) = v :=
  word_val (fun j hj => himg _ (hS j hj)) hr

/-- Stage 4 of `free`: the epilogue, to the unlock hook's tail call. -/
theorem fst4 (C : FreeIn live maxReq headroom H q n s r saved rv0 mv0 k W)
    {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    (h : StPost (spF s) rv0 (MtFB W q n s headroom mv0 (rv0 8) r) (freeBytes vsaLayout H q n s headroom)
      0x80007434#64 rv mv) :
    LocalRun (vsaModel live) roR pathText mRegs (freeBytes vsaLayout H q n s headroom)
      (FreeRoomEnd vsaLayout (vsaRoomFast maxReq) H r s saved k) 3 rv mv := by
  have h32 := spF_toNat C.sp.geom
  have hle := C.sp.geom.lo; have hhi := C.sp.geom.hi
  unfold tohostAddr at hle
  have word : ∀ o, o + 8 ≤ 32 → ∀ v : BitVec 64,
      read64 (MtFP W q n s headroom mv0 (rv0 8) r) (s.toNat - 32 + o) = some v.toNat →
      bytesVal .ld (wordOf mv ((spF s).toNat + o)) = v := fun o ho v hr => by
    rw [h32]
    exact FreeIn.word h.img (fun j hj => by rw [Nat.add_assoc]; exact C.frame_owned (by omega))
      ((C.mtFB_frame ho (rv0 8)).trans hr)
  have vr := word 24 (by omega) r
    (read64_of_writeLog_at _ _ 2 _ _ rfl (by simp only [List.drop, OutLRange]))
  have vs0 := word 16 (by omega) (rv0 8)
    (read64_of_writeLog_at _ _ 0 _ _ rfl (by simp only [List.drop, OutLRange, and_true]; omega))
  refine seg_step segFEpi (fepiL (spF s) (rv 10) (rv 8) (rv 1))
    [wordOf mv ((spF s).toNat + 16), wordOf mv ((spF s).toNat + 24)] 0x80007434#64
    (frameLDn mv (spF s) 32) [] 4 rfl (by change ChainOK _ [2, 10, 8, 1] _; decide)
    (by change KeysOK [2, 10, 8, 1]; decide)
    (by change ∀ x ∈ wrChain segFEpi, x ∈ [2, 10, 8, 1]; decide)
    (fun a _ => by show OutL [] a; trivial) C.text
    (fun c _ hcode hLD => fepi_facts hcode (by rw [h32]; unfold tohostAddr; omega) (by rw [h32]; omega)
      (pin_range hLD fun k hk => mem_rangeLD hk))
    (by decide) h.pc ?_ ?_ (fun p hp => by cases hp) h.img ?_
  · intro p hp
    simp only [fepiL, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact .inl ⟨by dsimp only; decide, h.sp⟩
    all_goals exact .inl ⟨by dsimp only; decide, rfl⟩
  · intro p hp
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
    rw [List.mem_range] at hj
    refine ⟨?_, rfl⟩
    rw [h32]; exact C.frame_owned hj
  · intro rv' mv' hpc hL hU hI
    refine fst5 C ⟨hpc, ?_, ?_, ?_, h.keep.step fun q hq => hU q ?_ ?_ ?_, fun a ha => ?_⟩
    · rw [hL (2, spF s) (by simp [fepiL]), fepi_sp]
      apply BitVec.eq_of_toNat_eq
      rw [add_imm _ _ 32 (by decide) (by rw [h32]; omega), h32]; omega
    · rw [hL (1, rv 1) (by simp [fepiL]), fepi_ra, vr]
    · rw [hL (8, rv 8) (by simp [fepiL]), fepi_s0, vs0]
    · rcases hq with rfl | rfl | rfl <;> decide
    · rcases hq with rfl | rfl | rfl <;> decide
    · exact not_pin (by rcases hq with rfl | rfl | rfl <;> simp [fepiL])
    · rw [hI a ha, show (segOut segFEpi (fepiL (spF s) (rv 10) (rv 8) (rv 1))
        [wordOf mv ((spF s).toNat + 16), wordOf mv ((spF s).toNat + 24)]).log = [] from rfl,
        writeLog_nil']

end FreeStages

end VsaIris.MallocFast
