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

end VsaIris.MallocFast
