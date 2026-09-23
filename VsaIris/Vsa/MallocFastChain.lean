import VsaIris.Vsa.MallocFastRun

/-!
# `_malloc_r`'s fast path as a local run

The top-split fast path for requests `24 ≤ n ≤ 487`, from a heap with no free
chunk and a clear `binblocks` bitmap, run from its entry to its return as a
`LocalRun` over the allocator's owned registers and bytes. The eleven pieces
(wrapper, prologue, `jal` to the lock, lock hook, retarget `ret`, bin checks,
split, `jal` to the unlock, unlock hook, `ret`, epilogue) are chained through
`seg_step`/`jal_step`, one stage lemma each (`st10` … `st0`).

The owned image is tracked as the total read of a memory: the heap witness
`m1` with the stack window inserted (`Mt0`), advanced by the prologue's stack
stores (`MtP`) and the split's stores (`MtS`). At the return the heap part of
`MtS` is `splitMem m1 …` (`FastAt.split`), which gives the post shape and
room.
-/

namespace VsaIris.MallocFast

open Vsa.Sim Vsa.MemRepr Vsa.Sim.DlHeap VsaIris.Inst VsaIris.VsaHeap
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Machine (Config)
open Iris

/-! ## Memories and words -/

/-- `m` with the bytes of `[lo, lo + len)` set to the image `f`. -/
def stackBase (m : Mem) (lo len : Nat) (f : Nat → BitVec 8) : Mem :=
  (List.range len).foldl (fun m k => m.insert (lo + k) (f (lo + k))) m

theorem stackBase_get (m : Mem) (lo len : Nat) (f : Nat → BitVec 8) (a : Nat) :
    (stackBase m lo len f)[a]? = if lo ≤ a ∧ a < lo + len then some (f a) else m[a]? := by
  unfold stackBase
  induction len generalizing a with
  | zero => simp only [List.range_zero, List.foldl_nil]; rw [ite_eq_right (by omega)]
  | succ len ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Std.ExtHashMap.getElem?_insert]
    by_cases h : lo + len = a
    · subst h; simp
    · rw [ite_eq_right (by simpa using h), ih]
      by_cases h2 : lo ≤ a ∧ a < lo + len
      · rw [ite_eq_left h2, ite_eq_left ⟨h2.1, by omega⟩]
      · rw [ite_eq_right h2, ite_eq_right (by omega)]

/-- `x ||| 1 = x + 1` for an even `x`. -/
theorem or_one_even (x : BitVec 64) (h : x.toNat % 2 = 0) :
    x ||| sign_extend (m := 64) (0x001#12) = x + 1#64 := by
  rw [show (sign_extend (m := 64) (0x001#12) : BitVec 64) = 1#64 by decide]
  refine (BitVec.add_eq_or_of_and_eq_zero x 1#64 ?_).symm
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (1#64 : BitVec 64).toNat = 2 ^ 1 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod]
  simpa using h

/-- A loaded word, read back from a tracking memory that carries the image. -/
theorem word_val {Mt : Mem} {f : Nat → BitVec 8} {a : Nat} {v : BitVec 64}
    (himg : ∀ k, k < 8 → f (a + k) = imgM Mt (a + k)) (hr : read64 Mt a = some v.toNat) :
    bytesVal .ld (wordOf f a) = v := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, h0, h1, h2, h3, h4, h5, h6, h7, _⟩ :=
    read64_bytes Mt a v.toNat hr
  refine wordOf_value (m := Mt) (fun k hk => ?_) hr
  rw [himg k hk]
  unfold imgM
  have : (Mt[a + k]?).isSome := by
    rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k
    all_goals first
      | (simp only [Nat.add_zero]; rw [h0]; rfl)
      | (rw [h1]; rfl) | (rw [h2]; rfl) | (rw [h3]; rfl) | (rw [h4]; rfl) | (rw [h5]; rfl)
      | (rw [h6]; rfl) | (rw [h7]; rfl) | omega
  cases hm : Mt[a + k]? with
  | none => rw [hm] at this; cases this
  | some b => rfl

/-- A `Pointwise` memory transformer respects byte agreement. -/
theorem pointwise_congr {f : Mem → Mem} (hf : Pointwise f) {m m' : Mem} {a : Nat}
    (h : m[a]? = m'[a]?) : (f m)[a]? = (f m')[a]? := by
  rcases hf a with h1 | ⟨v, h1⟩
  · rw [h1, h1, h]
  · rw [h1, h1]

/-! ## The run's context -/

/-- The fast path's capacity predicate: the fast heap shape with `k` credits. -/
def vsaRoomFast (maxReq : Nat) : RoomPred := fun img H k =>
  ∃ m top brkv chunks bins, ImgOn (vsaFoot H) img m ∧ FastAt m H maxReq k top brkv chunks bins

theorem roomLocal_fast (maxReq : Nat) : RoomLocal vsaLayout (vsaRoomFast maxReq) := by
  rintro H img img' k h ⟨m, top, brkv, chunks, bins, hm, hf⟩
  exact ⟨m, top, brkv, chunks, bins, fun a ha => (hm a ha).trans (by rw [h a ha]), hf⟩

/-- The caller's stack discipline on the fast path. -/
structure SpOKFast (headroom : Nat) (s : BitVec 64) : Prop where
  geom : SpGeom s
  head : 96 ≤ headroom
  room : headroom ≤ s.toNat

/-- Everything fixed across one fast-path run. -/
structure FastIn (live : Nat → Prop) (maxReq headroom : Nat) (H : List (Nat × Nat))
    (n s r : BitVec 64) (saved : List (Nat × BitVec 64)) (rv0 : Nat → BitVec 64)
    (mv0 : Nat → BitVec 8) (k : Nat) (m1 : Mem) (top brkv : Nat) (chunks : List Chunk)
    (bins : Nat → List Nat) : Prop where
  text : ∀ p ∈ pathText, live p.1
  max : maxReq ≤ 487
  sp : SpOKFast headroom s
  ral : r.toNat % 4 = 0
  n_lo : 24 ≤ n.toNat
  n_hi : n.toNat ≤ maxReq
  saved_keys : saved.map Prod.fst = vsaSaved
  entry : EntryRegs rv0 mallocEntryBV r n s saved
  fast : FastAt m1 H maxReq (k + 1) top brkv chunks bins
  img : ImgOn (vsaFoot H) mv0 m1
  disj : ∀ a, stackWin s headroom a → ¬ heapFoot vsaLayout H a

/-- The chunk size of the request. -/
abbrev nbN (n : BitVec 64) : Nat := (n.toNat + 23) / 16 * 16

/-- The allocator's stack pointer. -/
abbrev spN (s : BitVec 64) : BitVec 64 := s + sign_extend (m := 64) (0xfa0#12)

/-- The tracking memory at entry. -/
abbrev Mt0 (m1 : Mem) (s : BitVec 64) (headroom : Nat) (mv0 : Nat → BitVec 8) : Mem :=
  stackBase m1 (s.toNat - headroom) headroom mv0

/-- The prologue's stack stores. -/
abbrev proLogN (s s0v r n : BitVec 64) : List WEntry :=
  [(s.toNat - 96 + 80, 8, s0v), (s.toNat - 96 + 88, 8, r), (s.toNat - 96 + 8, 8, nbOf n)]

/-- The split's stores (heap, the saved top on the stack, heap, heap). -/
abbrev splitLogN (s : BitVec 64) (top nb brkv : Nat) : List WEntry :=
  [(top + 8, 8, BitVec.ofNat 64 (nb + 1)), (s.toNat - 96 + 8, 8, BitVec.ofNat 64 top),
   (topAddr, 8, BitVec.ofNat 64 (top + nb)), (top + nb + 8, 8, BitVec.ofNat 64 (brkv - top - nb + 1))]

/-- The saved registers the fast path never touches. -/
structure KeepS (rv rv0 : Nat → BitVec 64) : Prop where
  s1 : rv 9 = rv0 9
  s2 : rv 18 = rv0 18
  s3 : rv 19 = rv0 19

/-- The frame bytes `[sp, sp + 96)` as loaded owned bytes. -/
abbrev frameLD (f : Nat → BitVec 8) (sp : BitVec 64) : List (Nat × DFrac × BitVec 8) :=
  (List.range 96).map fun k => (sp.toNat + k, DFrac.own 1, f (sp.toNat + k))

theorem frameLD_pin {f : Nat → BitVec 8} {sp : BitVec 64} {m : Mem}
    (h : ∀ p ∈ frameLD f sp, (m[p.1]?).getD 0 = p.2.2) :
    ∀ k, k < 96 → (m[sp.toNat + k]?).getD 0 = f (sp.toNat + k) :=
  fun k hk => h _ (List.mem_map_of_mem (f := fun k => (sp.toNat + k, DFrac.own 1, f (sp.toNat + k)))
    (List.mem_range.2 hk))

section Stages

variable {live : Nat → Prop} {maxReq headroom : Nat} {H : List (Nat × Nat)} {n s r : BitVec 64}
  {saved : List (Nat × BitVec 64)} {rv0 : Nat → BitVec 64} {mv0 : Nat → BitVec 8} {k : Nat}
  {m1 : Mem} {top brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat}

theorem FastIn.sp96 (C : FastIn live maxReq headroom H n s r saved rv0 mv0 k m1 top brkv chunks bins) :
    (spN s).toNat = s.toNat - 96 := VsaIris.MallocFast.sp96 C.sp.geom

/-- Frame bytes are owned (in the stack window). -/
theorem FastIn.frame_owned (C : FastIn live maxReq headroom H n s r saved rv0 mv0 k m1 top brkv chunks bins)
    {j : Nat} (hj : j < 96) : mallocBytes vsaLayout H s headroom (s.toNat - 96 + j) := by
  have := C.sp.head; have := C.sp.room
  exact .inl ⟨by simp only; omega, by simp only; omega⟩

/-- A stack byte is not a heap byte. -/
theorem FastIn.stack_not_heap (C : FastIn live maxReq headroom H n s r saved rv0 mv0 k m1 top brkv chunks bins)
    {j a : Nat} (hj : j < 96) (ha : heapFoot vsaLayout H a) : s.toNat - 96 + j ≠ a := by
  rintro rfl
  have := C.sp.head; have := C.sp.room
  exact C.disj _ ⟨by simp only; omega, by simp only; omega⟩ ha

/-- Two 8-byte words with no common byte are disjoint intervals. -/
theorem disj8 {a b : Nat} (h : ∀ i, i < 8 → ∀ j, j < 8 → a + i ≠ b + j) :
    a + 8 ≤ b ∨ b + 8 ≤ a := by
  refine Classical.byContradiction fun hc => ?_
  have h1 : max a b - a < 8 := by omega
  have h2 : max a b - b < 8 := by omega
  exact h _ h1 _ h2 (by omega)

/-- The split's heap words are allocator footprint. -/
theorem FastIn.split_foot (C : FastIn live maxReq headroom H n s r saved rv0 mv0 k m1 top brkv chunks bins)
    {i : Nat} (hi : i < 8) :
    heapFoot vsaLayout H (top + 8 + i) ∧ heapFoot vsaLayout H (topAddr + i) ∧
      heapFoot vsaLayout H (top + nbN n + 8 + i) := by
  have hH := C.fast.heap
  obtain ⟨bytes, rr, hb⟩ := C.fast.reserve_top (Nat.succ_pos k)
  have hcap := rr.capacity
  have hlo := rr.arena_lo; have hhi := rr.arena_hi
  have hP := physSize_min maxReq
  have hnbP : nbN n ≤ physSize maxReq := by
    have := C.n_hi; simp only [physSize, Nat.max_def, nbN]; split <;> omega
  have hk1 : physSize maxReq ≤ (k + 1) * physSize maxReq :=
    Nat.le_mul_of_pos_left _ (Nat.succ_pos k)
  refine ⟨foot_header hH (.inl rfl) i hi, .inl (.inl ⟨by unfold topAddr avAddr; omega,
    by unfold topAddr avAddr; omega⟩), .inr ⟨by show heapStart ≤ _; unfold heapStart at hlo ⊢; omega,
    by show _ < heapEnd; unfold heapEnd at hhi ⊢; omega, fun e he hin => ?_⟩⟩
  obtain ⟨c, hc, _, h1, h2⟩ := hH.heap.live e he
  have := hH.heap.walk.chunk_bounds c hc
  unfold InExt at hin
  omega

/-- The request, the chunk size and the top chunk, named. -/
structure FastGeo (n : BitVec 64) (maxReq top brkv : Nat) : Prop where
  nb16 : nbN n % 16 = 0
  nb32 : 32 ≤ nbN n
  nbP : nbN n ≤ physSize maxReq
  nb496 : nbN n ≤ 496
  n8 : n.toNat + 8 ≤ nbN n
  n_lo : 24 ≤ n.toNat
  room : nbN n + 32 ≤ brkv - top
  top_lo : heapStart ≤ top
  top_hi : brkv ≤ heapEnd
  top16 : top % 16 = 0
  size16 : (brkv - top) % 16 = 0
  top_le : top ≤ brkv

theorem FastIn.geo (C : FastIn live maxReq headroom H n s r saved rv0 mv0 k m1 top brkv chunks bins) :
    FastGeo n maxReq top brkv := by
  obtain ⟨bytes, rr, hb⟩ := C.fast.reserve_top (Nat.succ_pos k)
  have hcap := rr.capacity
  have hP := physSize_min maxReq
  have hk1 : physSize maxReq ≤ (k + 1) * physSize maxReq :=
    Nat.le_mul_of_pos_left _ (Nat.succ_pos k)
  have hnbP : nbN n ≤ physSize maxReq := by
    have := C.n_hi; simp only [physSize, Nat.max_def, nbN]; split <;> omega
  have := C.n_lo; have := C.n_hi; have := C.max
  have hH := C.fast.heap.heap
  exact ⟨by simp only [nbN]; omega, by simp only [nbN]; omega, hnbP, by simp only [nbN]; omega,
    by simp only [nbN]; omega, C.n_lo, by omega, hH.walk.le, hH.brk_le, rr.top_aligned,
    hH.top_size, hH.top_le⟩

/-- The tracking memory after the prologue. -/
abbrev MtP (m1 : Mem) (s : BitVec 64) (headroom : Nat) (mv0 : Nat → BitVec 8) (s0v r n : BitVec 64) :
    Mem :=
  writeLog (Mt0 m1 s headroom mv0) (proLogN s s0v r n)

/-- The tracking memory after the split. -/
abbrev MtS (m1 : Mem) (s : BitVec 64) (headroom : Nat) (mv0 : Nat → BitVec 8) (s0v r n : BitVec 64)
    (top brkv : Nat) : Mem :=
  writeLog (MtP m1 s headroom mv0 s0v r n) (splitLogN s top (nbN n) brkv)

/-- The saved words of the frame, read back after the split. -/
theorem FastIn.mtS_reads (C : FastIn live maxReq headroom H n s r saved rv0 mv0 k m1 top brkv chunks bins) :
    read64 (MtS m1 s headroom mv0 (rv0 8) r n top brkv) (s.toNat - 96 + 80) = some (rv0 8).toNat ∧
    read64 (MtS m1 s headroom mv0 (rv0 8) r n top brkv) (s.toNat - 96 + 88) = some r.toNat ∧
    read64 (MtS m1 s headroom mv0 (rv0 8) r n top brkv) (s.toNat - 96 + 8) = some top := by
  have G := C.geo
  have hle := C.sp.geom.lo; have hhi := C.sp.geom.hi
  have hsp : ∀ j, j < 96 → ∀ i, i < 8 →
      s.toNat - 96 + j ≠ top + 8 + i ∧ s.toNat - 96 + j ≠ topAddr + i ∧
      s.toNat - 96 + j ≠ top + nbN n + 8 + i := fun j hj i hi =>
    ⟨C.stack_not_heap hj (C.split_foot hi).1, C.stack_not_heap hj (C.split_foot hi).2.1,
      C.stack_not_heap hj (C.split_foot hi).2.2⟩
  have off : ∀ o, o + 8 ≤ 96 → 16 ≤ o → read64 (MtS m1 s headroom mv0 (rv0 8) r n top brkv)
      (s.toNat - 96 + o) = read64 (MtP m1 s headroom mv0 (rv0 8) r n) (s.toNat - 96 + o) := by
    intro o ho ho8
    refine read64_logOut fun j hj => ?_
    simp only [OutL]
    refine ⟨?_, ?_, ?_, ?_, trivial⟩
    · have := disj8 (a := s.toNat - 96 + o) (b := top + 8) fun i hi i' hi' => by
        have := (hsp (o + i) (by omega) i' hi').1; omega
      omega
    · omega
    · have := disj8 (a := s.toNat - 96 + o) (b := topAddr) fun i hi i' hi' => by
        have := (hsp (o + i) (by omega) i' hi').2.1; omega
      unfold topAddr avAddr at this ⊢; omega
    · have := disj8 (a := s.toNat - 96 + o) (b := top + nbN n + 8) fun i hi i' hi' => by
        have := (hsp (o + i) (by omega) i' hi').2.2; omega
      omega
  have hs0 : read64 (MtP m1 s headroom mv0 (rv0 8) r n) (s.toNat - 96 + 80) = some (rv0 8).toNat :=
    read64_of_writeLog_at _ _ 0 _ _ rfl (by simp only [List.drop, OutLRange, and_true]; omega)
  have hr : read64 (MtP m1 s headroom mv0 (rv0 8) r n) (s.toNat - 96 + 88) = some r.toNat :=
    read64_of_writeLog_at _ _ 1 _ _ rfl (by simp only [List.drop, OutLRange, and_true]; omega)
  refine ⟨(off 80 (by omega) (by omega)).trans hs0, (off 88 (by omega) (by omega)).trans hr, ?_⟩
  have := read64_of_writeLog_at (MtP m1 s headroom mv0 (rv0 8) r n) (splitLogN s top (nbN n) brkv)
    1 (s.toNat - 96 + 8) (BitVec.ofNat 64 top) rfl (by
      simp only [List.drop, OutLRange]
      have h1 := hsp 8 (by omega)
      refine ⟨?_, ?_, trivial⟩
      · have := disj8 (a := s.toNat - 96 + 8) (b := topAddr) fun i hi i' hi' => by
          have := (hsp (8 + i) (by omega) i' hi').2.1; omega
        unfold topAddr avAddr at this ⊢; omega
      · have := disj8 (a := s.toNat - 96 + 8) (b := top + nbN n + 8) fun i hi i' hi' => by
          have := (hsp (8 + i) (by omega) i' hi').2.2; omega
        omega)
  rw [this, ofNat_toNat_lt (by have h1 := G.top_hi; have h2 := G.top_le; unfold heapEnd at h1; omega)]

/-- Dropping a log entry that does not write `a`. -/
theorem drop_mid {X Y : Mem} {e1 eS : WEntry} {rest : List WEntry} {a : Nat}
    (hw : eS.2.1 = 8) (hS : a < eS.1 ∨ eS.1 + 8 ≤ a) (h : X[a]? = Y[a]?) :
    (writeLog X (e1 :: eS :: rest))[a]? = (writeLog Y (e1 :: rest))[a]? := by
  show (writeLog (applyW (applyW X e1) eS) rest)[a]? = (writeLog (applyW Y e1) rest)[a]?
  refine pointwise_congr (pointwise_writeLog rest) ?_
  rw [applyW_getElem_disjoint _ _ _ (by rw [hw]; decide) (by rw [hw]; exact hS)]
  exact pointwise_congr (pointwise_applyW e1) h

/-- On the heap, the tracking memory after the split is the split heap. -/
theorem FastIn.post_heap (C : FastIn live maxReq headroom H n s r saved rv0 mv0 k m1 top brkv chunks bins)
    {a : Nat} (ha : heapFoot vsaLayout H a) :
    (MtS m1 s headroom mv0 (rv0 8) r n top brkv)[a]? = (splitMem m1 top (nbN n) brkv)[a]? := by
  have hs : ∀ j, j < 96 → s.toNat - 96 + j ≠ a := fun j hj => C.stack_not_heap hj ha
  have hle := C.sp.geom.lo
  have h0 : (Mt0 m1 s headroom mv0)[a]? = m1[a]? := by
    rw [stackBase_get, ite_eq_right]
    rintro ⟨h1, h2⟩
    exact C.disj a ⟨h1, by simp only; omega⟩ ha
  have hP : (MtP m1 s headroom mv0 (rv0 8) r n)[a]? = m1[a]? := by
    rw [← h0]
    refine writeLog_out _ _ _ ?_
    simp only [OutL]
    refine ⟨?_, ?_, ?_, trivial⟩ <;>
    · refine Classical.byContradiction fun hc => ?_
      exact hs (a - (s.toNat - 96)) (by omega) (by omega)
  unfold MtS splitLogN splitMem splitLog
  exact drop_mid rfl (by
    simp only
    refine Classical.byContradiction fun hc => ?_
    exact hs (a - (s.toNat - 96)) (by omega) (by omega)) hP

/-- The split heap is present on the allocator's footprint. -/
theorem FastIn.post_present (C : FastIn live maxReq headroom H n s r saved rv0 mv0 k m1 top brkv chunks bins)
    {a : Nat} (ha : heapFoot vsaLayout H a) : ((splitMem m1 top (nbN n) brkv)[a]?).isSome :=
  writeLog_present _ _ _ (by rw [C.img a ha]; rfl)

/-! ## Stages -/

theorem writeLog_nil' (m : Mem) : writeLog m [] = m := rfl

/-- A register outside a pin list. -/
theorem not_pin {L : GRegs} {q : Nat} (h : q ∉ L.map Prod.fst) : ∀ p ∈ L, p.1 ≠ q :=
  fun p hp e => h (e ▸ List.mem_map_of_mem hp)

/-- The owned registers and bytes of a malloc run. -/
abbrev mRegs : List Nat := allocRegs vsaClob vsaSaved

/-- Stage 10: back from `__malloc_unlock`, at the epilogue. -/
structure St10 (s : BitVec 64) (rv0 : Nat → BitVec 64) (Mt : Mem) (S : Nat → Prop)
    (rv : Nat → BitVec 64) (mv : Nat → BitVec 8) : Prop where
  pc : rv VsaIris.PC = 0x80004c14#64
  sp : rv 2 = spN s
  keep : KeepS rv rv0
  img : ∀ a, S a → mv a = imgM Mt a

theorem st10 (C : FastIn live maxReq headroom H n s r saved rv0 mv0 k m1 top brkv chunks bins)
    {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    (h : St10 s rv0 (MtS m1 s headroom mv0 (rv0 8) r n top brkv) (mallocBytes vsaLayout H s headroom) rv mv) :
    LocalRun (vsaModel live) roR pathText mRegs (mallocBytes vsaLayout H s headroom)
      (MallocRoomEnd vsaLayout (vsaRoomFast maxReq) H n r s saved k) 1 rv mv := by
  have G := C.geo
  have h96 := C.sp96
  have hle := C.sp.geom.lo; have hhi := C.sp.geom.hi; have hal := C.sp.geom.align
  unfold tohostAddr at hle
  obtain ⟨R80, R88, R8⟩ := C.mtS_reads
  have frame : ∀ j, j < 96 → mv (s.toNat - 96 + j) = imgM (MtS m1 s headroom mv0 (rv0 8) r n top brkv)
      (s.toNat - 96 + j) := fun j hj => h.img _ (C.frame_owned hj)
  have word : ∀ o, o + 8 ≤ 96 → ∀ v : BitVec 64,
      read64 (MtS m1 s headroom mv0 (rv0 8) r n top brkv) (s.toNat - 96 + o) = some v.toNat →
      bytesVal .ld (wordOf mv ((spN s).toNat + o)) = v := fun o ho v hr => by
    rw [h96]
    exact word_val (fun j hj => by rw [Nat.add_assoc]; exact frame (o + j) (by omega)) hr
  have vr := word 88 (by omega) r R88
  have vs0 := word 80 (by omega) (rv0 8) R80
  have htopv : (BitVec.ofNat 64 top).toNat = top :=
    ofNat_toNat_lt (by have h1 := G.top_hi; have h2 := G.top_le; unfold heapEnd at h1; omega)
  have vtop := word 8 (by omega) (BitVec.ofNat 64 top) (by rw [R8, htopv])
  refine seg_step (Q := MallocRoomEnd vsaLayout (vsaRoomFast maxReq) H n r s saved k)
    segEpi (epiL (spN s) (rv 15) (rv 10) (rv 1) (rv 8)) (epiLds mv (spN s)) 0x80004c14#64
    (frameLD mv (spN s)) [] 6 rfl (by change ChainOK _ [2, 15, 10, 1, 8] _; decide)
    (by change KeysOK [2, 15, 10, 1, 8]; decide)
    (by change ∀ x ∈ wrChain segEpi, x ∈ [2, 15, 10, 1, 8]; decide)
    (fun a _ => by show OutL [] a; trivial) C.text
    (fun c _ hcode hLD => epi_facts hcode (by rw [h96]; unfold tohostAddr; omega)
      (by rw [h96]; omega) (frameLD_pin hLD) vr C.ral)
    (by decide) h.pc ?_ ?_ (fun p hp => by cases hp) h.img ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact .inl ⟨by dsimp only; decide, h.sp⟩
    all_goals exact .inl ⟨by dsimp only; decide, rfl⟩
  · intro p hp
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
    rw [List.mem_range] at hj
    refine ⟨?_, rfl⟩
    rw [h96]; exact C.frame_owned hj
  · intro rv' mv' hpc hL hU hI
    have hr' : rv' 1 = r := (hL (1, rv 1) (by simp)).trans vr
    have hs0' : rv' 8 = rv0 8 := (hL (8, rv 8) (by simp)).trans vs0
    have hsp' : rv' 2 = s := by
      rw [hL (2, spN s) (by simp)]
      show spN s + sign_extend (m := 64) (0x060#12) = s
      apply BitVec.eq_of_toNat_eq
      rw [add_imm _ _ 96 (by decide) (by rw [h96]; omega), h96]; omega
    have ha0 : (rv' VsaIris.a0).toNat = top + 16 := by
      rw [show VsaIris.a0 = 10 from rfl, hL (10, rv 10) (by simp)]
      show (bytesVal .ld (wordOf mv ((spN s).toNat + 8)) + sign_extend (m := 64) (0x010#12)).toNat = _
      have hb : top + 16 < 2 ^ 64 := by
        have h1 := G.top_hi; have h2 := G.top_le; unfold heapEnd at h1; omega
      rw [vtop, add_imm _ _ 16 (by decide) (by rw [htopv]; exact hb), htopv]
    have hpc' : rv' VsaIris.PC = r := by
      rw [hpc]
      show Sail.BitVec.update (bytesVal .ld (wordOf mv ((spN s).toNat + 88)) +
        sign_extend (m := 64) (0#12)) 0 0#1 = r
      rw [vr, ret_tgt r C.ral]
    have hkeep : ∀ q, q = 9 ∨ q = 18 ∨ q = 19 → rv' q = rv0 q := by
      rintro q (rfl | rfl | rfl)
      · exact (hU 9 (by decide) (by decide) (not_pin (by simp))).trans h.keep.s1
      · exact (hU 18 (by decide) (by decide) (not_pin (by simp))).trans h.keep.s2
      · exact (hU 19 (by decide) (by decide) (not_pin (by simp))).trans h.keep.s3
    -- the post image, on the heap
    have hsplit := C.fast.split (n := n.toNat) G.nb16 G.nb32 G.nbP (by have := G.n_lo; omega) G.n8
    have himg' : ImgOn (vsaFoot ((top + 16, n.toNat) :: H)) mv' (splitMem m1 top (nbN n) brkv) := by
      intro a ha
      have ha' : heapFoot vsaLayout H a := by
        rcases ha with hg | ⟨h1, h2, h3⟩
        · exact .inl hg
        · exact .inr ⟨h1, h2, fun e he => h3 e (List.mem_cons_of_mem _ he)⟩
      have hlog : (segOut segEpi (epiL (spN s) (rv 15) (rv 10) (rv 1) (rv 8))
        (epiLds mv (spN s))).log = [] := rfl
      rw [hI a (.inr ha'), hlog, writeLog_nil']
      unfold imgM
      rw [C.post_heap ha']
      have := C.post_present ha'
      cases hm : (splitMem m1 top (nbN n) brkv)[a]? with
      | none => rw [hm] at this; cases this
      | some b => rfl
    show MallocRoomEnd vsaLayout (vsaRoomFast maxReq) H n r s saved k rv' mv'
    refine ⟨⟨hpc', hr', hsp', fun p hp => ?_⟩, ?_, ?_, ?_, ?_⟩ <;> (try rw [ha0])
    · have hk : p.1 ∈ vsaSaved := by
        rw [← C.saved_keys]; exact List.mem_map_of_mem hp
      have := C.entry.saved p hp
      simp only [vsaSaved, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with h8 | h9 | h18 | h19
      · rw [h8, hs0', ← h8]; exact this
      all_goals first
        | (rw [h9, hkeep 9 (by decide), ← h9]; exact this)
        | (rw [h18, hkeep 18 (by decide), ← h18]; exact this)
        | (rw [h19, hkeep 19 (by decide), ← h19]; exact this)
    · -- the block is fresh
      have hH := C.fast.heap.heap
      obtain ⟨bytes, rr, hb⟩ := C.fast.reserve_top (Nat.succ_pos k)
      refine ⟨by omega, by show heapStart ≤ _; have := G.top_lo; omega,
        by show _ ≤ heapEnd; have := G.top_hi; have := G.room; have := G.n8; omega,
        fun e he a ha hin => ?_⟩
      obtain ⟨c, hc, _, h1, h2⟩ := hH.live e he
      have := hH.walk.chunk_bounds c hc
      unfold InExt at ha hin
      simp only at ha hin
      omega
    · have := G.top16; omega
    · exact ⟨_, himg', _, _, _, _, hsplit.heap⟩
    · exact ⟨_, _, _, _, _, himg', hsplit⟩

end Stages

end VsaIris.MallocFast
