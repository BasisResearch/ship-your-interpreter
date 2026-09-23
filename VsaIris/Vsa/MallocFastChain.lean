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
  n_hi : n.toNat ≤ maxReq
  saved_keys : saved.map Prod.fst = vsaSaved
  entry : EntryRegs rv0 mallocEntryBV r n s saved
  fast : FastAt m1 H maxReq (k + 1) top brkv chunks bins
  img : ImgOn (vsaFoot H) mv0 m1
  disj : ∀ a, stackWin s headroom a → ¬ heapFoot vsaLayout H a

/-- The chunk size of the request. -/
abbrev nbN (n : BitVec 64) : Nat := max 32 ((n.toNat + 23) / 16 * 16)

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
  {m1 : Mem} {top brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {pl : List WEntry}

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
    have := C.n_hi; simp only [physSize, nbN]; omega
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
    have := C.n_hi; simp only [physSize, nbN]; omega
  have := C.n_hi; have := C.max
  have hH := C.fast.heap.heap
  exact ⟨by simp only [nbN]; omega, by simp only [nbN]; omega, hnbP, by simp only [nbN]; omega,
    by simp only [nbN]; omega, by omega, hH.walk.le, hH.brk_le, rr.top_aligned,
    hH.top_size, hH.top_le⟩

/-- The tracking memory after the prologue. -/
abbrev MtP (m1 : Mem) (s : BitVec 64) (headroom : Nat) (mv0 : Nat → BitVec 8) (pl : List WEntry) :
    Mem :=
  writeLog (Mt0 m1 s headroom mv0) pl

/-- The tracking memory after the split. -/
abbrev MtS (m1 : Mem) (s : BitVec 64) (headroom : Nat) (mv0 : Nat → BitVec 8) (pl : List WEntry)
    (n : BitVec 64) (top brkv : Nat) : Mem :=
  writeLog (MtP m1 s headroom mv0 pl) (splitLogN s top (nbN n) brkv)

/-- A prologue's stack stores: inside the frame, saving `s0` at 80 and `ra` at 88. -/
structure ProLog (s s0v r : BitVec 64) (pl : List WEntry) : Prop where
  off : ∀ a, (∀ j, j < 96 → s.toNat - 96 + j ≠ a) → OutL pl a
  s0 : ∀ M, read64 (writeLog M pl) (s.toNat - 96 + 80) = some s0v.toNat
  ra : ∀ M, read64 (writeLog M pl) (s.toNat - 96 + 88) = some r.toNat

/-- The larger requests' prologue saves `s0`, `ra` and `nb`. -/
theorem proLog_A {s : BitVec 64} (hs : SpGeom s) (s0v r n : BitVec 64) :
    ProLog s s0v r (proLogN s s0v r n) := by
  have := hs.lo; unfold tohostAddr at this
  refine ⟨fun a ha => ?_, fun M => ?_, fun M => ?_⟩
  · simp only [proLogN, OutL]
    refine ⟨?_, ?_, ?_, trivial⟩ <;>
    · refine Classical.byContradiction fun hc => ?_
      exact ha (a - (s.toNat - 96)) (by omega) (by omega)
  · exact read64_of_writeLog_at _ _ 0 _ _ rfl (by simp only [List.drop, OutLRange, and_true]; omega)
  · exact read64_of_writeLog_at _ _ 1 _ _ rfl (by simp only [List.drop, OutLRange, and_true]; omega)

theorem FastIn.mtP_heap (C : FastIn live maxReq headroom H n s r saved rv0 mv0 k m1 top brkv chunks bins)
    {s0v : BitVec 64} {pl : List WEntry} (P : ProLog s s0v r pl)
    {a : Nat} (ha : heapFoot vsaLayout H a) :
    (MtP m1 s headroom mv0 pl)[a]? = m1[a]? := by
  have hs : ∀ j, j < 96 → s.toNat - 96 + j ≠ a := fun j hj => C.stack_not_heap hj ha
  have hle := C.sp.geom.lo
  have h0 : (Mt0 m1 s headroom mv0)[a]? = m1[a]? := by
    rw [stackBase_get, ite_eq_right]
    rintro ⟨h1, h2⟩
    exact C.disj a ⟨h1, by simp only; omega⟩ ha
  rw [← h0]
  exact writeLog_out _ _ _ (P.off a hs)

theorem FastIn.mtP_read (C : FastIn live maxReq headroom H n s r saved rv0 mv0 k m1 top brkv chunks bins)
    {s0v : BitVec 64} {pl : List WEntry} (P : ProLog s s0v r pl)
    {a : Nat} (ha : ∀ j, j < 8 → heapFoot vsaLayout H (a + j)) :
    read64 (MtP m1 s headroom mv0 pl) a = read64 m1 a :=
  (read64_agreeP (P := fun b => heapFoot vsaLayout H b) (fun b hb => (C.mtP_heap P hb).symm) ha).symm

/-- The saved words of the frame, read back after the split. -/
theorem FastIn.mtS_reads (C : FastIn live maxReq headroom H n s r saved rv0 mv0 k m1 top brkv chunks bins)
    {pl : List WEntry} (P : ProLog s (rv0 8) r pl) :
    read64 (MtS m1 s headroom mv0 pl n top brkv) (s.toNat - 96 + 80) = some (rv0 8).toNat ∧
    read64 (MtS m1 s headroom mv0 pl n top brkv) (s.toNat - 96 + 88) = some r.toNat ∧
    read64 (MtS m1 s headroom mv0 pl n top brkv) (s.toNat - 96 + 8) = some top := by
  have G := C.geo
  have hle := C.sp.geom.lo; have hhi := C.sp.geom.hi
  have hsp : ∀ j, j < 96 → ∀ i, i < 8 →
      s.toNat - 96 + j ≠ top + 8 + i ∧ s.toNat - 96 + j ≠ topAddr + i ∧
      s.toNat - 96 + j ≠ top + nbN n + 8 + i := fun j hj i hi =>
    ⟨C.stack_not_heap hj (C.split_foot hi).1, C.stack_not_heap hj (C.split_foot hi).2.1,
      C.stack_not_heap hj (C.split_foot hi).2.2⟩
  have off : ∀ o, o + 8 ≤ 96 → 16 ≤ o → read64 (MtS m1 s headroom mv0 pl n top brkv)
      (s.toNat - 96 + o) = read64 (MtP m1 s headroom mv0 pl) (s.toNat - 96 + o) := by
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
  have hs0 := P.s0 (Mt0 m1 s headroom mv0)
  have hr := P.ra (Mt0 m1 s headroom mv0)
  refine ⟨(off 80 (by omega) (by omega)).trans hs0, (off 88 (by omega) (by omega)).trans hr, ?_⟩
  have := read64_of_writeLog_at (MtP m1 s headroom mv0 pl) (splitLogN s top (nbN n) brkv)
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
    {pl : List WEntry} (P : ProLog s (rv0 8) r pl) {a : Nat} (ha : heapFoot vsaLayout H a) :
    (MtS m1 s headroom mv0 pl n top brkv)[a]? = (splitMem m1 top (nbN n) brkv)[a]? := by
  have hs : ∀ j, j < 96 → s.toNat - 96 + j ≠ a := fun j hj => C.stack_not_heap hj ha
  have hle := C.sp.geom.lo
  have hP := C.mtP_heap P ha
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
    (P : ProLog s (rv0 8) r pl)
    {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    (h : St10 s rv0 (MtS m1 s headroom mv0 pl n top brkv) (mallocBytes vsaLayout H s headroom) rv mv) :
    LocalRun (vsaModel live) roR pathText mRegs (mallocBytes vsaLayout H s headroom)
      (MallocRoomEnd vsaLayout (vsaRoomFast maxReq) H n r s saved k) 1 rv mv := by
  have G := C.geo
  have h96 := C.sp96
  have hle := C.sp.geom.lo; have hhi := C.sp.geom.hi; have hal := C.sp.geom.align
  unfold tohostAddr at hle
  obtain ⟨R80, R88, R8⟩ := C.mtS_reads P
  have frame : ∀ j, j < 96 → mv (s.toNat - 96 + j) = imgM (MtS m1 s headroom mv0 pl n top brkv)
      (s.toNat - 96 + j) := fun j hj => h.img _ (C.frame_owned hj)
  have word : ∀ o, o + 8 ≤ 96 → ∀ v : BitVec 64,
      read64 (MtS m1 s headroom mv0 pl n top brkv) (s.toNat - 96 + o) = some v.toNat →
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
    have hsplit := C.fast.split (n := n.toNat) G.nb16 G.nb32 G.nbP G.n8
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
      rw [C.post_heap P ha']
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

/-- A stage between the split and the epilogue: the stack pointer, the kept
registers and the image after the split. -/
structure StPost (s : BitVec 64) (rv0 : Nat → BitVec 64) (Mt : Mem) (S : Nat → Prop)
    (pc : BitVec 64) (rv : Nat → BitVec 64) (mv : Nat → BitVec 8) : Prop where
  pc : rv VsaIris.PC = pc
  sp : rv 2 = spN s
  keep : KeepS rv rv0
  img : ∀ a, S a → mv a = imgM Mt a

theorem KeepS.step {rv rv' rv0 : Nat → BitVec 64} (h : KeepS rv rv0)
    (hU : ∀ q, q = 9 ∨ q = 18 ∨ q = 19 → rv' q = rv q) : KeepS rv' rv0 :=
  ⟨(hU 9 (.inl rfl)).trans h.s1, (hU 18 (.inr (.inl rfl))).trans h.s2,
    (hU 19 (.inr (.inr rfl))).trans h.s3⟩

/-- Stage 9: at the retarget `ret` after the unlock hook. -/
theorem st9 (C : FastIn live maxReq headroom H n s r saved rv0 mv0 k m1 top brkv chunks bins)
    (P : ProLog s (rv0 8) r pl)
    {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    (h : StPost s rv0 (MtS m1 s headroom mv0 pl n top brkv) (mallocBytes vsaLayout H s headroom)
      0x80006ff8#64 rv mv) (hra : rv 1 = 0x80004c14#64) :
    LocalRun (vsaModel live) roR pathText mRegs (mallocBytes vsaLayout H s headroom)
      (MallocRoomEnd vsaLayout (vsaRoomFast maxReq) H n r s saved k) 2 rv mv := by
  refine seg_step segRel [(1, rv 1)] [] 0x80006ff8#64 [] [] 0 rfl
    (by change ChainOK _ [1] _; decide) (by change KeysOK [1]; decide)
    (by change ∀ x ∈ wrChain segRel, x ∈ [1]; decide) (fun a _ => by show OutL [] a; trivial) C.text
    (fun c _ hcode _ => ret_facts_rel hcode (rv 1) (by rw [hra]; decide))
    (by decide) h.pc (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp; exact .inl ⟨by dsimp only; decide, rfl⟩) (fun p hp => by cases hp) (fun p hp => by cases hp)
    h.img ?_
  intro rv' mv' hpc hL hU hI
  refine st10 C P ⟨?_, ?_, h.keep.step fun q hq => hU q (by rcases hq with rfl | rfl | rfl <;> decide)
    (by rcases hq with rfl | rfl | rfl <;> decide) (not_pin (by rcases hq with rfl | rfl | rfl <;> simp)),
    fun a ha => (hI a ha).trans (by rw [show (segOut segRel [(1, rv 1)] []).log = [] from rfl,
      writeLog_nil'])⟩
  · rw [hpc]
    show Sail.BitVec.update (rv 1 + sign_extend (m := 64) (0#12)) 0 0#1 = _
    rw [hra, ret_tgt _ (by decide)]
  · rw [hU 2 (by decide) (by decide) (not_pin (by simp))]; exact h.sp

/-- Stage 8: at the unlock hook. -/
theorem st8 (C : FastIn live maxReq headroom H n s r saved rv0 mv0 k m1 top brkv chunks bins)
    (P : ProLog s (rv0 8) r pl)
    {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    (h : StPost s rv0 (MtS m1 s headroom mv0 pl n top brkv) (mallocBytes vsaLayout H s headroom)
      0x80005070#64 rv mv) (hra : rv 1 = 0x80004c14#64) :
    LocalRun (vsaModel live) roR pathText mRegs (mallocBytes vsaLayout H s headroom)
      (MallocRoomEnd vsaLayout (vsaRoomFast maxReq) H n r s saved k) 3 rv mv := by
  refine seg_step segUnlock [(10, rv 10), (3, gpV)] [] 0x80005070#64 [] [] 1 rfl
    (by change ChainOK _ [10, 3] _; decide) (by change KeysOK [10, 3]; decide)
    (by change ∀ x ∈ wrChain segUnlock, x ∈ [10, 3]; decide) (fun a _ => by show OutL [] a; trivial)
    C.text (fun c _ hcode _ => unlock_facts hcode (rv 10))
    (by decide) h.pc (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact .inl ⟨by dsimp only; decide, rfl⟩
      · exact .inr ⟨List.mem_singleton.2 rfl, rfl⟩) (fun p hp => by cases hp) (fun p hp => by cases hp)
    h.img ?_
  intro rv' mv' hpc hL hU hI
  have keep := fun q (hq : q = 9 ∨ q = 18 ∨ q = 19 ∨ q = 1 ∨ q = 2) => hU q
    (by rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide)
    (by rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide)
    (not_pin (by rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp))
  refine st9 C P ⟨hpc, (keep 2 (by simp)).trans h.sp,
    h.keep.step fun q hq => keep q (by rcases hq with rfl | rfl | rfl <;> simp),
    fun a ha => (hI a ha).trans (by
      rw [show (segOut segUnlock [(10, rv 10), (3, gpV)] []).log = [] from rfl, writeLog_nil'])⟩
    ((keep 1 (by simp)).trans hra)

/-- Stage 7: at the `jal __malloc_unlock`. -/
theorem st7 (C : FastIn live maxReq headroom H n s r saved rv0 mv0 k m1 top brkv chunks bins)
    (P : ProLog s (rv0 8) r pl)
    {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    (h : StPost s rv0 (MtS m1 s headroom mv0 pl n top brkv) (mallocBytes vsaLayout H s headroom)
      0x80004c10#64 rv mv) :
    LocalRun (vsaModel live) roR pathText mRegs (mallocBytes vsaLayout H s headroom)
      (MallocRoomEnd vsaLayout (vsaRoomFast maxReq) H n r s saved k) 4 rv mv := by
  have hmem : ∀ p ∈ codeFoot 0x80004c10 [0xef#8, 0x00#8, 0x00#8, 0x46#8], (p.1, p.2.2) ∈ pathText := by
    obtain ⟨b0, b1, b2, b3⟩ := jal_bytes_80004c10
    intro p hp
    simp [codeFoot] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact b0
    · exact b1
    · exact b2
    · exact b3
  refine jal_step 0x80004c10 [0xef#8, 0x00#8, 0x00#8, 0x46#8] 0x80005070#64
    (jal_exec_80004c10 live fun p hp => C.text (p.1, p.2.2) (hmem p hp)) hmem (by decide) (by decide)
    h.pc h.img ?_
  · intro rv' mv' hpc hra hU hI
    exact st8 C P ⟨hpc, (hU 2 (by decide) (by decide) (by decide)).trans h.sp,
      h.keep.step fun q hq => hU q (by rcases hq with rfl | rfl | rfl <;> decide)
        (by rcases hq with rfl | rfl | rfl <;> decide) (by rcases hq with rfl | rfl | rfl <;> decide),
      hI⟩ (by rw [show (1 : Nat) = VsaIris.ra from rfl, hra])

/-- The `av` region as loaded owned bytes. -/
abbrev avLD (f : Nat → BitVec 8) : List (Nat × DFrac × BitVec 8) :=
  (List.range 2064).map fun k => (0x8001ad10 + k, DFrac.own 1, f (0x8001ad10 + k))

theorem avLD_pin {f : Nat → BitVec 8} {m : Mem} {L : List (Nat × DFrac × BitVec 8)}
    (h : ∀ p ∈ avLD f ++ L, (m[p.1]?).getD 0 = p.2.2) :
    ∀ a, 0x8001ad10 ≤ a → a < 0x8001b520 → (m[a]?).getD 0 = f a := by
  intro a h1 h2
  have := h (0x8001ad10 + (a - 0x8001ad10), DFrac.own 1, f (0x8001ad10 + (a - 0x8001ad10)))
    (List.mem_append_left _ (List.mem_map_of_mem
      (f := fun k => (0x8001ad10 + k, DFrac.own 1, f (0x8001ad10 + k))) (List.mem_range.2 (by omega))))
  rwa [show 0x8001ad10 + (a - 0x8001ad10) = a by omega] at this

/-- An 8-byte word as written owned bytes at their current values. -/
abbrev wordW (f : Nat → BitVec 8) (a : Nat) : List (Nat × BitVec 8) :=
  (List.range 8).map fun k => (a + k, f (a + k))

theorem mem_wordW {f : Nat → BitVec 8} {a b : Nat} (h1 : a ≤ b) (h2 : b < a + 8) :
    ∃ p ∈ wordW f a, p.1 = b :=
  ⟨(b, f b), by
    refine List.mem_map.2 ⟨b - a, List.mem_range.2 (by omega), ?_⟩
    have e : a + (b - a) = b := by omega
    rw [e], rfl⟩

/-- The split's reflected write log, in clean form. -/
theorem split_log_eq {s a0 s0 a2 a3 a5 t1 : BitVec 64} {f : Nat → BitVec 8} {nb top brkv : Nat}
    (hs : SpGeom s) (ht : SplitTop f top (brkv - top) nb) :
    (segOut segSplit (splitL (spN s) a0 s0 a2 a3 a5 t1 nb) (splitLds f top)).log =
      splitLogN s top nb brkv := by
  have h96 := sp96 hs
  have hhi := hs.hi; have hlo := hs.lo
  have htl := ht.top_lo; have hth := ht.top_hi; have hr := ht.room; have hn16 := ht.nb16
  have hs16 := ht.size_align
  unfold heapStart at htl; unfold heapEnd at hth
  have htopv : (BitVec.ofNat 64 top).toNat = top := ofNat_toNat_lt (by omega)
  have hnbv : (BitVec.ofNat 64 nb).toNat = nb := ofNat_toNat_lt (by omega)
  have hszv : (BitVec.ofNat 64 (brkv - top + 1)).toNat = brkv - top + 1 := ofNat_toNat_lt (by omega)
  simp only [segOut, segSplit, evalBlocks, evalBlock, SegEvalState.init, wlogM, wentryM, widthOfM,
    eaddrM]
  seg_norm
  simp only [splitLds, List.tail_cons, List.nil_append, List.append_nil]
  rw [ht.top_ptr, ht.header]
  have hand : (BitVec.ofNat 64 (brkv - top + 1) &&& sign_extend (m := 64) (0xffc#12)).toNat =
      brkv - top := by rw [and_m4_toNat, hszv]; omega
  have hsub : ((BitVec.ofNat 64 (brkv - top + 1) &&& sign_extend (m := 64) (0xffc#12)) -
      BitVec.ofNat 64 nb).toNat = brkv - top - nb := by
    rw [BitVec.toNat_sub, hand, hnbv]; omega
  have htn : (BitVec.ofNat 64 top + BitVec.ofNat 64 nb).toNat = top + nb := by
    rw [BitVec.toNat_add, htopv, hnbv, Nat.mod_eq_of_lt (by omega)]
  have e1 : (BitVec.ofNat 64 top + sign_extend (m := 64) (0x008#12)).toNat = top + 8 := by
    rw [add_imm _ _ 8 (by decide) (by omega), htopv]
  have v1 : BitVec.ofNat 64 nb ||| sign_extend (m := 64) (0x001#12) = BitVec.ofNat 64 (nb + 1) := by
    rw [or_one_even _ (by rw [hnbv]; omega)]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hnbv, ofNat_toNat_lt (by omega)]
    simp only [BitVec.toNat_ofNat]
  have e2 : (spN s + sign_extend (m := 64) (0x008#12)).toNat = s.toNat - 96 + 8 := by
    rw [add_imm _ _ 8 (by decide) (by rw [h96]; omega), h96]
  have e3 : (0x8001ad10#64 + sign_extend (m := 64) (0x010#12)).toNat = topAddr := by decide
  have v3 : BitVec.ofNat 64 top + BitVec.ofNat 64 nb = BitVec.ofNat 64 (top + nb) := by
    apply BitVec.eq_of_toNat_eq; rw [htn, ofNat_toNat_lt (by omega)]
  have e4 : (BitVec.ofNat 64 top + BitVec.ofNat 64 nb + sign_extend (m := 64) (0x008#12)).toNat =
      top + nb + 8 := by
    rw [add_imm _ _ 8 (by decide) (by rw [htn]; omega), htn]
  have v4 : (BitVec.ofNat 64 (brkv - top + 1) &&& sign_extend (m := 64) (0xffc#12)) -
      BitVec.ofNat 64 nb ||| sign_extend (m := 64) (0x001#12) = BitVec.ofNat 64 (brkv - top - nb + 1) := by
    rw [or_one_even _ (by rw [hsub]; omega)]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hsub, ofNat_toNat_lt (by omega)]
    simp only [BitVec.toNat_ofNat]
  rw [e1, v1, e2, e3, e4, v4, v3]

/-- The top chunk's header word as loaded owned bytes. -/
abbrev hdrLD (f : Nat → BitVec 8) (top : Nat) : List (Nat × DFrac × BitVec 8) :=
  (List.range 8).map fun k => (top + 8 + k, DFrac.own 1, f (top + 8 + k))

/-- Stage 6: the index-free part of the path, at the top-size tests. -/
structure St6 (s : BitVec 64) (rv0 : Nat → BitVec 64) (Mt : Mem) (S : Nat → Prop) (nb : Nat)
    (rv : Nat → BitVec 64) (mv : Nat → BitVec 8) : Prop where
  pc : rv VsaIris.PC = 0x80004a2c#64
  sp : rv 2 = spN s
  a4 : rv 14 = BitVec.ofNat 64 nb
  a6 : rv 16 = 0x8001ad10#64
  keep : KeepS rv rv0
  img : ∀ a, S a → mv a = imgM Mt a

theorem st6 (C : FastIn live maxReq headroom H n s r saved rv0 mv0 k m1 top brkv chunks bins)
    (P : ProLog s (rv0 8) r pl)
    {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    (h : St6 s rv0 (MtP m1 s headroom mv0 pl) (mallocBytes vsaLayout H s headroom) (nbN n) rv mv) :
    LocalRun (vsaModel live) roR pathText mRegs (mallocBytes vsaLayout H s headroom)
      (MallocRoomEnd vsaLayout (vsaRoomFast maxReq) H n r s saved k) 5 rv mv := by
  have G := C.geo
  have h96 := C.sp96
  have hle := C.sp.geom.lo; have hhi := C.sp.geom.hi; have hal := C.sp.geom.align
  unfold tohostAddr at hle
  have R := C.fast.reads (Nat.succ_pos k)
  have hglobS : ∀ a, 0x8001ad10 ≤ a → a < 0x8001b520 → mallocBytes vsaLayout H s headroom a :=
    fun a h1 h2 => .inr (.inl (.inl ⟨h1, h2⟩))
  have hglobH : ∀ a, 0x8001ad10 ≤ a → a < 0x8001b520 → heapFoot vsaLayout H a :=
    fun a h1 h2 => .inl (.inl ⟨h1, h2⟩)
  have ht : SplitTop mv top (brkv - top) (nbN n) :=
    { top_ptr := word_val (Mt := MtP m1 s headroom mv0 pl)
        (fun j hj => h.img _ (hglobS _ (by unfold topAddr avAddr; omega) (by unfold topAddr avAddr; omega)))
        (by rw [C.mtP_read P (fun j hj => hglobH _ (by unfold topAddr avAddr; omega)
          (by unfold topAddr avAddr; omega)), R.top_ptr,
          ofNat_toNat_lt (by have := G.top_hi; have := G.top_le; unfold heapEnd at *; omega)])
      header := word_val (Mt := MtP m1 s headroom mv0 pl)
        (fun j hj => h.img _ (.inr (C.split_foot hj).1))
        (by rw [C.mtP_read P (fun j hj => (C.split_foot hj).1), R.top_header,
          ofNat_toNat_lt (by have := G.top_hi; have := G.top_le; unfold heapEnd at *; omega)])
      top_lo := G.top_lo
      top_hi := by have := G.top_hi; have := G.top_le; omega
      top_align := G.top16
      size_align := G.size16
      room := G.room
      nb16 := G.nb16
      nb32 := G.nb32 }
  refine seg_step segSplit (splitL (spN s) (rv 10) (rv 8) (rv 12) (rv 13) (rv 15) (rv 6) (nbN n))
    (splitLds mv top) 0x80004a2c#64 (avLD mv ++ hdrLD mv top)
    (wordW mv (top + 8) ++ wordW mv (s.toNat - 96 + 8) ++ wordW mv topAddr ++
      wordW mv (top + nbN n + 8)) 14 rfl
    (by change ChainOK _ [2, 10, 8, 12, 13, 14, 15, 16, 6] _; decide)
    (by change KeysOK [2, 10, 8, 12, 13, 14, 15, 16, 6]; decide)
    (by change ∀ x ∈ wrChain segSplit, x ∈ [2, 10, 8, 12, 13, 14, 15, 16, 6]; decide) ?_ C.text
    (fun c _ hcode hLD => split_facts hcode (by rw [h96]; unfold tohostAddr; omega)
      (by rw [h96]; omega) (by rw [h96]; omega) (avLD_pin hLD) (fun j hj => by
        have := hLD (top + 8 + j, DFrac.own 1, mv (top + 8 + j)) (List.mem_append_right _
          (List.mem_map_of_mem (f := fun k => (top + 8 + k, DFrac.own 1, mv (top + 8 + k)))
            (List.mem_range.2 hj)))
        exact this) ht)
    (by decide) h.pc ?_ ?_ ?_ h.img ?_
  · intro a ha
    rw [split_log_eq C.sp.geom ht]
    have cw : ∀ b, (∀ p ∈ wordW mv b, p ∈ wordW mv (top + 8) ++ wordW mv (s.toNat - 96 + 8) ++
        wordW mv topAddr ++ wordW mv (top + nbN n + 8)) → a < b ∨ b + 8 ≤ a := fun b hb => by
      refine Classical.byContradiction fun hc => ?_
      obtain ⟨p, hp, hpa⟩ := mem_wordW (f := mv) (a := b) (b := a) (by omega) (by omega)
      exact ha p (hb p hp) hpa
    simp only [splitLogN, OutL]
    refine ⟨cw _ fun p hp => ?_, cw _ fun p hp => ?_, cw _ fun p hp => ?_, cw _ fun p hp => ?_, trivial⟩
    · simp only [List.mem_append]; exact .inl (.inl (.inl hp))
    · simp only [List.mem_append]; exact .inl (.inl (.inr hp))
    · simp only [List.mem_append]; exact .inl (.inr hp)
    · simp only [List.mem_append]; exact .inr hp
  · intro p hp
    simp only [splitL, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact .inl ⟨by dsimp only; decide, h.sp⟩
    · exact .inl ⟨by dsimp only; decide, rfl⟩
    · exact .inl ⟨by dsimp only; decide, rfl⟩
    · exact .inl ⟨by dsimp only; decide, rfl⟩
    · exact .inl ⟨by dsimp only; decide, rfl⟩
    · exact .inl ⟨by dsimp only; decide, h.a4⟩
    · exact .inl ⟨by dsimp only; decide, rfl⟩
    · exact .inl ⟨by dsimp only; decide, h.a6⟩
    · exact .inl ⟨by dsimp only; decide, rfl⟩
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
      rw [List.mem_range] at hj
      exact ⟨hglobS _ (by omega) (by omega), rfl⟩
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
      rw [List.mem_range] at hj
      exact ⟨.inr (C.split_foot hj).1, rfl⟩
  · intro p hp
    simp only [List.mem_append] at hp
    rcases hp with ((hp | hp) | hp) | hp <;>
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
      rw [List.mem_range] at hj
      refine ⟨?_, rfl⟩
      first
        | exact .inr (C.split_foot hj).1
        | exact C.frame_owned (j := 8 + j) (by omega) |>.imp id id |> fun h' => by
            rw [show s.toNat - 96 + 8 + j = s.toNat - 96 + (8 + j) by omega]; exact h'
        | exact .inr (C.split_foot hj).2.1
        | exact .inr (C.split_foot hj).2.2
  · intro rv' mv' hpc hL hU hI
    refine st7 C P ⟨hpc, ?_, h.keep.step fun q hq => hU q ?_ ?_ ?_, fun a ha => ?_⟩
    · exact (hL (2, spN s) (by simp [splitL])).trans rfl
    · rcases hq with rfl | rfl | rfl <;> decide
    · rcases hq with rfl | rfl | rfl <;> decide
    · exact not_pin (by rcases hq with rfl | rfl | rfl <;> simp [splitL])
    · rw [hI a ha, split_log_eq C.sp.geom ht]

theorem bins_a4 (sp a0 a1 a2 a3 a4 a5 a6 a7 t4 : BitVec 64) (f : Nat → BitVec 8) (nb : Nat) :
    finReg segBins (binsL sp a0 a1 a2 a3 a4 a5 a6 a7 t4) (binsLds f sp nb) 14 =
      bytesVal .ld (wordOf f (sp.toNat + 8)) := by
  simp only [finReg, segOut, segBins, evalBlocks_regs, runChain, SegEvalState.init]
  seg_norm

theorem bins_a6 (sp a0 a1 a2 a3 a4 a5 a6 a7 t4 : BitVec 64) (f : Nat → BitVec 8) (nb : Nat) :
    finReg segBins (binsL sp a0 a1 a2 a3 a4 a5 a6 a7 t4) (binsLds f sp nb) 16 = 0x8001ad10#64 := by
  simp only [finReg, segOut, segBins, evalBlocks_regs, runChain, SegEvalState.init]
  seg_norm
  decide

theorem bins_sp (sp a0 a1 a2 a3 a4 a5 a6 a7 t4 : BitVec 64) (f : Nat → BitVec 8) (nb : Nat) :
    finReg segBins (binsL sp a0 a1 a2 a3 a4 a5 a6 a7 t4) (binsLds f sp nb) 2 = sp := by
  simp only [finReg, segOut, segBins, evalBlocks_regs, runChain, SegEvalState.init]
  seg_norm

/-- The empty-bin words the bin checks read, from the image after any prologue. -/
theorem FastIn.binsImg (C : FastIn live maxReq headroom H n s r saved rv0 mv0 k m1 top brkv chunks bins)
    {s0v : BitVec 64} (P : ProLog s s0v r pl) {mv : Nat → BitVec 8}
    (himg : ∀ a, mallocBytes vsaLayout H s headroom a → mv a = imgM (MtP m1 s headroom mv0 pl) a) :
    BinsImg mv := by
  have R := C.fast.reads (Nat.succ_pos k)
  have gword : ∀ a v, 0x8001ad10 ≤ a → a + 8 ≤ 0x8001b520 → v < 2 ^ 64 → read64 m1 a = some v →
      bytesVal .ld (wordOf mv a) = BitVec.ofNat 64 v := fun a v h1 h2 hv hr =>
    word_val (Mt := MtP m1 s headroom mv0 pl)
      (fun j hj => himg _ (.inr (.inl (.inl ⟨by omega, by omega⟩))))
      (by rw [C.mtP_read P (fun j hj => .inl (.inl ⟨by omega, by omega⟩)), hr, ofNat_toNat_lt hv])
  exact
    { bk := fun i h0 h1 => gword _ _ (by unfold binAt avAddr; omega)
        (by unfold binAt avAddr; omega)
        (by unfold binAt avAddr; omega) (R.bin_bk i h0 h1)
      fd1 := gword _ _ (by decide) (by decide) (by decide) (R.bin_fd 1 (by decide) (by decide))
      binblocks := gword _ _ (by decide) (by decide) (by decide) R.binblocks }

/-- Stage 5: back from the lock hook, at the bin checks (requests 24..`maxReq`). -/
theorem st5 (C : FastIn live maxReq headroom H n s r saved rv0 mv0 k m1 top brkv chunks bins)
    (hA : 24 ≤ n.toNat) {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    (h : StPost s rv0 (MtP m1 s headroom mv0 (proLogN s (rv0 8) r n)) (mallocBytes vsaLayout H s headroom)
      0x80004878#64 rv mv) :
    LocalRun (vsaModel live) roR pathText mRegs (mallocBytes vsaLayout H s headroom)
      (MallocRoomEnd vsaLayout (vsaRoomFast maxReq) H n r s saved k) 6 rv mv := by
  have G := C.geo
  have h96 := C.sp96
  have hle := C.sp.geom.lo; have hhi := C.sp.geom.hi
  unfold tohostAddr at hle
  have hglobS : ∀ a, 0x8001ad10 ≤ a → a < 0x8001b520 → mallocBytes vsaLayout H s headroom a :=
    fun a h1 h2 => .inr (.inl (.inl ⟨h1, h2⟩))
  have hb := C.binsImg (proLog_A C.sp.geom (rv0 8) r n) h.img
  have hv1 : bytesVal .ld (wordOf mv ((spN s).toNat + 8)) = BitVec.ofNat 64 (nbN n) := by
    rw [h96]
    refine word_val (Mt := MtP m1 s headroom mv0 (proLogN s (rv0 8) r n))
      (fun j hj => by rw [Nat.add_assoc]; exact h.img _ (C.frame_owned (j := 8 + j) (by omega))) ?_
    have e : (n.toNat + 23) / 16 * 16 = nbN n := (Nat.max_eq_right (by omega)).symm
    rw [read64_of_writeLog_at _ _ 2 _ (nbOf n) rfl (by simp only [List.drop, OutLRange]),
      nbOf_toNat (Nat.le_trans C.n_hi C.max), e, ofNat_toNat_lt (by have := G.nb496; omega)]
  refine seg_step segBins (binsL (spN s) (rv 10) (rv 11) (rv 12) (rv 13) (rv 14) (rv 15) (rv 16)
      (rv 17) (rv 29)) (binsLds mv (spN s) (nbN n)) 0x80004878#64 (avLD mv ++ frameLD mv (spN s)) []
    26 rfl (by change ChainOK _ [2, 10, 11, 12, 13, 14, 15, 16, 17, 29] _; decide)
    (by change KeysOK [2, 10, 11, 12, 13, 14, 15, 16, 17, 29]; decide)
    (by change ∀ x ∈ wrChain segBins, x ∈ [2, 10, 11, 12, 13, 14, 15, 16, 17, 29]; decide)
    (fun a _ => by show OutL [] a; trivial) C.text
    (fun c _ hcode hLD => bins_facts hcode (by rw [h96]; unfold tohostAddr; omega)
      (by rw [h96]; omega) (frameLD_pin fun p hp => hLD p (List.mem_append_right _ hp))
      (avLD_pin hLD) (mem_sizeClasses G.nb16 G.nb32 G.nb496) hv1 hb)
    (by decide) h.pc ?_ ?_ (fun p hp => by cases hp) h.img ?_
  · intro p hp
    simp only [binsL, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact .inl ⟨by dsimp only; decide, h.sp⟩
    all_goals exact .inl ⟨by dsimp only; decide, rfl⟩
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
      rw [List.mem_range] at hj
      exact ⟨hglobS _ (by omega) (by omega), rfl⟩
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
      rw [List.mem_range] at hj
      refine ⟨?_, rfl⟩
      rw [h96]; exact C.frame_owned hj
  · intro rv' mv' hpc hL hU hI
    refine st6 C (proLog_A C.sp.geom (rv0 8) r n) ⟨hpc, ?_, ?_, ?_, h.keep.step fun q hq => hU q ?_ ?_ ?_, fun a ha => ?_⟩
    · rw [hL (2, spN s) (by simp [binsL]), bins_sp]
    · rw [hL (14, rv 14) (by simp [binsL]), bins_a4, hv1]
    · rw [hL (16, rv 16) (by simp [binsL]), bins_a6]
    · rcases hq with rfl | rfl | rfl <;> decide
    · rcases hq with rfl | rfl | rfl <;> decide
    · exact not_pin (by rcases hq with rfl | rfl | rfl <;> simp [binsL])
    · rw [hI a ha, show (segOut segBins (binsL (spN s) (rv 10) (rv 11) (rv 12) (rv 13) (rv 14) (rv 15)
        (rv 16) (rv 17) (rv 29)) (binsLds mv (spN s) (nbN n))).log = [] from rfl, writeLog_nil']

/-- The lock hook and its retarget `ret`, back to `ret`. -/
theorem lock_hook {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {S : Nat → Prop} {Mt : Mem}
    {N : Nat} (htext : ∀ p ∈ pathText, live p.1) {ret : BitVec 64} (hret : ret.toNat % 4 = 0)
    {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    (hk : ∀ rv' mv', StPost s rv0 Mt S ret rv' mv' →
      LocalRun (vsaModel live) roR pathText mRegs S Q N rv' mv')
    (h : StPost s rv0 Mt S 0x80005068#64 rv mv) (hra : rv 1 = ret) :
    LocalRun (vsaModel live) roR pathText mRegs S Q (N + 2) rv mv := by
  refine seg_step segLock [(10, rv 10), (3, gpV)] [] 0x80005068#64 [] [] 1 rfl
    (by change ChainOK _ [10, 3] _; decide) (by change KeysOK [10, 3]; decide)
    (by change ∀ x ∈ wrChain segLock, x ∈ [10, 3]; decide) (fun a _ => by show OutL [] a; trivial)
    htext (fun c _ hcode _ => lock_facts hcode (rv 10))
    (by decide) h.pc (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact .inl ⟨by dsimp only; decide, rfl⟩
      · exact .inr ⟨List.mem_singleton.2 rfl, rfl⟩) (fun p hp => by cases hp) (fun p hp => by cases hp)
    h.img ?_
  intro rv1 mv1 hpc1 _ hU1 hI1
  have keep := fun q (hq : q = 9 ∨ q = 18 ∨ q = 19 ∨ q = 1 ∨ q = 2) => hU1 q
    (by rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide)
    (by rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide)
    (not_pin (by rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp))
  have hra1 : rv1 1 = ret := (keep 1 (by simp)).trans hra
  refine seg_step segAcq [(1, rv1 1)] [] 0x80006fe0#64 [] [] 0 rfl
    (by change ChainOK _ [1] _; decide) (by change KeysOK [1]; decide)
    (by change ∀ x ∈ wrChain segAcq, x ∈ [1]; decide) (fun a _ => by show OutL [] a; trivial) htext
    (fun c _ hcode _ => ret_facts_acq hcode (rv1 1) (by rw [hra1]; exact hret))
    (by decide) hpc1 (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp; exact .inl ⟨by dsimp only; decide, rfl⟩) (fun p hp => by cases hp) (fun p hp => by cases hp)
    (fun a ha => (hI1 a ha).trans (by
      rw [show (segOut segLock [(10, rv 10), (3, gpV)] []).log = [] from rfl, writeLog_nil'])) ?_
  intro rv' mv' hpc hL hU hI
  refine hk rv' mv' ⟨?_, ?_, (h.keep.step fun q hq => keep q (by rcases hq with rfl | rfl | rfl <;> simp)).step
    fun q hq => hU q (by rcases hq with rfl | rfl | rfl <;> decide)
      (by rcases hq with rfl | rfl | rfl <;> decide) (not_pin (by rcases hq with rfl | rfl | rfl <;> simp)),
    fun a ha => (hI a ha).trans (by rw [show (segOut segAcq [(1, rv1 1)] []).log = [] from rfl,
      writeLog_nil'])⟩
  · rw [hpc]
    show Sail.BitVec.update (rv1 1 + sign_extend (m := 64) (0#12)) 0 0#1 = _
    rw [hra1, ret_tgt _ hret]
  · rw [hU 2 (by decide) (by decide) (not_pin (by simp)), keep 2 (by simp)]; exact h.sp

/-- A `jal __malloc_lock` site, the hook, and its return. -/
theorem lock_call {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {S : Nat → Prop} {Mt : Mem}
    {N : Nat} (htext : ∀ p ∈ pathText, live p.1) (i : Nat) (code : List (BitVec 8))
    (hexec : JalExec (vsaModel live) i code 0x80005068#64)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ pathText)
    (hret : (BitVec.ofNat 64 (i + 4)).toNat % 4 = 0)
    {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    (hk : ∀ rv' mv', StPost s rv0 Mt S (BitVec.ofNat 64 (i + 4)) rv' mv' →
      LocalRun (vsaModel live) roR pathText mRegs S Q N rv' mv')
    (h : StPost s rv0 Mt S (BitVec.ofNat 64 i) rv mv) :
    LocalRun (vsaModel live) roR pathText mRegs S Q (N + 3) rv mv := by
  refine jal_step i code 0x80005068#64 hexec hcode (by decide) (by decide) h.pc h.img ?_
  intro rv' mv' hpc hra hU hI
  exact lock_hook htext hret hk ⟨hpc, (hU 2 (by decide) (by decide) (by decide)).trans h.sp,
      h.keep.step fun q hq => hU q (by rcases hq with rfl | rfl | rfl <;> decide)
        (by rcases hq with rfl | rfl | rfl <;> decide) (by rcases hq with rfl | rfl | rfl <;> decide),
      hI⟩ hra

/-- The code bytes of a `jal` site, from its generated membership facts. -/
theorem jal_code {i : Nat} {b0 b1 b2 b3 : BitVec 8}
    (h : (i, b0) ∈ pathText ∧ (i + 1, b1) ∈ pathText ∧ (i + 2, b2) ∈ pathText ∧ (i + 3, b3) ∈ pathText) :
    ∀ p ∈ codeFoot i [b0, b1, b2, b3], (p.1, p.2.2) ∈ pathText := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  intro p hp
  simp [codeFoot] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-- Stage 2: at the `jal __malloc_lock` of requests 24..`maxReq`. -/
theorem st2 (C : FastIn live maxReq headroom H n s r saved rv0 mv0 k m1 top brkv chunks bins)
    (hA : 24 ≤ n.toNat) {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    (h : StPost s rv0 (MtP m1 s headroom mv0 (proLogN s (rv0 8) r n)) (mallocBytes vsaLayout H s headroom)
      0x80004874#64 rv mv) :
    LocalRun (vsaModel live) roR pathText mRegs (mallocBytes vsaLayout H s headroom)
      (MallocRoomEnd vsaLayout (vsaRoomFast maxReq) H n r s saved k) 9 rv mv :=
  lock_call C.text 0x80004874 _ (jal_exec_80004874 live fun p hp => C.text (p.1, p.2.2)
    (jal_code jal_bytes_80004874 p hp)) (jal_code jal_bytes_80004874) (by decide)
    (fun _ _ h' => st5 C hA h') h

/-- The prologue's reflected write log, in clean form. -/
theorem pro_log {s s0 r n a0 a4 a5 : BitVec 64} (hs : SpGeom s) :
    (segOut segPro (proL s s0 r n a0 a4 a5) []).log = proLogN s s0 r n := by
  have h96 := sp96 hs
  have := hs.hi
  simp only [segOut, segPro, evalBlocks, evalBlock, SegEvalState.init, wlogM, wentryM, widthOfM,
    eaddrM]
  seg_norm
  simp only [List.nil_append, List.cons_append, List.append_nil]
  have e := fun (imm : BitVec 12) (c : Nat) (hc : (sign_extend (m := 64) imm : BitVec 64).toNat = c)
      (hcl : c ≤ 96) => add_imm (s + sign_extend (m := 64) (0xfa0#12)) imm c hc (by rw [h96]; omega)
  rw [e (0x050#12) 80 (by decide) (by omega), e (0x058#12) 88 (by decide) (by omega),
    e (0x008#12) 8 (by decide) (by omega), h96]

theorem pro_sp (s s0 r n a0 a4 a5 : BitVec 64) :
    finReg segPro (proL s s0 r n a0 a4 a5) [] 2 = spN s := by
  simp only [finReg, segOut, segPro, evalBlocks_regs, runChain, SegEvalState.init]
  seg_norm

/-- Stage 1: in `_malloc_r`, at the prologue. -/
structure St1 (s r n : BitVec 64) (rv0 : Nat → BitVec 64) (Mt : Mem) (S : Nat → Prop)
    (rv : Nat → BitVec 64) (mv : Nat → BitVec 8) : Prop where
  pc : rv VsaIris.PC = 0x800047a8#64
  sp : rv 2 = s
  ra : rv 1 = r
  a1 : rv 11 = n
  s0 : rv 8 = rv0 8
  keep : KeepS rv rv0
  img : ∀ a, S a → mv a = imgM Mt a

theorem st1 (C : FastIn live maxReq headroom H n s r saved rv0 mv0 k m1 top brkv chunks bins)
    (hA : 24 ≤ n.toNat) {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    (h : St1 s r n rv0 (Mt0 m1 s headroom mv0) (mallocBytes vsaLayout H s headroom) rv mv) :
    LocalRun (vsaModel live) roR pathText mRegs (mallocBytes vsaLayout H s headroom)
      (MallocRoomEnd vsaLayout (vsaRoomFast maxReq) H n r s saved k) 10 rv mv := by
  have h96 := C.sp96
  have hle := C.sp.geom.lo; have hhi := C.sp.geom.hi
  unfold tohostAddr at hle
  refine seg_step segPro (proL s (rv 8) (rv 1) (rv 11) (rv 10) (rv 14) (rv 15)) [] 0x800047a8#64 []
    (wordW mv (s.toNat - 96 + 80) ++ wordW mv (s.toNat - 96 + 88) ++ wordW mv (s.toNat - 96 + 8)) 12 rfl
    (by change ChainOK _ [2, 8, 1, 11, 10, 14, 15] _; decide)
    (by change KeysOK [2, 8, 1, 11, 10, 14, 15]; decide)
    (by change ∀ x ∈ wrChain segPro, x ∈ [2, 8, 1, 11, 10, 14, 15]; decide) ?_ C.text
    (fun c _ hcode _ => pro_facts hcode C.sp.geom (h.a1 ▸ hA) (h.a1 ▸ Nat.le_trans C.n_hi C.max))
    (by decide) h.pc ?_ (fun p hp => by cases hp) ?_ h.img ?_
  · intro a ha
    rw [pro_log C.sp.geom]
    have cw : ∀ b, (∀ p ∈ wordW mv b, p ∈ wordW mv (s.toNat - 96 + 80) ++
        wordW mv (s.toNat - 96 + 88) ++ wordW mv (s.toNat - 96 + 8)) → a < b ∨ b + 8 ≤ a := fun b hb => by
      refine Classical.byContradiction fun hc => ?_
      obtain ⟨p, hp, hpa⟩ := mem_wordW (f := mv) (a := b) (b := a) (by omega) (by omega)
      exact ha p (hb p hp) hpa
    simp only [proLogN, OutL]
    refine ⟨cw _ fun p hp => ?_, cw _ fun p hp => ?_, cw _ fun p hp => ?_, trivial⟩
    · simp only [List.mem_append]; exact .inl (.inl hp)
    · simp only [List.mem_append]; exact .inl (.inr hp)
    · simp only [List.mem_append]; exact .inr hp
  · intro p hp
    simp only [proL, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact .inl ⟨by dsimp only; decide, h.sp⟩
    all_goals exact .inl ⟨by dsimp only; decide, rfl⟩
  · intro p hp
    simp only [List.mem_append] at hp
    have hw : ∀ o, o + 8 ≤ 96 → ∀ p ∈ wordW mv (s.toNat - 96 + o),
        mallocBytes vsaLayout H s headroom p.1 ∧ mv p.1 = p.2 := fun o ho p hp => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
      rw [List.mem_range] at hj
      refine ⟨?_, rfl⟩
      rw [Nat.add_assoc]; exact C.frame_owned (j := o + j) (by omega)
    rcases hp with (hp | hp) | hp
    · exact hw 80 (by omega) p hp
    · exact hw 88 (by omega) p hp
    · exact hw 8 (by omega) p hp
  · intro rv' mv' hpc hL hU hI
    refine st2 C hA ⟨hpc, ?_, h.keep.step fun q hq => hU q ?_ ?_ ?_, fun a ha => ?_⟩
    · rw [hL (2, s) (by simp [proL]), pro_sp]
    · rcases hq with rfl | rfl | rfl <;> decide
    · rcases hq with rfl | rfl | rfl <;> decide
    · exact not_pin (by rcases hq with rfl | rfl | rfl <;> simp [proL])
    · rw [hI a ha, pro_log C.sp.geom, h.s0, h.ra, h.a1]

theorem wrap_a1 (n a1 : BitVec 64) : finReg segWrap (wrapL n a1) [impW] 11 = n := by
  simp only [finReg, segOut, segWrap, evalBlocks_regs, runChain, SegEvalState.init]
  seg_norm
  rw [show (sign_extend (m := 64) (0#12) : BitVec 64) = 0#64 by decide, BitVec.add_zero]

/-- Stage 0: at `malloc`, the entry. -/
theorem st0 (C : FastIn live maxReq headroom H n s r saved rv0 mv0 k m1 top brkv chunks bins)
    {mv : Nat → BitVec 8}
    (k1 : ∀ {rv mv}, St1 s r n rv0 (Mt0 m1 s headroom mv0) (mallocBytes vsaLayout H s headroom) rv mv →
      LocalRun (vsaModel live) roR pathText mRegs (mallocBytes vsaLayout H s headroom)
        (MallocRoomEnd vsaLayout (vsaRoomFast maxReq) H n r s saved k) 10 rv mv)
    (himg : ∀ a, mallocBytes vsaLayout H s headroom a → mv a = imgM (Mt0 m1 s headroom mv0) a) :
    LocalRun (vsaModel live) roR pathText mRegs (mallocBytes vsaLayout H s headroom)
      (MallocRoomEnd vsaLayout (vsaRoomFast maxReq) H n r s saved k) 11 rv0 mv := by
  have E := C.entry
  refine seg_step segWrap (wrapL (rv0 10) (rv0 11)) [impW] 0x80004790#64 [] [] 2 rfl
    (by change ChainOK _ [10, 11, 3] _; decide) (by change KeysOK [10, 11, 3]; decide)
    (by change ∀ x ∈ wrChain segWrap, x ∈ [10, 11, 3]; decide) (fun a _ => by show OutL [] a; trivial)
    C.text (fun c _ hcode _ => wrap_facts hcode (rv0 10) (rv0 11))
    (by decide) E.pc (fun p hp => by
      simp only [wrapL, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact .inl ⟨by dsimp only; decide, rfl⟩
      · exact .inl ⟨by dsimp only; decide, rfl⟩
      · exact .inr ⟨List.mem_singleton.2 rfl, rfl⟩) (fun p hp => by cases hp) (fun p hp => by cases hp)
    himg ?_
  intro rv' mv' hpc hL hU hI
  have keep := fun q (hq : q = 9 ∨ q = 18 ∨ q = 19 ∨ q = 1 ∨ q = 2 ∨ q = 8) => hU q
    (by rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (not_pin (by rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [wrapL]))
  refine k1 ⟨hpc, (keep 2 (by simp)).trans E.sp, (keep 1 (by simp)).trans E.ra, ?_,
    keep 8 (by simp), ⟨keep 9 (by simp), keep 18 (by simp), keep 19 (by simp)⟩,
    fun a ha => (hI a ha).trans (by
      rw [show (segOut segWrap (wrapL (rv0 10) (rv0 11)) [impW]).log = [] from rfl, writeLog_nil'])⟩
  rw [hL (11, rv0 11) (by simp [wrapL]), wrap_a1]
  exact E.a0

end Stages

end VsaIris.MallocFast
