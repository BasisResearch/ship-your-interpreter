import Std.Data.ExtHashMap

/-!
# Code and data images as byte functions over address ranges

A text (the byte footprint a proof reads as code or constant data) is described by
`TextPiece`s: a byte function of the loaded image plus the half-open address ranges
where the piece is claimed. `piecesText` materialises the footprint as the
`List (Nat × BitVec 8)` the machine layer consumes; every membership fact is one
application of `mem_piecesText` to a Boolean check (`piecesHasB`, `bytesHasB`) that
`decide` evaluates at a literal address. Nothing here depends on a particular binary:
the byte functions and ranges are parameters.
-/

open Std (ExtHashMap)

namespace Vsa.Sim

/-- A byte function of a loaded image, claimed on the listed half-open ranges. -/
structure TextPiece where
  img : Nat → BitVec 8
  ranges : List (Nat × Nat)

/-- Membership of an address in a list of half-open ranges. -/
def inRangesB (rs : List (Nat × Nat)) (a : Nat) : Bool :=
  rs.any fun r => decide (r.1 ≤ a) && decide (a < r.2)

/-- The `(address, byte)` footprint of `img` on the ranges `rs`. -/
def rangeText (img : Nat → BitVec 8) (rs : List (Nat × Nat)) : List (Nat × BitVec 8) :=
  rs.flatMap fun r => (List.range (r.2 - r.1)).map fun k => (r.1 + k, img (r.1 + k))

/-- The footprint of a list of pieces. -/
@[irreducible] def piecesText (ps : List TextPiece) : List (Nat × BitVec 8) :=
  ps.flatMap fun p => rangeText p.img p.ranges

/-- Some piece claims address `a` with byte `b`. -/
def piecesHasB (ps : List TextPiece) (a : Nat) (b : BitVec 8) : Bool :=
  ps.any fun p => inRangesB p.ranges a && p.img a == b

/-- Consecutive bytes `bs` starting at `a` are all claimed. -/
def bytesHasB (ps : List TextPiece) (a : Nat) (bs : List (BitVec 8)) : Bool :=
  bs.zipIdx.all fun q => piecesHasB ps (a + q.2) q.1

/-- Every range of `rs` lies in `[lo, hi)`. -/
def rangesWithinB (rs : List (Nat × Nat)) (lo hi : Nat) : Bool :=
  rs.all fun r => decide (lo ≤ r.1) && decide (r.2 ≤ hi)

theorem inRangesB_iff {rs : List (Nat × Nat)} {a : Nat} :
    inRangesB rs a = true ↔ ∃ r ∈ rs, r.1 ≤ a ∧ a < r.2 := by
  simp [inRangesB]

theorem mem_rangeText_iff {img : Nat → BitVec 8} {rs : List (Nat × Nat)} {p : Nat × BitVec 8} :
    p ∈ rangeText img rs ↔ inRangesB rs p.1 = true ∧ p.2 = img p.1 := by
  rw [inRangesB_iff]
  constructor
  · intro h
    obtain ⟨r, hr, hp⟩ := List.mem_flatMap.1 h
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hp
    exact ⟨⟨r, hr, by omega, by have := List.mem_range.1 hk; omega⟩, rfl⟩
  · rintro ⟨⟨r, hr, h1, h2⟩, he⟩
    obtain ⟨a, b⟩ := p
    simp only at he h1 h2
    subst he
    refine List.mem_flatMap.2 ⟨r, hr, List.mem_map.2 ⟨a - r.1, List.mem_range.2 (by omega), ?_⟩⟩
    rw [show r.1 + (a - r.1) = a by omega]

theorem mem_piecesText_iff {ps : List TextPiece} {p : Nat × BitVec 8} :
    p ∈ piecesText ps ↔ ∃ q ∈ ps, inRangesB q.ranges p.1 = true ∧ p.2 = q.img p.1 := by
  unfold piecesText
  simp only [List.mem_flatMap, mem_rangeText_iff]

theorem mem_piecesText {ps : List TextPiece} {a : Nat} {b : BitVec 8}
    (h : piecesHasB ps a b = true) : (a, b) ∈ piecesText ps := by
  obtain ⟨q, hq, h⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact mem_piecesText_iff.2 ⟨q, hq, h.1, h.2.symm⟩

theorem piecesHasB_of_bytes {ps : List TextPiece} {a : Nat} {bs : List (BitVec 8)}
    (h : bytesHasB ps a bs = true) {b : BitVec 8} {k : Nat} (hk : (b, k) ∈ bs.zipIdx) :
    piecesHasB ps (a + k) b = true :=
  List.all_eq_true.1 h (b, k) hk

theorem bytesHasB_get {ps : List TextPiece} {a : Nat} {bs : List (BitVec 8)}
    (h : bytesHasB ps a bs = true) (k : Nat) (hk : k < bs.length) :
    piecesHasB ps (a + k) bs[k] = true :=
  piecesHasB_of_bytes h (List.mem_zipIdx_iff_getElem?.2 (by simp [hk]))

/-- Every byte of a piece footprint satisfies `P`, given `P` on each piece's ranges. -/
theorem forall_piecesText {ps : List TextPiece} {P : Nat → BitVec 8 → Prop}
    (h : ∀ q ∈ ps, ∀ a, inRangesB q.ranges a = true → P a (q.img a)) :
    ∀ p ∈ piecesText ps, P p.1 p.2 := by
  intro p hp
  obtain ⟨q, hq, hr, he⟩ := mem_piecesText_iff.1 hp
  rw [he]
  exact h q hq p.1 hr

theorem inRangesB_within {rs : List (Nat × Nat)} {lo hi a : Nat}
    (hw : rangesWithinB rs lo hi = true) (ha : inRangesB rs a = true) : lo ≤ a ∧ a < hi := by
  obtain ⟨r, hr, h1, h2⟩ := inRangesB_iff.1 ha
  have := List.all_eq_true.1 hw r hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  omega

section Loaded

variable {m : ExtHashMap Nat (BitVec 8)}

/-- A footprint `T` is present in memory `m` (same shape as the machine layer's
    `TextLoaded`). -/
abbrev TextIn (T : List (Nat × BitVec 8)) (m : ExtHashMap Nat (BitVec 8)) : Prop :=
  ∀ p ∈ T, m[p.1]? = some p.2

theorem TextIn.left {A B : List (Nat × BitVec 8)} (h : TextIn (A ++ B) m) : TextIn A m :=
  fun p hp => h p (List.mem_append_left _ hp)

theorem TextIn.right {A B : List (Nat × BitVec 8)} (h : TextIn (A ++ B) m) : TextIn B m :=
  fun p hp => h p (List.mem_append_right _ hp)

theorem TextIn.pin {ps : List TextPiece} (h : TextIn (piecesText ps) m) {a : Nat} {b : BitVec 8}
    (hb : piecesHasB ps a b = true) : m[a]? = some b :=
  h _ (mem_piecesText hb)

/-- Four consecutive bytes from one Boolean check. -/
theorem TextIn.pin4 {ps : List TextPiece} (h : TextIn (piecesText ps) m) {a : Nat}
    {b0 b1 b2 b3 : BitVec 8} (hb : bytesHasB ps a [b0, b1, b2, b3] = true) :
    m[a]? = some b0 ∧ m[a + 1]? = some b1 ∧ m[a + 2]? = some b2 ∧ m[a + 3]? = some b3 :=
  ⟨h.pin (bytesHasB_get hb 0 (by simp)), h.pin (bytesHasB_get hb 1 (by simp)),
   h.pin (bytesHasB_get hb 2 (by simp)), h.pin (bytesHasB_get hb 3 (by simp))⟩

/-- Four byte facts at literal addresses, from one Boolean check. -/
theorem TextIn.pin4L {ps : List TextPiece} (h : TextIn (piecesText ps) m) (a0 a1 a2 a3 : Nat)
    {b0 b1 b2 b3 : BitVec 8}
    (hb : (piecesHasB ps a0 b0 && piecesHasB ps a1 b1 && piecesHasB ps a2 b2 &&
      piecesHasB ps a3 b3) = true) :
    m[a0]? = some b0 ∧ m[a1]? = some b1 ∧ m[a2]? = some b2 ∧ m[a3]? = some b3 := by
  simp only [Bool.and_eq_true] at hb
  exact ⟨h.pin hb.1.1.1, h.pin hb.1.1.2, h.pin hb.1.2, h.pin hb.2⟩

/-- A footprint stays present where memory agrees on it. -/
theorem TextIn.transport {T : List (Nat × BitVec 8)} {m' : ExtHashMap Nat (BitVec 8)}
    (h : TextIn T m) (hag : ∀ p ∈ T, m'[p.1]? = m[p.1]?) : TextIn T m' :=
  fun p hp => (hag p hp).trans (h p hp)

/-- A piece footprint from any present list that contains it (checked by `decide`). -/
theorem TextIn.of_list {ps : List TextPiece} {L : List (Nat × BitVec 8)} (hL : TextIn L m)
    (hsub : (ps.all fun q => q.ranges.all fun r =>
      (List.range (r.2 - r.1)).all fun k => L.contains (r.1 + k, q.img (r.1 + k))) = true) :
    TextIn (piecesText ps) m := by
  intro p hp
  obtain ⟨q, hq, hr, he⟩ := mem_piecesText_iff.1 hp
  obtain ⟨r, hrr, h1, h2⟩ := inRangesB_iff.1 hr
  have h3 := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 hsub q hq) r hrr)
    (p.1 - r.1) (List.mem_range.2 (by omega))
  rw [show r.1 + (p.1 - r.1) = p.1 by omega] at h3
  have : (p.1, q.img p.1) ∈ L := by simpa using h3
  rw [he]
  exact hL _ this

end Loaded

/-- The little-endian bytes of the literal `v` at `[base, base + n)`; the byte function of
    a small initialised data object that lies outside the fixed text/rodata image. -/
def natBytes (base v : Nat) (a : Nat) : BitVec 8 :=
  BitVec.ofNat 8 (Nat.shiftRight v (8 * (a - base)))

end Vsa.Sim
