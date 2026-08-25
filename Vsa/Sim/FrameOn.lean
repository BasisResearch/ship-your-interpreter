import Vsa.Sim.SnprintfSpec19
import Vsa.Sim.Mfr

/-!
# `FrameOn` — memory frames as *data* (window lists)

Every capstone so far states its memory frame as a bespoke pointwise
conjunction over 4–9 windows

    ∀ a, ¬(l₁ ≤ a ∧ a < h₁) → … → ¬(l_k ≤ a ∧ a < h_k) → mem[a]? = m0[a]?

and every composition hand-writes two-sided `*_of_agree` transports per
predicate (`SnprintfSpec26`'s `hagree`/`hslotUp` block is the worst case:
~40 `have`s, each re-threading 4–6 `by omega` window disequalities).

This module replaces the *shape* with data: a window is a `W` (a `lo`/`hi`
pair, the footprint `[lo, hi)`), a frame is

    FrameOn ws m0 m  :=  ∀ a, OutW ws a → m[a]? = m0[a]?

and the side conditions of every lemma are **recursively defined list
predicates** (`OutW`, `OutWRange`, `InsideW`, `AllCovered`) that unfold to
plain conjunctions/disjunctions of linear facts for any *concrete* window
list — so they close with `by simp only [...]; omega` (`decide` is never
needed and window bounds may be symbolic, e.g. `vsp.toNat + 16`).

API:

* `frameOn_refl`, `frameOn_trans` (window-list union = `++`),
  `frameOn_mono` (`AllCovered ws ws'`: every old window inside some new one);
* `frameOn_read` / `frameOn_read_range` — reads outside all windows transfer;
* one-line predicate transports: `pin8_of_frameOn`, `pin4_of_frameOn`,
  `byte_of_frameOn`, `slotHolds_of_frameOn`, `mvBytes_of_frameOn`;
* write preservation: `frameOn_insert`, `frameOn_writeMap4`,
  `frameOn_writeMap8` (a write *inside* some window keeps the frame);
* the bespoke↔data bridges `frameOn_of_pointwise2..9` /
  `pointwise_of_frameOn2..9` for consuming/producing the existing capstone
  conclusions (Spec20's `ssprint_iov2_post` six-window frame, Spec26's
  nine-window frame, Spec42/55's two-window frame).

The `writeLog` interop (`Vsa/Sim/BlockMem.lean`'s computed memory posts)
lives in `Vsa/Sim/WriteLogNF.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa

namespace Vsa.Sim

/-- A memory window: the footprint is the half-open interval `[lo, hi)`. -/
structure W where
  lo : Nat
  hi : Nat

/-- `a` lies outside every window of `ws`.  Recursively defined so a concrete
list unfolds to a conjunction of interval facts (`simp only [OutW]; omega`). -/
def OutW : List W → Nat → Prop
  | [], _ => True
  | w :: ws, a => (a < w.lo ∨ w.hi ≤ a) ∧ OutW ws a

/-- The whole range `[A, A+n)` lies outside every window of `ws`. -/
def OutWRange : List W → Nat → Nat → Prop
  | [], _, _ => True
  | w :: ws, A, n => (A + n ≤ w.lo ∨ w.hi ≤ A) ∧ OutWRange ws A n

/-- The range `[A, A+n)` lies inside a *single* window of `ws`. -/
def InsideW : List W → Nat → Nat → Prop
  | [], _, _ => False
  | w :: ws, A, n => (w.lo ≤ A ∧ A + n ≤ w.hi) ∨ InsideW ws A n

/-- Every window of the first list is contained in some window of the second
(the side condition of `frameOn_mono`). -/
def AllCovered : List W → List W → Prop
  | [], _ => True
  | w :: ws, ws' => InsideW ws' w.lo (w.hi - w.lo) ∧ AllCovered ws ws'

/-- **The frame as data**: `m` agrees with `m0` everywhere outside the windows
`ws`.  `ws` is meant to be a *concrete* list (symbolic bounds are fine). -/
def FrameOn (ws : List W) (m0 m : Std.ExtHashMap Nat (BitVec 8)) : Prop :=
  ∀ a, OutW ws a → m[a]? = m0[a]?

/-! ## Side-condition plumbing -/

theorem outW_of_range {ws : List W} {A n k : Nat}
    (h : OutWRange ws A n) (hk1 : A ≤ k) (hk2 : k < A + n) : OutW ws k := by
  induction ws with
  | nil => trivial
  | cons w ws ih => exact ⟨by have := h.1; omega, ih h.2⟩

theorem outW_append {ws1 ws2 : List W} {a : Nat}
    (h : OutW (ws1 ++ ws2) a) : OutW ws1 a ∧ OutW ws2 a := by
  induction ws1 with
  | nil => exact ⟨trivial, h⟩
  | cons w ws ih =>
    obtain ⟨hw, hrest⟩ := h
    obtain ⟨h1, h2⟩ := ih hrest
    exact ⟨⟨hw, h1⟩, h2⟩

/-- A point outside all windows is disjoint from any range inside one. -/
theorem outW_disjoint_inside {ws : List W} {a A n : Nat}
    (ho : OutW ws a) (hi : InsideW ws A n) : a < A ∨ A + n ≤ a := by
  induction ws with
  | nil => exact False.elim hi
  | cons w ws ih =>
    rcases hi with hw | hrest
    · have := ho.1; omega
    · exact ih ho.2 hrest

/-- Containment transports "outside": outside the covering list ⇒ outside the
covered list. -/
theorem outW_of_covered {ws ws' : List W} {a : Nat}
    (hc : AllCovered ws ws') (ho : OutW ws' a) : OutW ws a := by
  induction ws with
  | nil => trivial
  | cons w rest ih =>
    refine ⟨?_, ih hc.2⟩
    have := outW_disjoint_inside ho hc.1
    omega

/-! ## Core frame algebra -/

theorem frameOn_refl (ws : List W) (m : Std.ExtHashMap Nat (BitVec 8)) :
    FrameOn ws m m := fun _ _ => rfl

/-- Composition: frames chain and the window lists *union* (list append). -/
theorem frameOn_trans {ws1 ws2 : List W} {m0 m1 m2 : Std.ExtHashMap Nat (BitVec 8)}
    (h1 : FrameOn ws1 m0 m1) (h2 : FrameOn ws2 m1 m2) :
    FrameOn (ws1 ++ ws2) m0 m2 := by
  intro a ha
  obtain ⟨ha1, ha2⟩ := outW_append ha
  exact (h2 a ha2).trans (h1 a ha1)

/-- Weakening: a frame outside `ws` is a frame outside any covering `ws'`
(each `w ∈ ws` inside some `w' ∈ ws'`; for concrete lists the side condition
closes by `simp only [AllCovered, InsideW]; omega`). -/
theorem frameOn_mono {ws ws' : List W} {m0 m : Std.ExtHashMap Nat (BitVec 8)}
    (hc : AllCovered ws ws') (h : FrameOn ws m0 m) : FrameOn ws' m0 m :=
  fun a ha => h a (outW_of_covered hc ha)

/-- Read transfer at one address (`frameOn_read hF a (by simp only [OutW]; omega)`). -/
theorem frameOn_read {ws : List W} {m0 m : Std.ExtHashMap Nat (BitVec 8)}
    (h : FrameOn ws m0 m) (a : Nat) (ha : OutW ws a) : m[a]? = m0[a]? := h a ha

/-- Read transfer over a whole range, in the shape `Pin8_frame`/`Pin4_frame`/
`slot_survives_frame` consume. -/
theorem frameOn_read_range {ws : List W} {m0 m : Std.ExtHashMap Nat (BitVec 8)}
    (h : FrameOn ws m0 m) (A n : Nat) (hout : OutWRange ws A n) :
    ∀ k, A ≤ k → k < A + n → m[k]? = m0[k]? :=
  fun k hk1 hk2 => h k (outW_of_range hout hk1 hk2)

/-! ## One-line predicate transports -/

/-- A byte pin outside all windows crosses the frame. -/
theorem byte_of_frameOn {ws : List W} {m0 m : Std.ExtHashMap Nat (BitVec 8)}
    {A : Nat} {b : BitVec 8} (h : FrameOn ws m0 m) (ha : OutW ws A)
    (hb : m0[A]? = some b) : m[A]? = some b := (h A ha).trans hb

theorem pin8_of_frameOn {ws : List W} {m0 m : Std.ExtHashMap Nat (BitVec 8)}
    {A : Nat} {v : BitVec 64} (h : FrameOn ws m0 m) (hout : OutWRange ws A 8)
    (hp : Pin8 m0 A v) : Pin8 m A v :=
  Pin8_frame (frameOn_read_range h A 8 hout) hp

theorem pin4_of_frameOn {ws : List W} {m0 m : Std.ExtHashMap Nat (BitVec 8)}
    {A : Nat} {v : BitVec 32} (h : FrameOn ws m0 m) (hout : OutWRange ws A 4)
    (hp : Pin4 m0 A v) : Pin4 m A v :=
  Pin4_frame (frameOn_read_range h A 4 hout) hp

/-- `SlotHolds` crosses the frame; `hA` names the slot's effective address so
the window side condition is plain linear arithmetic. -/
theorem slotHolds_of_frameOn {ws : List W} {m0 m : Std.ExtHashMap Nat (BitVec 8)}
    (base : BitVec 64) (off : Nat) (v : BitVec 64) (A : Nat)
    (hA : (base + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat = A)
    (h : FrameOn ws m0 m) (hout : OutWRange ws A 8)
    (hs : SlotHolds base off v m0) : SlotHolds base off v m := by
  unfold SlotHolds at hs ⊢
  rw [hA] at hs ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hs
  have hr := frameOn_read_range h A 8 hout
  exact ⟨(hr _ (by omega) (by omega)).trans h0, (hr _ (by omega) (by omega)).trans h1,
    (hr _ (by omega) (by omega)).trans h2, (hr _ (by omega) (by omega)).trans h3,
    (hr _ (by omega) (by omega)).trans h4, (hr _ (by omega) (by omega)).trans h5,
    (hr _ (by omega) (by omega)).trans h6, (hr _ (by omega) (by omega)).trans h7⟩

/-- A source-byte window (`MvBytes`) crosses the frame. -/
theorem mvBytes_of_frameOn {ws : List W} {m0 m : Std.ExtHashMap Nat (BitVec 8)}
    {src : BitVec 64} {n : Nat} {bs : Nat → BitVec 8}
    (h : FrameOn ws m0 m) (hout : OutWRange ws src.toNat n)
    (hb : MvBytes m0 src n bs) : MvBytes m src n bs :=
  fun k hk => (frameOn_read_range h src.toNat n hout _ (by omega) (by omega)).trans (hb k hk)

/-! ## Write preservation: stores inside a window keep the frame -/

/-- A single byte store inside some window preserves the frame. -/
theorem frameOn_insert {ws : List W} {m0 m : Std.ExtHashMap Nat (BitVec 8)}
    (h : FrameOn ws m0 m) (k : Nat) (b : BitVec 8) (hin : InsideW ws k 1) :
    FrameOn ws m0 (m.insert k b) := by
  intro a ha
  have := outW_disjoint_inside ha hin
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]
  exact h a ha

/-- A 4-byte store inside some window preserves the frame. -/
theorem frameOn_writeMap4 {ws : List W} {m0 m : Std.ExtHashMap Nat (BitVec 8)}
    (h : FrameOn ws m0 m) (k : Nat) (d : BitVec (8 * 4)) (hin : InsideW ws k 4) :
    FrameOn ws m0 (writeMap4 m k d) := by
  intro a ha
  have := outW_disjoint_inside ha hin
  rw [getElem?_writeMap4_out _ _ _ _ (by omega)]
  exact h a ha

/-- An 8-byte store inside some window preserves the frame. -/
theorem frameOn_writeMap8 {ws : List W} {m0 m : Std.ExtHashMap Nat (BitVec 8)}
    (h : FrameOn ws m0 m) (k : Nat) (d : BitVec (8 * 8)) (hin : InsideW ws k 8) :
    FrameOn ws m0 (writeMap8 m k d) := by
  intro a ha
  have := outW_disjoint_inside ha hin
  rw [getElem?_writeMap8_out _ _ _ _ (by omega)]
  exact h a ha

/-! ## Bespoke ↔ data bridges

`frameOn_of_pointwiseK` consumes an existing capstone's `K`-window pointwise
conclusion; `pointwise_of_frameOnK` restates a `FrameOn` in the legacy shape
(so record-style wrappers can feed flat-style consumers and vice versa). -/

/-! ## Bespoke ↔ data bridges

`frameOn_of_pointwiseK` consumes an existing capstone's `K`-window pointwise
conclusion; `pointwise_of_frameOnK` restates a `FrameOn` in the legacy shape
(so record-style wrappers can feed flat-style consumers and vice versa). -/

theorem frameOn_of_pointwise1 {m0 m : Std.ExtHashMap Nat (BitVec 8)}
    {l1 h1 : Nat}
    (h : ∀ a,
      ¬(l1 ≤ a ∧ a < h1) →
      m[a]? = m0[a]?) :
    FrameOn [⟨l1, h1⟩] m0 m := by
  intro a ha
  simp only [OutW, and_true] at ha
  exact h a (by omega)

theorem frameOn_of_pointwise2 {m0 m : Std.ExtHashMap Nat (BitVec 8)}
    {l1 h1 l2 h2 : Nat}
    (h : ∀ a,
      ¬(l1 ≤ a ∧ a < h1) → ¬(l2 ≤ a ∧ a < h2) →
      m[a]? = m0[a]?) :
    FrameOn [⟨l1, h1⟩, ⟨l2, h2⟩] m0 m := by
  intro a ha
  simp only [OutW, and_true] at ha
  exact h a (by omega) (by omega)

theorem frameOn_of_pointwise3 {m0 m : Std.ExtHashMap Nat (BitVec 8)}
    {l1 h1 l2 h2 l3 h3 : Nat}
    (h : ∀ a,
      ¬(l1 ≤ a ∧ a < h1) → ¬(l2 ≤ a ∧ a < h2) → ¬(l3 ≤ a ∧ a < h3) →
      m[a]? = m0[a]?) :
    FrameOn [⟨l1, h1⟩, ⟨l2, h2⟩, ⟨l3, h3⟩] m0 m := by
  intro a ha
  simp only [OutW, and_true] at ha
  exact h a (by omega) (by omega) (by omega)

theorem frameOn_of_pointwise4 {m0 m : Std.ExtHashMap Nat (BitVec 8)}
    {l1 h1 l2 h2 l3 h3 l4 h4 : Nat}
    (h : ∀ a,
      ¬(l1 ≤ a ∧ a < h1) → ¬(l2 ≤ a ∧ a < h2) → ¬(l3 ≤ a ∧ a < h3) →
      ¬(l4 ≤ a ∧ a < h4) →
      m[a]? = m0[a]?) :
    FrameOn [⟨l1, h1⟩, ⟨l2, h2⟩, ⟨l3, h3⟩, ⟨l4, h4⟩] m0 m := by
  intro a ha
  simp only [OutW, and_true] at ha
  exact h a (by omega) (by omega) (by omega) (by omega)

theorem frameOn_of_pointwise5 {m0 m : Std.ExtHashMap Nat (BitVec 8)}
    {l1 h1 l2 h2 l3 h3 l4 h4 l5 h5 : Nat}
    (h : ∀ a,
      ¬(l1 ≤ a ∧ a < h1) → ¬(l2 ≤ a ∧ a < h2) → ¬(l3 ≤ a ∧ a < h3) →
      ¬(l4 ≤ a ∧ a < h4) → ¬(l5 ≤ a ∧ a < h5) →
      m[a]? = m0[a]?) :
    FrameOn [⟨l1, h1⟩, ⟨l2, h2⟩, ⟨l3, h3⟩, ⟨l4, h4⟩, ⟨l5, h5⟩] m0 m := by
  intro a ha
  simp only [OutW, and_true] at ha
  exact h a (by omega) (by omega) (by omega) (by omega) (by omega)

theorem frameOn_of_pointwise6 {m0 m : Std.ExtHashMap Nat (BitVec 8)}
    {l1 h1 l2 h2 l3 h3 l4 h4 l5 h5 l6 h6 : Nat}
    (h : ∀ a,
      ¬(l1 ≤ a ∧ a < h1) → ¬(l2 ≤ a ∧ a < h2) → ¬(l3 ≤ a ∧ a < h3) →
      ¬(l4 ≤ a ∧ a < h4) → ¬(l5 ≤ a ∧ a < h5) → ¬(l6 ≤ a ∧ a < h6) →
      m[a]? = m0[a]?) :
    FrameOn [⟨l1, h1⟩, ⟨l2, h2⟩, ⟨l3, h3⟩, ⟨l4, h4⟩, ⟨l5, h5⟩, ⟨l6, h6⟩] m0 m := by
  intro a ha
  simp only [OutW, and_true] at ha
  exact h a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

theorem frameOn_of_pointwise7 {m0 m : Std.ExtHashMap Nat (BitVec 8)}
    {l1 h1 l2 h2 l3 h3 l4 h4 l5 h5 l6 h6 l7 h7 : Nat}
    (h : ∀ a,
      ¬(l1 ≤ a ∧ a < h1) → ¬(l2 ≤ a ∧ a < h2) → ¬(l3 ≤ a ∧ a < h3) →
      ¬(l4 ≤ a ∧ a < h4) → ¬(l5 ≤ a ∧ a < h5) → ¬(l6 ≤ a ∧ a < h6) →
      ¬(l7 ≤ a ∧ a < h7) →
      m[a]? = m0[a]?) :
    FrameOn [⟨l1, h1⟩, ⟨l2, h2⟩, ⟨l3, h3⟩, ⟨l4, h4⟩, ⟨l5, h5⟩, ⟨l6, h6⟩, ⟨l7, h7⟩] m0 m := by
  intro a ha
  simp only [OutW, and_true] at ha
  exact h a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

theorem frameOn_of_pointwise8 {m0 m : Std.ExtHashMap Nat (BitVec 8)}
    {l1 h1 l2 h2 l3 h3 l4 h4 l5 h5 l6 h6 l7 h7 l8 h8 : Nat}
    (h : ∀ a,
      ¬(l1 ≤ a ∧ a < h1) → ¬(l2 ≤ a ∧ a < h2) → ¬(l3 ≤ a ∧ a < h3) →
      ¬(l4 ≤ a ∧ a < h4) → ¬(l5 ≤ a ∧ a < h5) → ¬(l6 ≤ a ∧ a < h6) →
      ¬(l7 ≤ a ∧ a < h7) → ¬(l8 ≤ a ∧ a < h8) →
      m[a]? = m0[a]?) :
    FrameOn [⟨l1, h1⟩, ⟨l2, h2⟩, ⟨l3, h3⟩, ⟨l4, h4⟩, ⟨l5, h5⟩, ⟨l6, h6⟩, ⟨l7, h7⟩, ⟨l8, h8⟩] m0 m := by
  intro a ha
  simp only [OutW, and_true] at ha
  exact h a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

theorem frameOn_of_pointwise9 {m0 m : Std.ExtHashMap Nat (BitVec 8)}
    {l1 h1 l2 h2 l3 h3 l4 h4 l5 h5 l6 h6 l7 h7 l8 h8 l9 h9 : Nat}
    (h : ∀ a,
      ¬(l1 ≤ a ∧ a < h1) → ¬(l2 ≤ a ∧ a < h2) → ¬(l3 ≤ a ∧ a < h3) →
      ¬(l4 ≤ a ∧ a < h4) → ¬(l5 ≤ a ∧ a < h5) → ¬(l6 ≤ a ∧ a < h6) →
      ¬(l7 ≤ a ∧ a < h7) → ¬(l8 ≤ a ∧ a < h8) → ¬(l9 ≤ a ∧ a < h9) →
      m[a]? = m0[a]?) :
    FrameOn [⟨l1, h1⟩, ⟨l2, h2⟩, ⟨l3, h3⟩, ⟨l4, h4⟩, ⟨l5, h5⟩, ⟨l6, h6⟩, ⟨l7, h7⟩, ⟨l8, h8⟩, ⟨l9, h9⟩] m0 m := by
  intro a ha
  simp only [OutW, and_true] at ha
  exact h a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

theorem pointwise_of_frameOn1 {m0 m : Std.ExtHashMap Nat (BitVec 8)}
    {l1 h1 : Nat}
    (h : FrameOn [⟨l1, h1⟩] m0 m) :
    ∀ a,
      ¬(l1 ≤ a ∧ a < h1) →
      m[a]? = m0[a]? :=
  fun a w1 => h a (by simp only [OutW, and_true]; omega)

theorem pointwise_of_frameOn2 {m0 m : Std.ExtHashMap Nat (BitVec 8)}
    {l1 h1 l2 h2 : Nat}
    (h : FrameOn [⟨l1, h1⟩, ⟨l2, h2⟩] m0 m) :
    ∀ a,
      ¬(l1 ≤ a ∧ a < h1) → ¬(l2 ≤ a ∧ a < h2) →
      m[a]? = m0[a]? :=
  fun a w1 w2 => h a (by simp only [OutW, and_true]; omega)

theorem pointwise_of_frameOn3 {m0 m : Std.ExtHashMap Nat (BitVec 8)}
    {l1 h1 l2 h2 l3 h3 : Nat}
    (h : FrameOn [⟨l1, h1⟩, ⟨l2, h2⟩, ⟨l3, h3⟩] m0 m) :
    ∀ a,
      ¬(l1 ≤ a ∧ a < h1) → ¬(l2 ≤ a ∧ a < h2) → ¬(l3 ≤ a ∧ a < h3) →
      m[a]? = m0[a]? :=
  fun a w1 w2 w3 => h a (by simp only [OutW, and_true]; omega)

theorem pointwise_of_frameOn4 {m0 m : Std.ExtHashMap Nat (BitVec 8)}
    {l1 h1 l2 h2 l3 h3 l4 h4 : Nat}
    (h : FrameOn [⟨l1, h1⟩, ⟨l2, h2⟩, ⟨l3, h3⟩, ⟨l4, h4⟩] m0 m) :
    ∀ a,
      ¬(l1 ≤ a ∧ a < h1) → ¬(l2 ≤ a ∧ a < h2) → ¬(l3 ≤ a ∧ a < h3) →
      ¬(l4 ≤ a ∧ a < h4) →
      m[a]? = m0[a]? :=
  fun a w1 w2 w3 w4 => h a (by simp only [OutW, and_true]; omega)

theorem pointwise_of_frameOn5 {m0 m : Std.ExtHashMap Nat (BitVec 8)}
    {l1 h1 l2 h2 l3 h3 l4 h4 l5 h5 : Nat}
    (h : FrameOn [⟨l1, h1⟩, ⟨l2, h2⟩, ⟨l3, h3⟩, ⟨l4, h4⟩, ⟨l5, h5⟩] m0 m) :
    ∀ a,
      ¬(l1 ≤ a ∧ a < h1) → ¬(l2 ≤ a ∧ a < h2) → ¬(l3 ≤ a ∧ a < h3) →
      ¬(l4 ≤ a ∧ a < h4) → ¬(l5 ≤ a ∧ a < h5) →
      m[a]? = m0[a]? :=
  fun a w1 w2 w3 w4 w5 => h a (by simp only [OutW, and_true]; omega)

theorem pointwise_of_frameOn6 {m0 m : Std.ExtHashMap Nat (BitVec 8)}
    {l1 h1 l2 h2 l3 h3 l4 h4 l5 h5 l6 h6 : Nat}
    (h : FrameOn [⟨l1, h1⟩, ⟨l2, h2⟩, ⟨l3, h3⟩, ⟨l4, h4⟩, ⟨l5, h5⟩, ⟨l6, h6⟩] m0 m) :
    ∀ a,
      ¬(l1 ≤ a ∧ a < h1) → ¬(l2 ≤ a ∧ a < h2) → ¬(l3 ≤ a ∧ a < h3) →
      ¬(l4 ≤ a ∧ a < h4) → ¬(l5 ≤ a ∧ a < h5) → ¬(l6 ≤ a ∧ a < h6) →
      m[a]? = m0[a]? :=
  fun a w1 w2 w3 w4 w5 w6 => h a (by simp only [OutW, and_true]; omega)

theorem pointwise_of_frameOn7 {m0 m : Std.ExtHashMap Nat (BitVec 8)}
    {l1 h1 l2 h2 l3 h3 l4 h4 l5 h5 l6 h6 l7 h7 : Nat}
    (h : FrameOn [⟨l1, h1⟩, ⟨l2, h2⟩, ⟨l3, h3⟩, ⟨l4, h4⟩, ⟨l5, h5⟩, ⟨l6, h6⟩, ⟨l7, h7⟩] m0 m) :
    ∀ a,
      ¬(l1 ≤ a ∧ a < h1) → ¬(l2 ≤ a ∧ a < h2) → ¬(l3 ≤ a ∧ a < h3) →
      ¬(l4 ≤ a ∧ a < h4) → ¬(l5 ≤ a ∧ a < h5) → ¬(l6 ≤ a ∧ a < h6) →
      ¬(l7 ≤ a ∧ a < h7) →
      m[a]? = m0[a]? :=
  fun a w1 w2 w3 w4 w5 w6 w7 => h a (by simp only [OutW, and_true]; omega)

theorem pointwise_of_frameOn8 {m0 m : Std.ExtHashMap Nat (BitVec 8)}
    {l1 h1 l2 h2 l3 h3 l4 h4 l5 h5 l6 h6 l7 h7 l8 h8 : Nat}
    (h : FrameOn [⟨l1, h1⟩, ⟨l2, h2⟩, ⟨l3, h3⟩, ⟨l4, h4⟩, ⟨l5, h5⟩, ⟨l6, h6⟩, ⟨l7, h7⟩, ⟨l8, h8⟩] m0 m) :
    ∀ a,
      ¬(l1 ≤ a ∧ a < h1) → ¬(l2 ≤ a ∧ a < h2) → ¬(l3 ≤ a ∧ a < h3) →
      ¬(l4 ≤ a ∧ a < h4) → ¬(l5 ≤ a ∧ a < h5) → ¬(l6 ≤ a ∧ a < h6) →
      ¬(l7 ≤ a ∧ a < h7) → ¬(l8 ≤ a ∧ a < h8) →
      m[a]? = m0[a]? :=
  fun a w1 w2 w3 w4 w5 w6 w7 w8 => h a (by simp only [OutW, and_true]; omega)

theorem pointwise_of_frameOn9 {m0 m : Std.ExtHashMap Nat (BitVec 8)}
    {l1 h1 l2 h2 l3 h3 l4 h4 l5 h5 l6 h6 l7 h7 l8 h8 l9 h9 : Nat}
    (h : FrameOn [⟨l1, h1⟩, ⟨l2, h2⟩, ⟨l3, h3⟩, ⟨l4, h4⟩, ⟨l5, h5⟩, ⟨l6, h6⟩, ⟨l7, h7⟩, ⟨l8, h8⟩, ⟨l9, h9⟩] m0 m) :
    ∀ a,
      ¬(l1 ≤ a ∧ a < h1) → ¬(l2 ≤ a ∧ a < h2) → ¬(l3 ≤ a ∧ a < h3) →
      ¬(l4 ≤ a ∧ a < h4) → ¬(l5 ≤ a ∧ a < h5) → ¬(l6 ≤ a ∧ a < h6) →
      ¬(l7 ≤ a ∧ a < h7) → ¬(l8 ≤ a ∧ a < h8) → ¬(l9 ≤ a ∧ a < h9) →
      m[a]? = m0[a]? :=
  fun a w1 w2 w3 w4 w5 w6 w7 w8 w9 => h a (by simp only [OutW, and_true]; omega)

end Vsa.Sim
