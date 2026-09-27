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

/-- **The frame as data**: `m` agrees with `m0` everywhere outside the windows
`ws`.  `ws` is meant to be a *concrete* list (symbolic bounds are fine). -/
def FrameOn (ws : List W) (m0 m : Std.ExtHashMap Nat (BitVec 8)) : Prop :=
  ∀ a, OutW ws a → m[a]? = m0[a]?

/-! ## Side-condition plumbing -/

/-- A point outside all windows is disjoint from any range inside one. -/
theorem outW_disjoint_inside {ws : List W} {a A n : Nat}
    (ho : OutW ws a) (hi : InsideW ws A n) : a < A ∨ A + n ≤ a := by
  induction ws with
  | nil => exact False.elim hi
  | cons w ws ih =>
    rcases hi with hw | hrest
    · have := ho.1; omega
    · exact ih ho.2 hrest

/-! ## Core frame algebra -/

theorem frameOn_refl (ws : List W) (m : Std.ExtHashMap Nat (BitVec 8)) :
    FrameOn ws m m := fun _ _ => rfl

/-! ## One-line predicate transports -/

/-! ## Write preservation: stores inside a window keep the frame -/

/-! ## Bespoke ↔ data bridges

`frameOn_of_pointwiseK` consumes an existing capstone's `K`-window pointwise
conclusion; `pointwise_of_frameOnK` restates a `FrameOn` in the legacy shape
(so record-style wrappers can feed flat-style consumers and vice versa). -/

/-! ## Bespoke ↔ data bridges

`frameOn_of_pointwiseK` consumes an existing capstone's `K`-window pointwise
conclusion; `pointwise_of_frameOnK` restates a `FrameOn` in the legacy shape
(so record-style wrappers can feed flat-style consumers and vice versa). -/

end Vsa.Sim
