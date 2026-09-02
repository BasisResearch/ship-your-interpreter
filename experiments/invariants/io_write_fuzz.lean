/-
Experiments 2 (fuzz SURVIVE) + 3 (CTI: 3 mutants must REFUTE) for the mined
_write loop invariant.  Self-contained, hermetic — mirrors statement_fuzz.py's
acceptance idiom (a ¬P probe that machine-checks axiom-clean ⟺ REFUTED).

Verdict protocol:
  * SURVIVED  ⟺ the ¬P probe CANNOT be closed (no lethal witness) — we assert
    this by instead PROVING P (the candidate holds).
  * REFUTED   ⟺ ¬(mutant) is provable axiom-clean (a witness kills it).

Nothing here enters a proof of the real binary — pre-proof CTI validation.
-/

namespace IoWriteFuzz

structure WG where
  buf : Nat
  len : Nat
  writeCmd : Nat

-- The mined (correct) invariant fields.
structure WInvMined (g : WG) (k a1 a3 a2 a4 : Nat) : Prop where
  klt   : k < g.len
  a1cur : a1 = g.buf + k
  a3end : a3 = g.buf + g.len
  a2len : a2 = g.len
  a4cmd : a4 = g.writeCmd
  guard : a1 < a3

def Candidate : Prop :=
  ∀ (g : WG) (k a1 a3 a2 a4 : Nat),
    WInvMined g k a1 a3 a2 a4 → (a1 < a3) ∧ (a3 - a1 = g.len - k)

/-- SURVIVED: the candidate is provable, so no lethal witness exists. -/
theorem candidate_survives : Candidate := by
  intro g k a1 a3 a2 a4 h
  exact ⟨h.guard, by rw [h.a1cur, h.a3end]; omega⟩
#print axioms candidate_survives   -- must be ⊆ {propext, Classical.choice, Quot.sound}

/-! ## Experiment 3 — three FALSE mutants; the fuzzer must REFUTE all three. -/

-- MUTANT 1: DROP A GUARD.  Remove the `guard : a1 < a3` field, but the
-- candidate still CLAIMS `a1 < a3` in the conclusion.  Without the guard the
-- witness k = len (so a1 = a3, cursor at end) refutes it.
structure WInv_dropGuard (g : WG) (k a1 a3 a2 a4 : Nat) : Prop where
  a1cur : a1 = g.buf + k
  a3end : a3 = g.buf + g.len
  a2len : a2 = g.len
  a4cmd : a4 = g.writeCmd
  -- guard DROPPED

def Mutant_dropGuard : Prop :=
  ∀ (g : WG) (k a1 a3 a2 a4 : Nat),
    WInv_dropGuard g k a1 a3 a2 a4 → (a1 < a3)

theorem refute_dropGuard : ¬ Mutant_dropGuard := by
  intro H
  -- witness: g = ⟨0, 3, 0⟩, k = 3 (=len), a1 = 3, a3 = 3 ⇒ a1 < a3 is false.
  have h := H ⟨0, 3, 0⟩ 3 3 3 3 0 ⟨rfl, rfl, rfl, rfl⟩
  exact absurd h (by decide)
#print axioms refute_dropGuard

-- MUTANT 2: WIDEN A CONSTANT.  Claim the STRONGER progress measure
-- `a3 - a1 = g.len - k + 1` (off-by-one widening of the bound).  False.
def Mutant_widenConst : Prop :=
  ∀ (g : WG) (k a1 a3 a2 a4 : Nat),
    WInvMined g k a1 a3 a2 a4 → (a3 - a1 = g.len - k + 1)

theorem refute_widenConst : ¬ Mutant_widenConst := by
  intro H
  -- witness: g = ⟨0, 3, 0⟩, k = 0, a1 = 0, a3 = 3 ⇒ a3-a1 = 3 ≠ 3-0+1 = 4.
  have h := H ⟨0, 3, 0⟩ 0 0 3 3 0
      ⟨by decide, rfl, rfl, rfl, rfl, by decide⟩
  exact absurd h (by decide)
#print axioms refute_widenConst

-- MUTANT 3: SWAP A BOUND.  Swap the guard direction to `a3 < a1`
-- (claim the cursor is ABOVE the end).  Contradicts the true fields.
def Mutant_swapBound : Prop :=
  ∀ (g : WG) (k a1 a3 a2 a4 : Nat),
    WInvMined g k a1 a3 a2 a4 → (a3 < a1)

theorem refute_swapBound : ¬ Mutant_swapBound := by
  intro H
  -- witness: g = ⟨0, 3, 0⟩, k = 0, a1 = 0, a3 = 3 ⇒ a3 < a1 is 3 < 0, false.
  have h := H ⟨0, 3, 0⟩ 0 0 3 3 0
      ⟨by decide, rfl, rfl, rfl, rfl, by decide⟩
  exact absurd h (by decide)
#print axioms refute_swapBound

end IoWriteFuzz
