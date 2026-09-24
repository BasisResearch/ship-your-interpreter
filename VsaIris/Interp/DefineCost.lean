import VsaIris.Interp.Repr
import Vsa.While.Cost

/-!
# `env_define`'s growth policy against the cost model

`capFor` (`Repr.lean`) and `arrayCostAux` (`Vsa/While/Cost.lean`) follow the
same fuel recursion over the caps `0, 8, 16, 32, …`. One more binding either
stays within the cap (no charge) or, at a full frame, moves to the next cap
and is charged that cap's `arrayReallocCost` (`capFor_succ`). `defineCost`
of a missing name is then the name copy plus exactly what `env_define`'s
growth `realloc`s request (`defineCost_miss`).
-/

namespace VsaIris.Interp

open Vsa.While

/-- The cap after `c`: `env.c`'s `cap ? 2 * cap : 8`. -/
def nextCap (c : Nat) : Nat := if c = 0 then 8 else 2 * c

theorem lt_nextCap (c : Nat) : c < nextCap c := by unfold nextCap; split <;> omega

theorem capForAux_zero (cap k : Nat) : capForAux 0 cap k = cap := rfl
theorem capForAux_succ (f cap k : Nat) :
    capForAux (f + 1) cap k = if k ≤ cap then cap else capForAux f (nextCap cap) k := rfl
theorem arrayCostAux_zero (cap k : Nat) : arrayCostAux 0 cap k = 0 := rfl
theorem arrayCostAux_succ (f cap k : Nat) :
    arrayCostAux (f + 1) cap k =
      if k ≤ cap then 0 else arrayReallocCost (nextCap cap) + arrayCostAux f (nextCap cap) k := rfl

/-- Fuel beyond the cap chain's reach changes nothing. -/
theorem capAux_fuel : ∀ (f cap k : Nat), k ≤ cap + f →
    capForAux f cap k = capForAux (f + 1) cap k ∧ arrayCostAux f cap k = arrayCostAux (f + 1) cap k
  | 0, cap, k, h => by
    rw [capForAux_succ, arrayCostAux_succ]
    simp only [show k ≤ cap by omega, ite_true]
    exact ⟨rfl, rfl⟩
  | f + 1, cap, k, h => by
    rw [capForAux_succ (f + 1), arrayCostAux_succ (f + 1), capForAux_succ f, arrayCostAux_succ f]
    by_cases hk : k ≤ cap
    · simp only [hk, ite_true]; exact ⟨trivial, trivial⟩
    · have := lt_nextCap cap
      have ih := capAux_fuel f (nextCap cap) k (by omega)
      simp only [hk, ite_false]
      exact ⟨ih.1, by rw [ih.2]⟩

/-- **One more binding**: at a full cap the next cap is reached and charged;
otherwise nothing changes. -/
theorem capAux_succ : ∀ (f cap k : Nat), k + 1 ≤ cap + f →
    (capForAux f cap k = k ∧ capForAux f cap (k + 1) = nextCap k ∧
      arrayCostAux f cap (k + 1) = arrayCostAux f cap k + arrayReallocCost (nextCap k)) ∨
    (k < capForAux f cap k ∧ capForAux f cap (k + 1) = capForAux f cap k ∧
      arrayCostAux f cap (k + 1) = arrayCostAux f cap k)
  | 0, cap, k, h => by
    right
    rw [capForAux_zero, capForAux_zero, arrayCostAux_zero, arrayCostAux_zero]
    exact ⟨by omega, rfl, rfl⟩
  | f + 1, cap, k, h => by
    rw [capForAux_succ, capForAux_succ, arrayCostAux_succ, arrayCostAux_succ]
    by_cases hk1 : k + 1 ≤ cap
    · right
      simp only [hk1, show k ≤ cap by omega, ite_true]
      exact ⟨by omega, trivial, trivial⟩
    · by_cases hk : k ≤ cap
      · -- `k = cap`: the frame is full
        have hkc : k = cap := by omega
        subst hkc
        left
        have hn := lt_nextCap k
        have hstop : capForAux f (nextCap k) (k + 1) = nextCap k ∧
            arrayCostAux f (nextCap k) (k + 1) = 0 := by
          cases f with
          | zero => exact ⟨rfl, rfl⟩
          | succ f =>
            rw [capForAux_succ, arrayCostAux_succ]
            simp only [show k + 1 ≤ nextCap k by omega, ite_true]
            exact ⟨trivial, trivial⟩
        simp only [hk, hk1, ite_true, ite_false, hstop.1, hstop.2]
        exact ⟨trivial, trivial, by omega⟩
      · have hn := lt_nextCap cap
        have ih := capAux_succ f (nextCap cap) k (by omega)
        simp only [hk, hk1, ite_false]
        rcases ih with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · left; exact ⟨h1, h2, by rw [h3]; omega⟩
        · right; exact ⟨h1, h2, by rw [h3]⟩

/-- **The canonical cap of one more binding**, and its cumulative charge. -/
theorem capFor_succ (n : Nat) :
    (capFor n = n ∧ capFor (n + 1) = nextCap n ∧
      arrayCost (n + 1) = arrayCost n + arrayReallocCost (nextCap n)) ∨
    (n < capFor n ∧ capFor (n + 1) = capFor n ∧ arrayCost (n + 1) = arrayCost n) := by
  have hf := capAux_fuel n 0 n (by omega)
  have hs := capAux_succ (n + 1) 0 n (by omega)
  unfold capFor arrayCost
  rw [hf.1, hf.2]
  exact hs

theorem arrayReallocCost_pos (c : Nat) (h : 1 ≤ c) : 0 < arrayReallocCost c := by
  unfold arrayReallocCost roundUp16; omega

/-- The charge of one more binding in a frame of `n`, as `defineCost` states it. -/
def growthCost (n : Nat) : Nat :=
  if n = 0 then arrayReallocCost 8
  else if arrayCostAux (n + 1) 0 (n + 1) ≠ arrayCostAux n 0 n then
    arrayCostAux (n + 1) 0 (n + 1) - arrayCostAux n 0 n
  else 0

/-- **The growth charge is the growth's two `realloc` requests** at a full
frame, and nothing otherwise. -/
theorem growthCost_eq (n : Nat) :
    (capFor n = n ∧ capFor (n + 1) = nextCap n ∧ growthCost n = arrayReallocCost (nextCap n)) ∨
    (n < capFor n ∧ capFor (n + 1) = capFor n ∧ growthCost n = 0) := by
  rcases capFor_succ n with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · left
    refine ⟨h1, h2, ?_⟩
    unfold growthCost
    by_cases h0 : n = 0
    · subst h0; rfl
    · have hp := arrayReallocCost_pos (nextCap n) (by have := lt_nextCap n; omega)
      unfold arrayCost at h3
      simp only [h0, ite_false, h3]
      have hne : arrayCostAux n 0 n + arrayReallocCost (nextCap n) ≠ arrayCostAux n 0 n := by omega
      rw [if_pos hne]
      omega
  · right
    refine ⟨h1, h2, ?_⟩
    unfold growthCost
    have h0 : n ≠ 0 := by
      intro h; subst h; exact absurd h1 (by decide)
    unfold arrayCost at h3
    simp [h0, h3]

/-- **`defineCost` of a missing name**: the name copy plus the growth. -/
theorem defineCost_miss {st : Store} {fa : Addr} {f : Frame} {x : String}
    (hf : st.frames[fa]? = some f) (hm : ¬ f.vars.any (·.1 == x)) :
    defineCost st fa x = nameCopyCost x + growthCost f.vars.length := by
  unfold defineCost growthCost
  rw [hf]
  simp only [hm, Bool.false_eq_true, ite_false]

/-- `defineCost` of a bound name is zero. -/
theorem defineCost_hit {st : Store} {fa : Addr} {f : Frame} {x : String}
    (hf : st.frames[fa]? = some f) (hm : f.vars.any (·.1 == x)) : defineCost st fa x = 0 := by
  unfold defineCost
  rw [hf]
  simp [hm]

end VsaIris.Interp
