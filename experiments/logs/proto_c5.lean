import Vsa.Sim.TermAssembly
open Vsa Vsa.Sim Vsa.MemRepr
open Std (ExtHashMap)

-- Cleaner: define constant-on-[0,N) by RECURSION on N, insert N-1 each step.
def crange : Nat → ExtHashMap Nat (BitVec 8)
  | 0 => ∅
  | n+1 => (crange n).insert n (0x1 : BitVec 8)

-- membership: k < N → crange N [k]? = some 1
theorem crange_get : ∀ N k, k < N → (crange N)[k]? = some (0x1 : BitVec 8) := by
  intro N
  induction N with
  | zero => intro k hk; exact absurd hk (by omega)
  | succ n ih =>
    intro k hk
    simp only [crange, Std.ExtHashMap.getElem?_insert]
    by_cases he : n = k
    · subst he; simp
    · rw [if_neg (by simp [beq_iff_eq]; omega)]
      exact ih k (by omega)

-- lookup OUTSIDE the range: k ≥ N → crange N [k]? = none
theorem crange_none : ∀ N k, N ≤ k → (crange N)[k]? = none := by
  intro N
  induction N with
  | zero => intro k hk; simp [crange]
  | succ n ih =>
    intro k hk
    simp only [crange, Std.ExtHashMap.getElem?_insert]
    rw [if_neg (by simp [beq_iff_eq]; omega)]
    exact ih k (by omega)
