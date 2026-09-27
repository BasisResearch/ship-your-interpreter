import Vsa.Compiler.Run

/-!
# Failure within a number of steps

`Fail code n A`: from `A` the code reaches the error exit (a halt with code
`70`) or runs for at least `n` steps. Failure is closed under run prefixes
(`Fail.of_prefix`, `Fail.of_star`); a run between different code positions
takes a step (`StarN.pos_of_pc`).
-/

namespace Vsa.Compiler

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa.Sim

/-- The code fails within `n` steps: the error exit, or `n` steps of running. -/
def Fail (code : List Ins) (n : Nat) (A : AM) : Prop :=
  Reaches code A (fun B => astep code B = some (.halt 70)) ∨ Runs code n A

theorem StarN.truncate {code : List Ins} : ∀ {m : Nat} {A B : AM}, StarN code m A B →
    ∀ n, n ≤ m → Runs code n A
  | _, A, _, .refl _, n, h => ⟨A, by rw [Nat.le_zero.mp h]; exact .refl _⟩
  | _, A, _, .step hs rest, n, h => by
    cases n with
    | zero => exact ⟨A, .refl _⟩
    | succ n =>
      obtain ⟨B', h'⟩ := rest.truncate n (by omega)
      exact ⟨B', .step hs h'⟩

/-- A run of `k` steps followed by failure within `n - k` steps fails within `n`. -/
theorem Fail.of_prefix {code : List Ins} {n k : Nat} {A A' : AM} (hr : StarN code k A A')
    (hf : Fail code (n - k) A') : Fail code n A := by
  rcases hf with ⟨B, hB, hh⟩ | ⟨B, hB⟩
  · exact .inl ⟨B, Star.trans ⟨k, hr⟩ hB, hh⟩
  · by_cases hk : k ≤ n
    · exact .inr ⟨B, by have := hr.trans hB; rwa [Nat.add_sub_cancel' hk] at this⟩
    · exact .inr (hr.truncate n (by omega))

theorem Fail.of_star {code : List Ins} {n : Nat} {A A' : AM} (hr : Star code A A')
    (hf : Fail code n A') : Fail code n A := by
  obtain ⟨k, hk⟩ := hr
  exact Fail.of_prefix hk (by
    rcases hf with h | ⟨B, hB⟩
    · exact .inl h
    · exact .inr (hB.truncate _ (by omega)))

theorem pcOf_inj {a b : Nat} (ha : PosOK a) (hb : PosOK b) (h : pcOf a = pcOf b) : a = b := by
  have := congrArg BitVec.toNat h
  unfold PosOK at ha hb
  rw [pcOf_toNat (by have : tohostAddr = 0x8001ad00 := rfl; omega),
    pcOf_toNat (by have : tohostAddr = 0x8001ad00 := rfl; omega)] at this
  omega

/-- A run between different code positions takes at least one step. -/
theorem StarN.pos_of_pc {code : List Ins} {k : Nat} {A B : AM} (h : StarN code k A B)
    (hne : A.pc ≠ B.pc) : 1 ≤ k := by
  cases h with
  | refl => exact absurd rfl hne
  | step => omega

end Vsa.Compiler
