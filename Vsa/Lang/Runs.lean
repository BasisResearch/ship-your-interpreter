import Vsa.Machine

/-! # Machine run algebra used by the language layer -/

namespace Vsa.Lang

open Vsa.Machine

/-- At least one machine step. -/
def Plus (c c' : Config) : Prop := ∃ n, StepsN (n + 1) c c'

theorem steps_trans {a b c : Config} (h1 : Steps a b) (h2 : Steps b c) : Steps a c := by
  induction h1 with
  | refl => exact h2
  | head s _ ih => exact .head s (ih h2)

theorem stepsN_toSteps {n : Nat} {a b : Config} (h : StepsN n a b) : Steps a b := by
  induction h with
  | zero => exact .refl _
  | succ s _ ih => exact .head s ih

theorem stepsN_append {n m : Nat} {a b c : Config} (h1 : StepsN n a b) (h2 : StepsN m b c) :
    StepsN (n + m) a c := by
  induction h1 with
  | zero => simpa using h2
  | succ s _ ih => rw [Nat.add_right_comm]; exact .succ s (ih h2)

theorem stepsN_prefix : ∀ {m k : Nat} {a c : Config}, StepsN (m + k) a c → ∃ b, StepsN m a b := by
  intro m
  induction m with
  | zero => intro k a c _; exact ⟨a, .zero _⟩
  | succ m ih =>
    intro k a c h
    rw [Nat.add_right_comm] at h
    cases h with
    | succ s r => obtain ⟨b, hb⟩ := ih r; exact ⟨b, .succ s hb⟩

theorem halts_of_steps {c c' : Config} {out : String} {e : Nat} (h : Steps c c')
    (h' : Halts c' out e) : Halts c out e := by
  obtain ⟨c'', σ, hs, hh, ho⟩ := h'
  exact ⟨c'', σ, steps_trans h hs, hh, ho⟩

end Vsa.Lang
