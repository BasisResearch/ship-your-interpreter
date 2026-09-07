import Vsa.Machine

/-! Generic deterministic transport for finite prefixes ending stuck.
No concrete prefix or machine fault is established in this file. -/

namespace Vsa.Machine

/-- A configuration with neither a successor nor an HTIF halt result. -/
structure Stuck (c : Config) : Prop where
  no_step : ∀ c', ¬ Step c c'
  no_halt : ∀ code σf, ¬ Halted c code σf

/-- Any halting run must follow the actual next step. -/
theorem Step.halts_tail {a b : Config} {out : String} {code : Nat}
    (hs : Step a b) (hh : Halts a out code) : Halts b out code := by
  obtain ⟨last, σf, path, halt, output⟩ := hh
  cases path with
  | refl => exact (hs.not_halted halt).elim
  | head first rest =>
    obtain rfl := hs.deterministic first
    exact ⟨last, σf, rest, halt, output⟩

/-- A hypothetical halt follows every actual finite prefix from its start. -/
theorem Steps.halts_tail {a b : Config} {out : String} {code : Nat}
    (hs : Steps a b) : Halts a out code → Halts b out code := by
  induction hs with
  | refl => exact fun hh => hh
  | head first rest ih =>
    intro hh
    exact ih (first.halts_tail hh)

/-- A stuck configuration cannot halt after any number of further steps. -/
theorem Stuck.not_halts {c : Config} (h : Stuck c)
    {out : String} {code : Nat} : ¬ Halts c out code := by
  rintro ⟨last, σf, path, halt, _⟩
  cases path with
  | refl => exact h.no_halt code σf halt
  | head first _ => exact h.no_step _ first

/-- An actual finite stuck prefix rules out every output and exit code. -/
theorem Steps.not_halts_of_stuck {a b : Config}
    (hs : Steps a b) (h : Stuck b) {out : String} {code : Nat} :
    ¬ Halts a out code :=
  fun hh => h.not_halts (hs.halts_tail hh)

#print axioms Step.halts_tail
#print axioms Steps.halts_tail
#print axioms Stuck.not_halts
#print axioms Steps.not_halts_of_stuck

end Vsa.Machine
