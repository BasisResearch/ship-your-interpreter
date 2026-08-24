import Vsa.Elf

/-!
# The RISC-V machine as an inductive transition relation

The Sail-generated RV64D model *is* the ISA semantics; this file presents it
as an inductive small-step relation on machine configurations (the graph of
one architectural step), and defines observable behaviors on top of it:
halting with an output/exit code, and divergence. Nothing here executes
anything — behaviors are `Prop`s over the relation, and all lemmas
(determinism, uniqueness of halting behavior, divergence vs halting) are
proved by ordinary induction.

A configuration carries the Sail sequential state plus the platform loop's
bookkeeping (clock-tick counter and step count), exactly the data threaded
by the reference emulator's top-level loop.
-/

namespace Vsa.Machine

open Sail ConcurrencyInterfaceV1 LeanRV64DExecutable

/-- Machine state of the Sail RV64D model: registers, memory, HTIF output. -/
abbrev MState := SequentialState RegisterType trivialChoiceSource

/-- A configuration of the top-level machine loop. -/
structure Config where
  σ : MState
  /-- instructions since the last clock tick (the platform ticks the clock
  every `plat_insns_per_tick` retired instructions). -/
  tick : Nat
  /-- architectural steps taken so far. -/
  steps : Nat

/-- Everything the machine has printed on the HTIF console. -/
def output (σ : MState) : String := String.join σ.sailOutput.toList

/-- **One step of the RISC-V ISA**, as an inductive relation: the graph of
the Sail model's step (`stepOnce` = HTIF-exit check + `try_step` + clock
bookkeeping, exactly the reference emulator loop body). -/
inductive Step : Config → Config → Prop where
  | mk {σ σ' : MState} {i i' u u' : Nat} :
    (stepOnce i u).run σ = .ok (.inr (i', u')) σ' →
    Step ⟨σ, i, u⟩ ⟨σ', i', u'⟩

/-- The machine has signalled exit through HTIF with code `e`; `σ'` is the
final state (whose `output` is the completed console output). -/
inductive Halted : Config → Nat → MState → Prop where
  | mk {σ σ' : MState} {i u e n : Nat} :
    (stepOnce i u).run σ = .ok (.inl (some e, n)) σ' →
    Halted ⟨σ, i, u⟩ e σ'

/-- Reflexive-transitive closure of `Step`. -/
inductive Steps : Config → Config → Prop where
  | refl (c : Config) : Steps c c
  | head {a b c : Config} : Step a b → Steps b c → Steps a c

/-- Exactly `n` steps. -/
inductive StepsN : Nat → Config → Config → Prop where
  | zero (c : Config) : StepsN 0 c c
  | succ {n : Nat} {a b c : Config} : Step a b → StepsN n b c → StepsN (n + 1) a c

/-- Observable halting behavior: the machine runs to a configuration that
signals HTIF exit `e` having printed `out`. -/
def Halts (c : Config) (out : String) (e : Nat) : Prop :=
  ∃ c' σf, Steps c c' ∧ Halted c' e σf ∧ output σf = out

/-- Divergence: the machine can always take another step. -/
def Diverges (c : Config) : Prop := ∀ n, ∃ c', StepsN n c c'

/-! ## Determinism

`Step` and `Halted` are graphs of the same function, so the machine is
deterministic and cannot both step and halt. Everything observable follows
by induction over `Steps`. -/

theorem Step.deterministic {a b b' : Config} (h : Step a b) (h' : Step a b') :
    b = b' := by
  cases h with | mk e =>
  cases h' with | mk e' =>
  rw [e] at e'
  cases e'
  rfl

theorem Halted.deterministic {a : Config} {e e' : Nat} {σ σ' : MState}
    (h : Halted a e σ) (h' : Halted a e' σ') : e = e' ∧ σ = σ' := by
  cases h with | mk he =>
  cases h' with | mk he' =>
  rw [he] at he'
  cases he'
  exact ⟨rfl, rfl⟩

theorem Step.not_halted {a b : Config} {e : Nat} {σ : MState}
    (h : Step a b) (h' : Halted a e σ) : False := by
  cases h with | mk he =>
  cases h' with | mk he' =>
  rw [he] at he'
  cases he'

/-- A configuration that halts takes no steps: any `Steps` run out of it is
empty. -/
theorem Steps.halted_start {a b : Config} {e : Nat} {σ : MState}
    (hs : Steps a b) (h : Halted a e σ) : b = a := by
  cases hs with
  | refl => rfl
  | head s _ => exact (s.not_halted h).elim

/-- Two runs from the same configuration that both end halted end in the
same configuration. Induction over the first run, peeling matched steps off
both by determinism. -/
theorem Steps.confluence_halted {a c₁ c₂ : Config} {e₁ e₂ : Nat}
    {σ₁ σ₂ : MState}
    (hs₁ : Steps a c₁) (hh₁ : Halted c₁ e₁ σ₁)
    (hs₂ : Steps a c₂) (hh₂ : Halted c₂ e₂ σ₂) : c₁ = c₂ := by
  induction hs₁ generalizing c₂ with
  | refl => exact (hs₂.halted_start hh₁).symm
  | head s hs ih =>
    cases hs₂ with
    | refl => exact (s.not_halted hh₂).elim
    | head s' hs₂' =>
      obtain rfl := s.deterministic s'
      exact ih hh₁ hs₂' hh₂

/-- Halting behavior (output and exit code) is unique. -/
theorem Halts.deterministic {c : Config} {out out' : String} {e e' : Nat}
    (h : Halts c out e) (h' : Halts c out' e') : out = out' ∧ e = e' := by
  obtain ⟨c₁, σ₁, hs₁, hh₁, ho₁⟩ := h
  obtain ⟨c₂, σ₂, hs₂, hh₂, ho₂⟩ := h'
  obtain rfl := hs₁.confluence_halted hh₁ hs₂ hh₂
  obtain ⟨he, hσ⟩ := hh₁.deterministic hh₂
  subst hσ
  exact ⟨ho₁.symm.trans ho₂, he⟩

/-- A run of `n` steps ending halted cannot be extended to `n + 1` steps:
peel matched steps off both runs by determinism. -/
theorem StepsN.halted_no_extension {e : Nat} {σ : MState} :
    ∀ {n : Nat} {a b c'' : Config}, StepsN n a b → Halted b e σ →
      StepsN (n + 1) a c'' → False := by
  intro n
  induction n with
  | zero =>
    intro a b c'' h1 hh h2
    cases h1
    cases h2 with | succ s _ => exact s.not_halted hh
  | succ n ih =>
    intro a b c'' h1 hh h2
    cases h1 with | succ s1 h1 =>
    cases h2 with | succ s2 h2 =>
    obtain rfl := s1.deterministic s2
    exact ih h1 hh h2

/-- Every finite run embeds into `StepsN`. -/
theorem Steps.toN {a b : Config} (hs : Steps a b) : ∃ n, StepsN n a b := by
  induction hs with
  | refl => exact ⟨0, .zero _⟩
  | head s _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, .succ s hn⟩

/-- A diverging configuration has no halting behavior. -/
theorem Diverges.not_halts {c : Config} (hd : Diverges c) {out : String}
    {e : Nat} (h : Halts c out e) : False := by
  obtain ⟨c', σf, hs, hh, _⟩ := h
  obtain ⟨n, hn⟩ := hs.toN
  obtain ⟨c'', hn'⟩ := hd (n + 1)
  exact hn.halted_no_extension hh hn'

end Vsa.Machine
