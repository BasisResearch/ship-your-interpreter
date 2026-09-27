import Vsa.Machine

/-!
# Layer 1: a total-correctness program logic over `Machine.Step`

PLAN-InterpSim.md Layer 1: `Triple P Q` says every configuration satisfying
`P` reaches (in finitely many architectural steps) a configuration
satisfying `Q` — total correctness, since the existence of the run is part
of the claim. The logic is fully model-independent: everything here is by
induction over `Steps`/`StepsN`, never by unfolding the Sail model.

`TripleN n P Q` additionally counts steps (the run has length ≥ `n`); it
feeds Layer 5's divergence simulation, where an `Approx n` spec derivation
must be mapped to at least `n` machine steps.

Framing is deliberately *not* a rule of the logic: per the plan, every
Layer-3 spec carries "memory outside this footprint is unchanged" inside
`P`/`Q` themselves, with disjointness discharged by the memory-map lemmas.
The conditional rule is the disjunction split (`Triple.cases`): machine-level
branches land in one of two precondition disjuncts, decided by the
step-characterization lemmas, not by the logic.
-/

namespace Vsa.Machine

/-- `Steps` is transitive (Machine.lean provides only `refl`/`head`). -/
theorem Steps.trans {a b c : Config} (h₁ : Steps a b) (h₂ : Steps b c) :
    Steps a c := by
  induction h₁ with
  | refl => exact h₂
  | head s _ ih => exact .head s (ih h₂)

/-- A single step is a `Steps` run. -/
theorem Steps.single {a b : Config} (h : Step a b) : Steps a b :=
  .head h (.refl b)

end Vsa.Machine

namespace Vsa.Logic

open Vsa.Machine

/-- Total-correctness triple over the machine: from every `P`-configuration,
some finite run reaches a `Q`-configuration. -/
def Triple (P Q : Config → Prop) : Prop :=
  ∀ c, P c → ∃ c', Steps c c' ∧ Q c'

/-- Step-counting triple: the reached run has length at least `n`. -/
def TripleN (n : Nat) (P Q : Config → Prop) : Prop :=
  ∀ c, P c → ∃ m c', n ≤ m ∧ StepsN m c c' ∧ Q c'

namespace Triple

/-- Zero-step rule: a pure implication is a triple. -/
theorem of_imp {P Q : Config → Prop} (h : ∀ c, P c → Q c) : Triple P Q :=
  fun c hc => ⟨c, .refl c, h c hc⟩

/-- Reflexivity. -/
theorem rfl {P : Config → Prop} : Triple P P := of_imp fun _ h => h

/-- Consequence: strengthen the precondition, weaken the postcondition. -/
theorem conseq {P P' Q Q' : Config → Prop} (h : Triple P Q)
    (hP : ∀ c, P' c → P c) (hQ : ∀ c, Q c → Q' c) : Triple P' Q' := by
  intro c hc
  obtain ⟨c', hs, hq⟩ := h c (hP c hc)
  exact ⟨c', hs, hQ c' hq⟩

/-- Sequencing: run to `Q`, then from `Q` to `R`. -/
theorem seq {P Q R : Config → Prop} (h₁ : Triple P Q) (h₂ : Triple Q R) :
    Triple P R := by
  intro c hc
  obtain ⟨c₁, hs₁, hq⟩ := h₁ c hc
  obtain ⟨c₂, hs₂, hr⟩ := h₂ c₁ hq
  exact ⟨c₂, hs₁.trans hs₂, hr⟩

/-- Conditional split: both branch preconditions reach the same
postcondition. Machine conditionals land in one disjunct via the branch
step-characterization lemmas. -/
theorem cases {P₁ P₂ Q : Config → Prop} (h₁ : Triple P₁ Q)
    (h₂ : Triple P₂ Q) : Triple (fun c => P₁ c ∨ P₂ c) Q := by
  intro c hc
  cases hc with
  | inl h => exact h₁ c h
  | inr h => exact h₂ c h

/-- Total-correctness loop rule, bounded form: induction on an upper bound
of the measure (plain `Nat` induction — no strong-recursion dependency). -/
private theorem loop_aux {I B : Config → Prop} (μ : Config → Nat)
    (body : ∀ n, Triple (fun c => I c ∧ B c ∧ μ c = n)
                        (fun c => I c ∧ μ c < n)) :
    ∀ n c, μ c ≤ n → I c → ∃ c', Steps c c' ∧ (I c' ∧ ¬ B c') := by
  intro n
  induction n with
  | zero =>
    intro c hμ hI
    by_cases hB : B c
    · obtain ⟨c₁, _, _, hlt⟩ := body (μ c) c ⟨hI, hB, _root_.rfl⟩
      exact absurd (Nat.lt_of_lt_of_le hlt hμ) (Nat.not_lt_zero _)
    · exact ⟨c, .refl c, hI, hB⟩
  | succ n ih =>
    intro c hμ hI
    by_cases hB : B c
    · obtain ⟨c₁, hs₁, hI₁, hlt⟩ := body (μ c) c ⟨hI, hB, _root_.rfl⟩
      obtain ⟨c₂, hs₂, hq⟩ :=
        ih c₁ (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt hμ)) hI₁
      exact ⟨c₂, hs₁.trans hs₂, hq⟩
    · exact ⟨c, .refl c, hI, hB⟩

/-- Total-correctness loop rule. `I` is the invariant, `B` the loop guard,
`μ` the decreasing measure: every guarded iteration re-establishes `I`
strictly decreasing `μ`, so the loop reaches `I ∧ ¬B`. Classical in `B`
(the guard need not be decidable at this level; the machine decides it). -/
theorem loop {I B : Config → Prop} (μ : Config → Nat)
    (body : ∀ n, Triple (fun c => I c ∧ B c ∧ μ c = n)
                        (fun c => I c ∧ μ c < n)) :
    Triple I (fun c => I c ∧ ¬ B c) :=
  fun c hI => loop_aux μ body (μ c) c (Nat.le_refl _) hI

end Triple

namespace TripleN

/-- Weaken the step bound. -/
theorem mono {m n : Nat} {P Q : Config → Prop} (hmn : m ≤ n)
    (h : TripleN n P Q) : TripleN m P Q := by
  intro c hc
  obtain ⟨k, c', hk, hs, hq⟩ := h c hc
  exact ⟨k, c', Nat.le_trans hmn hk, hs, hq⟩

end TripleN

end Vsa.Logic
