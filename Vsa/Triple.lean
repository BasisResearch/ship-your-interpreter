import Vsa.Machine

namespace Vsa.Machine

theorem Steps.trans {a b c : Config} (h₁ : Steps a b) (h₂ : Steps b c) :
    Steps a c := by
  induction h₁ with
  | refl => exact h₂
  | head s _ ih => exact .head s (ih h₂)

theorem Steps.single {a b : Config} (h : Step a b) : Steps a b :=
  .head h (.refl b)

end Vsa.Machine

namespace Vsa.Logic

open Vsa.Machine

def Triple (P Q : Config → Prop) : Prop :=
  ∀ c, P c → ∃ c', Steps c c' ∧ Q c'

def TripleN (n : Nat) (P Q : Config → Prop) : Prop :=
  ∀ c, P c → ∃ m c', n ≤ m ∧ StepsN m c c' ∧ Q c'

namespace Triple

theorem of_imp {P Q : Config → Prop} (h : ∀ c, P c → Q c) : Triple P Q :=
  fun c hc => ⟨c, .refl c, h c hc⟩

theorem rfl {P : Config → Prop} : Triple P P := of_imp fun _ h => h

theorem conseq {P P' Q Q' : Config → Prop} (h : Triple P Q)
    (hP : ∀ c, P' c → P c) (hQ : ∀ c, Q c → Q' c) : Triple P' Q' := by
  intro c hc
  obtain ⟨c', hs, hq⟩ := h c (hP c hc)
  exact ⟨c', hs, hQ c' hq⟩

theorem seq {P Q R : Config → Prop} (h₁ : Triple P Q) (h₂ : Triple Q R) :
    Triple P R := by
  intro c hc
  obtain ⟨c₁, hs₁, hq⟩ := h₁ c hc
  obtain ⟨c₂, hs₂, hr⟩ := h₂ c₁ hq
  exact ⟨c₂, hs₁.trans hs₂, hr⟩

theorem cases {P₁ P₂ Q : Config → Prop} (h₁ : Triple P₁ Q)
    (h₂ : Triple P₂ Q) : Triple (fun c => P₁ c ∨ P₂ c) Q := by
  intro c hc
  cases hc with
  | inl h => exact h₁ c h
  | inr h => exact h₂ c h

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

theorem loop {I B : Config → Prop} (μ : Config → Nat)
    (body : ∀ n, Triple (fun c => I c ∧ B c ∧ μ c = n)
                        (fun c => I c ∧ μ c < n)) :
    Triple I (fun c => I c ∧ ¬ B c) :=
  fun c hI => loop_aux μ body (μ c) c (Nat.le_refl _) hI

end Triple

namespace TripleN

theorem mono {m n : Nat} {P Q : Config → Prop} (hmn : m ≤ n)
    (h : TripleN n P Q) : TripleN m P Q := by
  intro c hc
  obtain ⟨k, c', hk, hs, hq⟩ := h c hc
  exact ⟨k, c', Nat.le_trans hmn hk, hs, hq⟩

end TripleN

end Vsa.Logic
