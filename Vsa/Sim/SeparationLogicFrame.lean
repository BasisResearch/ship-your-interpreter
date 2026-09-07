import Vsa.Sim.SeparationLogic

open Vsa.MemRepr

namespace Vsa.Sim.SeparationLogic

/-- The framed resource cannot contain a byte writable by the local resource. -/
theorem Compatible.frame_readable {left right : Resource} (h : Compatible left right)
    {k : Nat} (hk : right.support k) : ¬ left.write k := by
  intro hw
  rcases hk with hr | hr
  · exact h.write_write k hw hr
  · exact h.write_read k hw hr

/-- The semantic frame rule at a concrete resource split. The local post and
actual preservation outside local writes retain every framed assertion. -/
theorem frame_at_split {P R : Assertion} {m m' : Mem} {left right whole : Resource}
    (hs : Split left right whole) (hp : P m' left) (hr : R m right)
    (hmem : AgreeP (fun k => ¬ left.write k) m m') :
    (P ∗ R) m' whole := by
  refine ⟨left, right, hs, hp, ?_⟩
  exact R.stable (fun k hk => hmem k (hs.compatible.frame_readable hk)) hr

/-- A relational Hoare judgment with unchanged permissions. A result exists,
and every result satisfies the post and preserves read-only/framed memory.
This endpoint relation does not model divergent executions. Allocation rules
must additionally justify their permission changes. -/
structure Hoare (command : Mem → Mem → Prop) (P Q : Assertion) : Prop where
  existsResult : ∀ m r, P m r → ∃ m', command m m'
  correct : ∀ m m' r, P m r → command m m' → Q m' r
  preserves : ∀ m m' r, P m r → command m m' →
    AgreeP (fun k => ¬ r.write k) m m'

/-- General separating-conjunction frame rule. -/
theorem Hoare.frame {command : Mem → Mem → Prop} {P Q : Assertion}
    (h : Hoare command P Q) (R : Assertion) : Hoare command (P ∗ R) (Q ∗ R) where
  existsResult m _ hp := by
    obtain ⟨left, _, _, hp, _⟩ := hp
    exact h.existsResult m left hp
  correct m m' _ hp hc := by
    obtain ⟨left, right, hs, hp, hr⟩ := hp
    exact frame_at_split hs (h.correct m m' left hp hc) hr (h.preserves m m' left hp hc)
  preserves m m' whole hp hc := by
    obtain ⟨left, _, hs, hp, _⟩ := hp
    intro k hk
    exact h.preserves m m' left hp hc k
      (fun hw => hk ((hs.write k).mpr (Or.inl hw)))

theorem Hoare.consequence {command : Mem → Mem → Prop} {P P' Q Q' : Assertion}
    (h : Hoare command P Q) (hpre : P' ⊢ₛ P) (hpost : Q ⊢ₛ Q') :
    Hoare command P' Q' where
  existsResult m r hp := h.existsResult m r (hpre m r hp)
  correct m m' r hp hc := hpost m' r (h.correct m m' r (hpre m r hp) hc)
  preserves m m' r hp hc := h.preserves m m' r (hpre m r hp) hc

/-- Relational sequential composition retains all possible intermediate states. -/
def sequence (first second : Mem → Mem → Prop) (m m' : Mem) : Prop :=
  ∃ middle, first m middle ∧ second middle m'

theorem Hoare.sequence {first second : Mem → Mem → Prop} {P Q R : Assertion}
    (hfirst : Hoare first P Q) (hsecond : Hoare second Q R) :
    Hoare (sequence first second) P R where
  existsResult m r hp := by
    obtain ⟨middle, hf⟩ := hfirst.existsResult m r hp
    obtain ⟨last, hs⟩ := hsecond.existsResult middle r (hfirst.correct m middle r hp hf)
    exact ⟨last, middle, hf, hs⟩
  correct m m' r hp hc := by
    obtain ⟨middle, hf, hs⟩ := hc
    exact hsecond.correct middle m' r (hfirst.correct m middle r hp hf) hs
  preserves m m' r hp hc := by
    obtain ⟨middle, hf, hs⟩ := hc
    exact (hfirst.preserves m middle r hp hf).trans
      (hsecond.preserves middle m' r (hfirst.correct m middle r hp hf) hs)

/-- A single concrete byte update in the same memory map used by the machine. -/
def storeByte (a : Nat) (b : BitVec 8) (m m' : Mem) : Prop := m' = m.insert a b

theorem storeByte_spec (a : Nat) (old new : BitVec 8) :
    Hoare (storeByte a new) (pointsTo a old) (pointsTo a new) where
  existsResult m _ _ := ⟨m.insert a new, rfl⟩
  correct m m' r hp hc := by
    obtain ⟨hr, _⟩ := hp
    subst m'
    exact ⟨hr, by simp⟩
  preserves m m' r hp hc := by
    obtain ⟨hr, _⟩ := hp
    subst m'
    subst r
    intro k hk
    have hne : k ≠ a := hk
    simp [Std.ExtHashMap.getElem?_insert, Ne.symm hne]

#print axioms Compatible.frame_readable
#print axioms frame_at_split
#print axioms Hoare.frame
#print axioms Hoare.consequence
#print axioms Hoare.sequence
#print axioms storeByte_spec

end Vsa.Sim.SeparationLogic
