import Vsa.Sim.DeriveMeta

/-! Smoke test for `#derive_destructurer` on a tiny synthetic tower. -/

namespace Vsa.Sim.DeriveMetaSmoke

def Tower (a b : Nat) (p : Prop) : Prop :=
  a = 0 ∧ (∃ k, k = b) ∧ p ∧ b < 5

#derive_destructurer Tower

-- The generated structure + isos should exist and be usable by name:
example (a b : Nat) (p : Prop) (h : Tower a b p) : b < 5 :=
  (Tower.destruct a b p h).p4

example (a b : Nat) (p : Prop)
    (h1 : a = 0) (h2 : ∃ k, k = b) (h3 : p) (h4 : b < 5) : Tower a b p :=
  Tower.mk' a b p ⟨h1, h2, h3, h4⟩

#print axioms Tower.destruct
#print axioms Tower.mk'

end Vsa.Sim.DeriveMetaSmoke
