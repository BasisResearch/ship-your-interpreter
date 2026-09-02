import Vsa.Sim.TermAssembly
open Vsa Vsa.Sim Vsa.MemRepr
open Std (ExtHashMap)

-- N3 (C): FALSE. two windows [0,0x100) and [0x200,∞) agree; m0 populated on
-- [0,0x100). demand a in gap [0x100,0x200): mq[a]? = m0[a]?. Gap not covered.
-- Adversary: pick a=0x100. m0 = ∅ (so m0[0x100]?=none); mq = insert 0x100 v.
-- Then mq[0x100]? = some v ≠ none = m0[0x100]?. agree holds on both windows
-- since 0x100 ∉ [0,0x100) and 0x100 ∉ [0x200,∞).
def NovelResidC : Prop :=
  ∀ (m0 : ExtHashMap Nat (BitVec 8)),
    (∀ k, k < 0x100 → m0[k]? = some (0x1 : BitVec 8)) →
    ∀ mq : ExtHashMap Nat (BitVec 8),
      (∀ k, k < 0x100 → m0[k]? = mq[k]?) →
      (∀ k, 0x200 ≤ k → m0[k]? = mq[k]?) →
      ∀ a, 0x100 ≤ a ∧ a < 0x200 → mq[a]? = m0[a]?

theorem refuteC : ¬ NovelResidC := by
  intro H
  -- m0 must satisfy the population hyp on [0,0x100). Use m0 that is 0x1 on that
  -- window but we only need m0[0x100]? for the demand. Choose m0 = ∅ won't meet
  -- the population hyp. But population demands m0[k]?=some 1 for k<0x100.
  -- Use m0 = a map that is 1 everywhere < 0x100 and absent at 0x100.
  -- Simplest: m0 = fun ... we need concrete. Build via a "constant-on-prefix".
  -- Use the map that inserts 0..0xff -> 1. That's 256 inserts; instead pick a
  -- DIFFERENT demand address strategy: demand a where BOTH windows constrain
  -- nothing AND m0 population says nothing, but we still need m0[a]? computable.
  sorry
