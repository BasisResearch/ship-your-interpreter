import Vsa.Sim.TermAssembly
open Vsa Vsa.Sim Vsa.MemRepr
open Std (ExtHashMap)

def NovelResidC : Prop :=
  ∀ (m0 : ExtHashMap Nat (BitVec 8)),
    (∀ k, k < 0x100 → m0[k]? = some (0x1 : BitVec 8)) →
    ∀ mq : ExtHashMap Nat (BitVec 8),
      (∀ k, k < 0x100 → m0[k]? = mq[k]?) →
      (∀ k, 0x200 ≤ k → m0[k]? = mq[k]?) →
      ∀ a, 0x100 ≤ a ∧ a < 0x200 → mq[a]? = m0[a]?

-- KEY IDEA: keep m0 as a bound var? No, H quantifies m0. But I can pick m0 to be
-- ANY map satisfying population. Corrupt mq at a=0x100 relative to m0.
-- Population hyp: need a concrete m0 with m0[k]?=some 1 for all k<0x100.
-- Trick: instantiate m0 with a map, then DISCHARGE population by... we can't
-- enumerate 256. Instead: choose the demand address a and set mq to DIFFER, and
-- make m0's value at a be forced. mq = m0 with a corrupted. We need m0[a]? known.
-- Use m0 that is 'some 1' on a SUPERSET incl a? No — a is in the gap.
-- Cleanest: m0 := fun-backed? Std.ExtHashMap has no const. 
-- Alternative: WEAKEN — pick m0 arbitrary and prove population is UNSAT? No, it's a hyp we FEED.
-- Resolution: the adversary corrupts mq; m0 stays a var we must SUPPLY meeting population.
-- Build m0 via Nat-indexed: there is no finite map = some 1 on [0,256) unless we insert.
-- So test: does a 256-insert fold elaborate cheaply? Try small proxy first with window <0x4.
example : True := trivial
