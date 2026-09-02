import Vsa.Sim.TermAssembly
open Std (ExtHashMap)
-- Written 2026-09-02 post-encoder-v2: value-demand for a byte m0 need not
-- contain, single positive window, demand outside it. FALSE.
def FreshValDemand : Prop :=
  ∀ (m0 : ExtHashMap Nat (BitVec 8)),
    m0[(0x333 : Nat)]? = some (0x7 : BitVec 8) →
    ∀ mq : ExtHashMap Nat (BitVec 8),
      (∀ k, 0x400 ≤ k ∧ k < 0x500 → m0[k]? = mq[k]?) →
      mq[(0x333 : Nat)]? = some (0x7 : BitVec 8)
