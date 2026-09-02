import Vsa.Sim.TermAssembly
open Std (ExtHashMap)
-- FRESH (post-v2.1, never written before): three windows, value-demand at an
-- address in the gap between windows 2 and 3, where m0 does NOT hold the byte
-- (exercises the insert-adversary path). FALSE.
def FreshTriWin : Prop :=
  ∀ (m0 : ExtHashMap Nat (BitVec 8)),
    ∀ mq : ExtHashMap Nat (BitVec 8),
      (∀ k, k < 0x40 → m0[k]? = mq[k]?) →
      (∀ k, 0x80 ≤ k ∧ k < 0xc0 → m0[k]? = mq[k]?) →
      (∀ k, 0x200 ≤ k → m0[k]? = mq[k]?) →
      mq[(0xd0 : Nat)]? = m0[(0xd0 : Nat)]?
-- FRESH TRUE twin: demand inside window 2. Must survive.
def FreshTriWinT : Prop :=
  ∀ (m0 : ExtHashMap Nat (BitVec 8)),
    ∀ mq : ExtHashMap Nat (BitVec 8),
      (∀ k, 0x80 ≤ k ∧ k < 0xc0 → m0[k]? = mq[k]?) →
      mq[(0x90 : Nat)]? = m0[(0x90 : Nat)]?
