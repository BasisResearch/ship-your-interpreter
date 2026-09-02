import SmtReplaySupport
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

namespace SmtReplayProbe
open Vsa.SmtReplay
private def m0W : Mem := (∅ : Mem).insert 819 (7#8)
set_option maxHeartbeats 2000000 in
theorem refuted : ¬ FreshValDemand := by
  intro H
  have hm0 : m0W[(819 : Nat)]? = some (7 : BitVec 8) := by
    simp only [m0W]; exact Std.ExtHashMap.getElem?_insert_self
  have hag0 : (∀ k, 0x400 ≤ k ∧ k < 0x500 → (m0W[k]? : Option (BitVec 8)) = (∅ : Mem)[k]?) := by
    intro k hk
    have hkA : k ≠ 819 := by
      intro he; subst he; first | omega | exact hk (by omega)
    rw [show (m0W[k]? : Option (BitVec 8)) = none from by
          simp only [m0W]
          rw [getElem?_insert_out (∅ : Mem) 819 (7#8) k hkA]
          simp only [Std.ExtHashMap.getElem?_empty]]
    simp only [Std.ExtHashMap.getElem?_empty]
  have hc := H m0W  hm0 (∅ : Mem) hag0
  have hE : ((∅ : Mem)[(819:Nat)]? : Option (BitVec 8)) = none := by
    simp only [Std.ExtHashMap.getElem?_empty]
  rw [hE] at hc
  exact absurd hc (by simp)
#print axioms refuted
end SmtReplayProbe
