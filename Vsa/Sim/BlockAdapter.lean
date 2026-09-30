import Vsa.Sim.BlockMem
import Vsa.Sim.ValueSpec
import Vsa.Sim.ReprSurvival

open Vsa

namespace Vsa.Sim

theorem applyW_getElem_disjoint (m : Std.ExtHashMap Nat (BitVec 8)) (e : WEntry)
    (k : Nat) (hw : e.2.1 = 1 ∨ e.2.1 = 2 ∨ e.2.1 = 4 ∨ e.2.1 = 8)
    (hdisj : k < e.1 ∨ e.1 + e.2.1 ≤ k) : (applyW m e)[k]? = m[k]? := by
  obtain ⟨a, w, d⟩ := e
  have hw' : w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8 := hw
  have hdisj' : k < a ∨ a + w ≤ k := hdisj
  rcases hw' with h | h | h | h <;> subst h
  · show (m.insert a (sbData d))[k]? = m[k]?
    exact getElem_insert_ne m k a (sbData d) (by simp only [beq_eq_false_iff_ne, ne_eq]; omega)
  · show ((m.insert a ((shData d).extractLsb' 0 8)).insert (a + 1)
        ((shData d).extractLsb' 8 8))[k]? = m[k]?
    exact getElem_writeMap2_disjoint m a k (shData d) (by omega)
  · show (writeMap4 m a (swData d))[k]? = m[k]?
    exact getElem_writeMap4_disjoint m a k (swData d) (by omega)
  · show (writeMap8 m a (sdData_val d))[k]? = m[k]?
    exact getElem_writeMap8_disjoint m a k (sdData_val d) (by omega)

end Vsa.Sim
