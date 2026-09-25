import Vsa.While.CostEval
import Vsa.Sim.DlHeap

/-!
# `capacity` from one evaluator run

`DlHeap.InitialAllocatorAt.capacity` bounds the cost of every terminating
(`.normal`) cost derivation of the represented program. The cost evaluator
(`Vsa.While.CostEval`) is complete for the cost relations, so one run that
finishes decides it: a `done` result fixes the status and the cost of every
derivation, and a `stuck` result rules every derivation out.
-/

namespace Vsa.Sim.Boot

open Vsa.While Vsa.Sim.DlHeap

/-- The evaluator finished within `fuel`, and a normal result fits below `top`. -/
def capOk (fuel : Nat) (p : Program) (top : Nat) : Bool :=
  match execSeqEval fuel initSt 0 0 p with
  | .done r => r.status != .normal || decide (2 * r.n + extendSlack ≤ heapEnd - top)
  | .stuck => true
  | .fuel => false

theorem capacity_of_capOk {fuel : Nat} {p : Program} {top : Nat} (h : capOk fuel p top = true) :
    ∀ st' n, ExecSeqCost initSt 0 0 p st' .normal n → 2 * n + extendSlack ≤ heapEnd - top := by
  intro st' n hd
  unfold capOk at h
  split at h
  · rename_i r hr
    have he := execSeqCost_eq_of_eval hr hd
    subst he
    simp only [bne_self_eq_false, Bool.false_or, decide_eq_true_eq] at h
    exact h
  · rename_i hr
    exact absurd hd (execSeqCost_none_of_stuck hr st' .normal n)
  · cases h

end Vsa.Sim.Boot
