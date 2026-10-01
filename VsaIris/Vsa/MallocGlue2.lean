import VsaIris.Vsa.AllocTac
import Vsa.Sim.DlHeap

namespace VsaIris.Sym

open Lean Elab Tactic

def regClose (hs : Array Term) (strict : Bool) : TacticM Unit := do
  evalTactic (← `(tactic| simp (config := {failIfUnchanged := false}) only
    [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]))
  if (← getUnsolvedGoals).isEmpty then return
  for h in hs do
    let s ← saveState
    try
      evalTactic (← `(tactic| exact $h))
      return
    catch _ => s.restore
  let tac ← `(tactic| first
    | rfl
    | (rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
    | (unfold Vsa.Sim.DlHeap.binAt Vsa.Sim.DlHeap.avAddr; rfl))
  if strict then evalTactic tac else
    let s ← saveState
    try evalTactic tac catch _ => s.restore

elab "reg_close" " [" hs:term,* "]" : tactic => regClose hs.getElems true

elab "reg_try" " [" hs:term,* "]" : tactic => regClose hs.getElems false

end VsaIris.Sym
