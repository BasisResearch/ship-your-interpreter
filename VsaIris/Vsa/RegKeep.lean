import VsaIris.Vsa.AllocTac
import VsaIris.Vsa.BvLits
import Vsa.Sim.DlHeap

namespace VsaIris.VsaHeap

theorem keep3 {R R' : Nat → BitVec 64} {a b c : Nat} (h : ∀ x, x ≠ a → x ≠ b → x ≠ c → R' x = R x) (x : Nat)
    (h1 : x ≠ a := by decide) (h2 : x ≠ b := by decide) (h3 : x ≠ c := by decide) : R' x = R x :=
  h x h1 h2 h3

theorem keep4 {R R' : Nat → BitVec 64} {a b c d : Nat}
    (h : ∀ x, x ≠ a → x ≠ b → x ≠ c → x ≠ d → R' x = R x) (x : Nat) (h1 : x ≠ a := by decide)
    (h2 : x ≠ b := by decide) (h3 : x ≠ c := by decide) (h4 : x ≠ d := by decide) : R' x = R x :=
  h x h1 h2 h3 h4

theorem keep6 {R R' : Nat → BitVec 64} {a b c d e f : Nat}
    (h : ∀ x, x ≠ a → x ≠ b → x ≠ c → x ≠ d → x ≠ e → x ≠ f → R' x = R x) (x : Nat)
    (h1 : x ≠ a := by decide) (h2 : x ≠ b := by decide) (h3 : x ≠ c := by decide)
    (h4 : x ≠ d := by decide) (h5 : x ≠ e := by decide) (h6 : x ≠ f := by decide) : R' x = R x :=
  h x h1 h2 h3 h4 h5 h6

syntax "upd_norm" (" [" Lean.Parser.Tactic.simpLemma,* "]")? (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| upd_norm $[$loc]?) => `(tactic| upd_norm [] $[$loc]?)
  | `(tactic| upd_norm [$ts,*] $[$loc]?) =>
    `(tactic| simp (config := {failIfUnchanged := false}) only
      [VsaIris.Sym.upd_apply, Nat.reduceEqDiff, ite_true, ite_false, $ts,*] $[$loc]?)

end VsaIris.VsaHeap

namespace VsaIris.Sym

open Lean Elab Tactic

def regClose (hs : Array Term) (strict : Bool) : TacticM Unit := do
  evalTactic (← `(tactic| simp (config := {failIfUnchanged := false}) only
    [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]))
  if (← getUnsolvedGoals).isEmpty then return
  let nErr := fun (l : MessageLog) => (l.toList.filter (·.severity == .error)).length
  for h in hs do
    let s ← saveState
    let n0 := nErr (← Core.getMessageLog)
    try
      evalTactic (← `(tactic| with_reducible exact $h))
      if nErr (← Core.getMessageLog) == n0 then return
      s.restore
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
