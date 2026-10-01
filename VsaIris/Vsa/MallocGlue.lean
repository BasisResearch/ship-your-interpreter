import VsaIris.Vsa.AllocTac
import VsaIris.Vsa.BvLits

namespace VsaIris.VsaHeap

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
