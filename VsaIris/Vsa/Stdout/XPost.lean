import VsaIris.Vsa.Stdout.Tac
import VsaIris.Interp.XrunAttr

/-!
# Return facts of the stdio summaries for `xrun`

A stdio summary hands its continuation `RetOK R R' a0`: the result register and the kept
registers. `xrun` instantiates these lemmas at the returned hypothesis.
-/

namespace VsaIris.Sym

@[xrun_post] theorem RetOK.a0_eq {R R' : Nat → BitVec 64} {a0 : BitVec 64} (h : RetOK R R' a0) :
    R' 10 = a0 := h.a0

@[xrun_post] theorem RetOK.keep_eq {R R' : Nat → BitVec 64} {a0 : BitVec 64} (h : RetOK R R' a0)
    (x : Nat) (hx : decide (x ∈ iRegs ∧ x ≠ 32 ∧ x ≠ 10 ∧ x ∉ callClob) = true) : R' x = R x := by
  simp only [decide_eq_true_eq] at hx
  exact h.keep x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2

end VsaIris.Sym
