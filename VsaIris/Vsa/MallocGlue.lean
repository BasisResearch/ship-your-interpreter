import VsaIris.Vsa.Carry

namespace VsaIris.VsaHeap

theorem keep6 {R R' : Nat → BitVec 64} {a b c d e f : Nat}
    (h : ∀ x, x ≠ a → x ≠ b → x ≠ c → x ≠ d → x ≠ e → x ≠ f → R' x = R x) (x : Nat)
    (h1 : x ≠ a := by decide) (h2 : x ≠ b := by decide) (h3 : x ≠ c := by decide)
    (h4 : x ≠ d := by decide) (h5 : x ≠ e := by decide) (h6 : x ≠ f := by decide) : R' x = R x :=
  h x h1 h2 h3 h4 h5 h6

end VsaIris.VsaHeap
