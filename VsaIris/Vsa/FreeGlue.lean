namespace VsaIris.VsaHeap

theorem keep3 {R R' : Nat → BitVec 64} {a b c : Nat} (h : ∀ x, x ≠ a → x ≠ b → x ≠ c → R' x = R x) (x : Nat)
    (h1 : x ≠ a := by decide) (h2 : x ≠ b := by decide) (h3 : x ≠ c := by decide) : R' x = R x :=
  h x h1 h2 h3

end VsaIris.VsaHeap
