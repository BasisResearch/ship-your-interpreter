import VsaIris.Vsa.Fprintf.Strlen

/-! The string leaves' code (`strCode`) is in the stdio table's code: one kernel
`decide` over both lists (lane N3). -/

namespace VsaIris.Sym

open VsaIris.Interp

theorem strCode_stdio_all : strCode.all (fun p => stdioText.contains p) = true := by
  decide +kernel

/-- The string leaves' code is in the stdio table's code. -/
theorem strCode_stdio : ∀ p ∈ strCode, p ∈ stdioText := fun p hp => by
  have := List.all_eq_true.1 strCode_stdio_all p hp
  simpa using this

end VsaIris.Sym
