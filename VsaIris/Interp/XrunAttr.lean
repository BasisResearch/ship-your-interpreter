import Lean

/-- Facts `xrun` derives from a summary's return hypothesis: a lemma `L (h : P) : R' k = v`, or
`L (h : P) (x : Nat) (hx : decide c = true) : R' x = R x` (instantiated at every register for
which `hx` is decided). -/
register_label_attr xrun_post
