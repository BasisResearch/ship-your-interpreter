import VsaIris.Vsa.BinDom
import VsaIris.Interp.Code

/-!
# `interpText` is a slice of the fixed image

Every byte of the interpreter's code and jump tables is the fixed binary's
`.text` or `.rodata` byte at its address (one kernel `decide`). Consumers:
`binImg_textOwn` (the boundary's code resource) and the stdout runs' data
views (`Fprintf/Out.lean`).
-/

namespace VsaIris.Interp

open VsaIris.Sym VsaIris.Newlib

theorem interpText_img :
    interpText.all (fun p =>
      (decide (textDom p.1) && textByte p.1 == p.2) ||
        (decide (rodataDom p.1) && rodataByte p.1 == p.2)) = true := by
  decide +kernel

theorem interpText_img_mem :
    ∀ p ∈ interpText, (textDom p.1 ∧ textByte p.1 = p.2) ∨
      (rodataDom p.1 ∧ rodataByte p.1 = p.2) := by
  intro p hp
  have h := List.all_eq_true.1 interpText_img p hp
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact h

end VsaIris.Interp
