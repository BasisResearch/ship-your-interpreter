import VsaIris.Vsa.Newlib
import VsaIris.Vsa.NewlibOut

/-!
# `IrisHoles`: the assumptions the end-to-end theorem keeps

INTERP_DESIGN.md §9, user decisions Q2/Q4. Every field is an exact Iris
statement of newlib code the interpreter calls (every WP, every Iris
instance), scheduled after E1-E6, and has a row in `VsaIris/HOLES.md`
(`scripts/check_iris_holes.py` checks the two agree). Nothing else is assumed:
the allocator's runs, the string routines, `setjmp`/`longjmp` and the
interpreter's code are proved.
-/

namespace VsaIris.Interp

/-- **The named holes of the final theorem.** -/
structure IrisHoles : Prop where
  /-- The newlib call on the error paths (`VsaIris/Vsa/Newlib.lean`, H5):
  `snprintf` with `%s`/`%d` formats, at a post-write state `exit`'s close
  path runs from. `fwrite`, `fprintf` (`VsaIris/Vsa/Stderr/`) and `exit`'s
  newlib interior are proved (`Newlib.NewlibCore.full`,
  `VsaIris/Vsa/ExitH/Iris.lean`). -/
  newlib : Newlib.NewlibCore

end VsaIris.Interp
