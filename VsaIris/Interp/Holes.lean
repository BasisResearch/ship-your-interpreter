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
  /-- The newlib calls on the error paths (`VsaIris/Vsa/Newlib.lean`, H5):
  `snprintf` and `fprintf` with `%s`/`%d` formats and `fwrite` of the
  out-of-memory message, at a post-write state `exit`'s close path runs from.
  `exit`'s newlib interior is proved from it (`Newlib.NewlibCore.full`,
  `VsaIris/Vsa/ExitH/Iris.lean`). -/
  newlib : Newlib.NewlibCore
  /-- newlib's stdout calls (`fputs`, `fputc`, `fwrite`, `fprintf` on
  `stdout`) and `stringify`'s `snprintf` renderings, exact about what they
  print or render (`VsaIris/Vsa/NewlibOut.lean`, H2). -/
  out : Newlib.OutHoles

end VsaIris.Interp
