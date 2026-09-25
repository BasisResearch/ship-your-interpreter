import VsaIris.Interp.StrcpyRun
import VsaIris.Interp.StrIris
import VsaIris.Interp.HelperRun
import VsaIris.Interp.SpecStringify

/-!
# `strcpy`'s register permutation (lane A)

The `strcpy` specs (`strcpySpec`, `strcpyHeapSpec`) are proved in
`ProofStrcpyH.lean`; their destinations lie above the HTIF words
(`htifLo + 16 ≤ dst`), where VSA's store facts hold.
-/

namespace VsaIris.Interp.StrLeaf

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Inst.Strlen VsaIris.Newlib
open Vsa.Sim Vsa.MemRepr

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

theorem argClob_perm' : (12 :: VsaIris.Interp.argClob).Perm ([12, 13, 14, 15, 16] ++ retRest) := by
  decide

end

end VsaIris.Interp.StrLeaf
