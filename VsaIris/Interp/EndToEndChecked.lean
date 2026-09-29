import VsaIris.Interp.EndToEnd
import Vsa.Sim.CheckedBoundary

/-!
# The end-to-end theorem with checked program premises

`endToEnd_refinement` from `LoadedU` (`Loaded` without its heap-capacity and
stack-admissibility premises), the cost analysis's bound and the
`programStackFits` checker (`Vsa/Sim/CheckedBoundary.lean`).
-/

open Vsa.While

namespace Vsa.Sim.EndToEnd

open Vsa.Machine (Config Halts Diverges)
open Vsa.Sim.LayoutInstance
open Vsa.Densify (fillZero)

/-- **The end-to-end theorem with checked program premises.** For a program
whose allocation cost the analysis bounds by `B` and which passes
`programStackFits`, loaded with a heap holding `2 * B + extendSlack` free
bytes, the conclusion of `endToEnd_refinement` holds without the
heap-capacity and stack-admissibility premises of `Loaded`. -/
theorem endToEnd_checked (p : Program) (B : Nat) (hB : interpCostBound p = some B)
    (hs : programStackFits p = true) (c : Config) (hL : LoadedU p (fillZero c))
    (hroom : HeapRoom (fillZero c).σ.mem B) :
    (∀ out, BigStep p out ↔ Halts c out 0) ∧ (Diverges c → ¬ ∃ out, BigStep p out) :=
  endToEnd_refinement p c (loaded_of_checked hL hB hs hroom)

#print axioms endToEnd_checked

end Vsa.Sim.EndToEnd
