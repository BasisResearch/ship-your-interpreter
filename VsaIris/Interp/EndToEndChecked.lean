import VsaIris.Interp.EndToEnd
import Vsa.Sim.CheckedBoundary

open Vsa.While

namespace Vsa.Sim.EndToEnd

open Vsa.Machine (Config Halts Diverges)
open Vsa.Sim.LayoutInstance
open Vsa.Densify (fillZero)

theorem endToEnd_checked (p : Program) (B : Nat) (hB : interpCostBound p = some B)
    (hs : programStackFits p = true) (c : Config) (hL : LoadedU p (fillZero c))
    (hroom : HeapRoom (fillZero c).σ.mem B) :
    (∀ out, BigStep p out ↔ Halts c out 0) ∧ (Diverges c → ¬ ∃ out, BigStep p out) :=
  endToEnd_refinement p c (loaded_of_checked hL hB hs hroom)

#print axioms endToEnd_checked

end Vsa.Sim.EndToEnd
