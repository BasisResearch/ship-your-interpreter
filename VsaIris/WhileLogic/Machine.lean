import VsaIris.WhileLogic.Adequacy
import VsaIris.Interp.EndToEnd

/-!
# Machine-level adequacy of the WHILE program logic

`adequacy_bigStep` composed with `endToEnd_refinement`: a program proved in
the logic from `initOwn` makes every configuration that has it `Loaded` halt
with exit code `0`, printing an output that satisfies the postcondition, and
never diverge.
-/

namespace Vsa.While.Logic

open Iris Vsa.While
open Vsa.Machine (Halts Diverges)
open Vsa.Refine (Loaded)
open Vsa.Sim.LayoutInstance (interpRunLayout)
open Vsa.Densify (fillZero)

/-- **Adequacy (machine).** With `endToEnd_refinement`: every configuration
loaded with `p` halts with exit code `0`, printing an output that satisfies
`Q`, and does not diverge. -/
theorem adequacy_machine {p : Program} {Q : String → Prop}
    (h : initOwn ⊢ wpSeq 0 0 p (PostOut Q)) (c : Vsa.Machine.Config)
    (hL : Loaded interpRunLayout p (fillZero c)) :
    (∃ out, Halts c out 0 ∧ Q out) ∧ ¬ Diverges c := by
  obtain ⟨out, hbs, hQ⟩ := adequacy_bigStep h
  have hr := Vsa.Sim.EndToEnd.endToEnd_refinement p c hL
  exact ⟨⟨out, (hr.1 out).mp hbs, hQ⟩, fun hd => hr.2 hd ⟨out, hbs⟩⟩

end Vsa.While.Logic
