import VsaIris.WhileLogic.WholeProgram
import VsaIris.Interp.EndToEnd

namespace Vsa.While.Logic

open Iris Vsa.While
open Vsa.Machine (Halts Diverges)
open Vsa.Refine (Loaded)
open Vsa.Sim.LayoutInstance (interpRunLayout)
open Vsa.Densify (fillZero)

theorem adequacy_machine {p : Program} {Q : String → Prop}
    (h : initOwn ⊢ wpSeq 0 0 p (PostOut Q)) (c : Vsa.Machine.Config)
    (hL : Loaded interpRunLayout p (fillZero c)) :
    (∃ out, Halts c out 0 ∧ Q out) ∧ ¬ Diverges c := by
  obtain ⟨out, hbs, hQ⟩ := adequacy_bigStep h
  have hr := Vsa.Sim.EndToEnd.endToEnd_refinement p c hL
  exact ⟨⟨out, (hr.1 out).mp hbs, hQ⟩, fun hd => hr.2 hd ⟨out, hbs⟩⟩

theorem firstLoop_halts (c : Vsa.Machine.Config)
    (hL : Loaded interpRunLayout Example.firstLoop (fillZero c)) :
    Halts c "55\n" 0 ∧ ¬ Diverges c := by
  obtain ⟨⟨out, h, hout⟩, hd⟩ := adequacy_machine Example.firstLoop_spec c hL
  subst hout
  exact ⟨h, hd⟩

theorem whileWl_halts (c : Vsa.Machine.Config)
    (hL : Loaded interpRunLayout Vsa.While.Programs.whileWl (fillZero c)) :
    Halts c Whole.whileOut 0 ∧ ¬ Diverges c := by
  obtain ⟨⟨out, h, hout⟩, hd⟩ := adequacy_machine Whole.whileWl_spec c hL
  subst hout
  exact ⟨h, hd⟩

end Vsa.While.Logic
