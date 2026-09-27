import VsaIris.WhileLogic.WholeProgram
import VsaIris.Interp.EndToEnd

/-!
# Machine-level adequacy of the WHILE program logic

`adequacy_bigStep` composed with `endToEnd_refinement`: a program proved in
the logic from `initOwn` makes every configuration that has it `Loaded` halt
with exit code `0`, printing an output that satisfies the postcondition, and
never diverge. `firstLoop_halts` and `whileWl_halts` are the worked examples'
machine consequences. `Vsa.Sim.Boot.Gen.Proof.loaded` (with `prog_eq`)
supplies the `Loaded` hypothesis of `whileWl_halts` at the proof ELF's real
`interp_run` entry state.
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

/-- **The first loop of `tests/while.wl` at the machine.** Every
configuration that has `firstLoop` loaded halts with exit code `0` after
printing exactly `55\n`, and does not diverge. -/
theorem firstLoop_halts (c : Vsa.Machine.Config)
    (hL : Loaded interpRunLayout Example.firstLoop (fillZero c)) :
    Halts c "55\n" 0 ∧ ¬ Diverges c := by
  obtain ⟨⟨out, h, hout⟩, hd⟩ := adequacy_machine Example.firstLoop_spec c hL
  subst hout
  exact ⟨h, hd⟩

/-- **All of `tests/while.wl` at the machine.** Every configuration that has
`whileWl` loaded halts with exit code `0` after printing exactly
`55\n2500\n36\n`, and does not diverge. -/
theorem whileWl_halts (c : Vsa.Machine.Config)
    (hL : Loaded interpRunLayout Vsa.While.Programs.whileWl (fillZero c)) :
    Halts c Whole.whileOut 0 ∧ ¬ Diverges c := by
  obtain ⟨⟨out, h, hout⟩, hd⟩ := adequacy_machine Whole.whileWl_spec c hL
  subst hout
  exact ⟨h, hd⟩

end Vsa.While.Logic
