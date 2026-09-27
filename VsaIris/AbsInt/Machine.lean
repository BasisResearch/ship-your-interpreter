import VsaIris.Interp.EndToEnd
import Vsa.AbsInt.Examples

/-!
# Abstract interpretation carried to the machine

`endToEnd_refinement` identifies the machine's clean halts with `BigStep`
behaviours, so every result of the abstract interpreter about successful
runs holds of the compiled interpreter running the loaded program:

* `machine_final`: when the machine halts with exit code 0 and output `out`,
  some run of the program prints `out` and ends in a store described by the
  analysis's normal-completion state;
* `machine_no_halt_of_bot`: if the analysis finds normal completion
  unreachable, the machine never halts with exit code 0;
* `whileWl_machine`: for `whileWl`, a clean halt comes from a run whose
  final globals are `sum = 55`, `total = 2500`, `acc = 36`, and no run of the
  program has a runtime error.
-/

namespace Vsa.AbsInt.Machine

open Vsa.While Vsa.AbsInt
open Vsa.Machine (Halts Diverges)
open Vsa.Refine (Loaded)
open Vsa.Sim.LayoutInstance (interpRunLayout)
open Vsa.Densify (fillZero)

variable {A : Type} [AbsDom A]

/-- **Machine corollary.** A clean machine halt of a loaded program comes from
a run whose final store the analysis describes. -/
theorem machine_final (cfg : Cfg) {p : Program} {c : Vsa.Machine.Config} {out : String}
    (hL : Loaded interpRunLayout p (fillZero c)) (hH : Halts c out 0) :
    ∃ st', ExecSeq initSt 0 0 p st' .normal ∧ st'.out = out ∧
      SGam [0] st'.store (analyze (A := A) cfg p).norm := by
  obtain ⟨st', hrun, hout⟩ :=
    ((Vsa.Sim.EndToEnd.endToEnd_refinement p c hL).1 out).2 hH
  exact ⟨st', hrun, hout, bigStep_final cfg hrun⟩

/-- Every global of the final store is in the analysis's abstract value. -/
theorem machine_global (cfg : Cfg) {p : Program} {c : Vsa.Machine.Config} {out : String}
    (hL : Loaded interpRunLayout p (fillZero c)) (hH : Halts c out 0) :
    ∃ st', ExecSeq initSt 0 0 p st' .normal ∧ st'.out = out ∧
      ∀ x v, st'.store.get? 0 x = some v →
        AbsDom.Gam ((analyze (A := A) cfg p).norm.lookup x).1 v := by
  obtain ⟨st', hrun, hout, hs⟩ := machine_final (A := A) cfg hL hH
  exact ⟨st', hrun, hout, fun x v hx => (SGam.lookup rfl hs).1 v hx⟩

/-- If the analysis finds normal completion unreachable, the machine never
halts cleanly. -/
theorem machine_no_halt_of_bot (cfg : Cfg) {p : Program} {c : Vsa.Machine.Config}
    (hL : Loaded interpRunLayout p (fillZero c))
    (hbot : (analyze (A := A) cfg p).norm.isBot = true) (out : String) :
    ¬ Halts c out 0 := fun hH =>
  no_bigStep_of_bot (A := A) cfg hbot out
    (((Vsa.Sim.EndToEnd.endToEnd_refinement p c hL).1 out).2 hH)

/-- **`whileWl` on the machine.** A clean halt of the loaded `whileWl` comes
from an error-free program whose run ends with `sum = 55`, `total = 2500`
and `acc = 36`, printing exactly the machine's output. -/
theorem whileWl_machine {c : Vsa.Machine.Config} {out : String}
    (hL : Loaded interpRunLayout Programs.whileWl (fillZero c)) (hH : Halts c out 0) :
    ¬ BigStepErr Programs.whileWl ∧
      ∃ st', ExecSeq initSt 0 0 Programs.whileWl st' .normal ∧ st'.out = out ∧
        st'.store.get? 0 "sum" = some (.int 55) ∧
        st'.store.get? 0 "total" = some (.int 2500) ∧
        st'.store.get? 0 "acc" = some (.int 36) :=
  ⟨Examples.whileWl_no_error, Examples.whileWl_final
    (((Vsa.Sim.EndToEnd.endToEnd_refinement _ c hL).1 out).2 hH)⟩

end Vsa.AbsInt.Machine
