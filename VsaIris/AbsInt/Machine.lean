import VsaIris.Interp.EndToEnd
import Vsa.AbsInt.Examples

namespace Vsa.AbsInt.Machine

open Vsa.While Vsa.AbsInt
open Vsa.Machine (Halts Diverges)
open Vsa.Refine (Loaded)
open Vsa.Sim.LayoutInstance (interpRunLayout)
open Vsa.Densify (fillZero)

variable {A : Type} [AbsDom A]

theorem machine_final (cfg : Cfg) {p : Program} {c : Vsa.Machine.Config} {out : String}
    (hL : Loaded interpRunLayout p (fillZero c)) (hH : Halts c out 0) :
    ∃ st', ExecSeq initSt 0 0 p st' .normal ∧ st'.out = out ∧
      SGam [0] st'.store (analyze (A := A) cfg p).norm := by
  obtain ⟨st', hrun, hout⟩ :=
    ((Vsa.Sim.EndToEnd.endToEnd_refinement p c hL).1 out).2 hH
  exact ⟨st', hrun, hout, bigStep_final cfg hrun⟩

theorem machine_global (cfg : Cfg) {p : Program} {c : Vsa.Machine.Config} {out : String}
    (hL : Loaded interpRunLayout p (fillZero c)) (hH : Halts c out 0) :
    ∃ st', ExecSeq initSt 0 0 p st' .normal ∧ st'.out = out ∧
      ∀ x v, st'.store.get? 0 x = some v →
        AbsDom.Gam ((analyze (A := A) cfg p).norm.lookup x).1 v := by
  obtain ⟨st', hrun, hout, hs⟩ := machine_final (A := A) cfg hL hH
  exact ⟨st', hrun, hout, fun x v hx => (SGam.lookup rfl hs).1 v hx⟩

theorem machine_no_halt_of_bot (cfg : Cfg) {p : Program} {c : Vsa.Machine.Config}
    (hL : Loaded interpRunLayout p (fillZero c))
    (hbot : (analyze (A := A) cfg p).norm.isBot = true) (out : String) :
    ¬ Halts c out 0 := fun hH =>
  no_bigStep_of_bot (A := A) cfg hbot out
    (((Vsa.Sim.EndToEnd.endToEnd_refinement p c hL).1 out).2 hH)

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
