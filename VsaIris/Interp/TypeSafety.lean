import VsaIris.Interp.EndToEnd
import Vsa.While.TypeProgress
import Vsa.While.TypeInfer

namespace Vsa.Sim.EndToEnd

open Vsa.While Vsa.While.Types
open Vsa.Machine (Halts Diverges)
open Vsa.Refine (Loaded)
open Vsa.Sim.LayoutInstance (interpRunLayout)
open Vsa.Densify (fillZero)

theorem wellTyped_machine {Δ : TyEnv} {p : Program} {c : Vsa.Machine.Config}
    (hwt : WellTyped Δ p) (hL : Loaded interpRunLayout p (fillZero c)) :
    (∀ out, BigStep p out ↔ Halts c out 0) ∧
    (∀ out e, Halts c out e → e ≠ 0 →
      ExecSeqErrN initSt 0 0 p ∨ BigStepDiverges p) ∧
    (Diverges c → ¬ ∃ out, BigStep p out) := by
  obtain ⟨hbs, hdiv⟩ := endToEnd_refinement p c hL
  refine ⟨hbs, ?_, hdiv⟩
  intro out e hh he
  rcases type_soundness hwt with ⟨out', hb⟩ | herr | hd
  · exact absurd (Halts.deterministic hh ((hbs out').1 hb)).2 he
  · exact .inl herr
  · exact .inr hd

theorem wellTyped_halt_nonzero {Δ : TyEnv} {p : Program} {c : Vsa.Machine.Config}
    (hwt : WellTyped Δ p) (hL : Loaded interpRunLayout p (fillZero c))
    (hterm : ¬ BigStepDiverges p) {out : String} {e : Nat} (hh : Halts c out e)
    (he : e ≠ 0) : ExecSeqErrN initSt 0 0 p :=
  ((wellTyped_machine hwt hL).2.1 out e hh he).resolve_right hterm

theorem whileTyped_machine {p : Program} {c : Vsa.Machine.Config} (hwt : whileTyped p = true)
    (hL : Loaded interpRunLayout p (fillZero c)) :
    (∀ out, BigStep p out ↔ Halts c out 0) ∧
    (∀ out e, Halts c out e → e ≠ 0 →
      ExecSeqErrN initSt 0 0 p ∨ BigStepDiverges p) ∧
    (Diverges c → ¬ ∃ out, BigStep p out) :=
  let ⟨_, h⟩ := whileTyped_iff.mp hwt
  wellTyped_machine h hL

end Vsa.Sim.EndToEnd
