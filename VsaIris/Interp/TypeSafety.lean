import VsaIris.Interp.EndToEnd
import Vsa.While.TypeProgress
import Vsa.While.TypeInfer

/-!
# Type safety of the interpreter binary

`endToEnd_refinement` relates a WHILE program loaded in the interpreter to the
machine: exit code `0` with output `out` exactly when `BigStep p out`. Every
runtime error of the interpreter exits with the same nonzero code, so the
machine does not separate type errors from other errors. Combined with type
soundness (`type_soundness`), a nonzero halt of a well-typed program is
accounted for by division or remainder by zero, a failed `assert`, or the
call-depth cap (`ExecSeqErrN`), or else the program diverges at the source
level (`BigStepDiverges`). `endToEnd_refinement` does not relate source-level
divergence to machine halting, so that disjunct remains.
-/

namespace Vsa.Sim.EndToEnd

open Vsa.While Vsa.While.Types
open Vsa.Machine (Halts Diverges)
open Vsa.Refine (Loaded)
open Vsa.Sim.LayoutInstance (interpRunLayout)
open Vsa.Densify (fillZero)

/-- **Machine-level type safety.** For a well-typed program `p` loaded in `c`:
the machine exits with code `0` and output `out` exactly for the big-step
behaviours of `p`; a machine that halts with a nonzero exit code runs a
program that reaches a non-type runtime error (division or remainder by zero,
a failed `assert`, or the call-depth cap) or diverges at the source level;
and a diverging machine runs a program with no big-step behaviour. -/
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

/-- A nonzero halt of a well-typed, source-terminating program is a non-type
runtime error. -/
theorem wellTyped_halt_nonzero {Δ : TyEnv} {p : Program} {c : Vsa.Machine.Config}
    (hwt : WellTyped Δ p) (hL : Loaded interpRunLayout p (fillZero c))
    (hterm : ¬ BigStepDiverges p) {out : String} {e : Nat} (hh : Halts c out e)
    (he : e ≠ 0) : ExecSeqErrN initSt 0 0 p :=
  ((wellTyped_machine hwt hL).2.1 out e hh he).resolve_right hterm

/-- **Machine-level type safety for programs the WHILE type checker accepts.** -/
theorem whileTyped_machine {p : Program} {c : Vsa.Machine.Config} (hwt : whileTyped p = true)
    (hL : Loaded interpRunLayout p (fillZero c)) :
    (∀ out, BigStep p out ↔ Halts c out 0) ∧
    (∀ out e, Halts c out e → e ≠ 0 →
      ExecSeqErrN initSt 0 0 p ∨ BigStepDiverges p) ∧
    (Diverges c → ¬ ∃ out, BigStep p out) :=
  let ⟨_, h⟩ := whileTyped_iff.mp hwt
  wellTyped_machine h hL

end Vsa.Sim.EndToEnd
