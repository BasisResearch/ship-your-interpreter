import VsaIris.Interp.EndToEndTrichotomy
import VsaIris.Interp.TypeSafety
import VsaIris.AbsInt.Machine
import VsaIris.WhileLogic.Machine

/-!
# The tools' machine corollaries, sharpened by the trichotomy

`endToEnd_trichotomy` identifies the binary's failing behaviour (a nonzero
exit, always `70` or `1`, or a divergent run) with the program's failing
outcomes (`BigStepErr ∨ BigStepDiverges`), and `Vsa/While/Exclusive.lean`
makes the three semantic outcomes exclusive. Each tool's source-level result
therefore sharpens on the machine:

* **types** (`wellTyped_trichotomy`): for a well-typed program, the binary
  fails exactly when the program reaches a non-type runtime error (division or
  remainder by zero, a failed `assert`, the call-depth cap: `ExecSeqErrN`) or
  diverges; every nonzero exit is `70` or `1`; and a well-typed program that
  does not diverge exits nonzero only on a non-type error.
* **absint** (`noAlarm_machine`, `noAlarm_terminating`): without alarms the
  binary fails only for programs that diverge in the semantics, and a
  terminating alarm-free program always exits `0`.
* **logic** (`adequacy_exact`): a program proved in the logic has no runtime
  error and does not diverge, and every halt of the binary is exit `0` with an
  output satisfying the postcondition.

The divergence disjuncts cannot be dropped: the heap is finite, so a program
that diverges in the semantics may exit `1` (out of memory) on the binary
(`VsaIris/Interp/EndToEndTrichotomy.lean`). No corollary mentions the
diagnostic text: the machine proof does not pin what an abort prints.
-/

namespace Vsa.Sim.EndToEnd

open Vsa.While
open Vsa.Machine (Halts Diverges)
open Vsa.Refine (Loaded)
open Vsa.Sim.LayoutInstance (interpRunLayout)
open Vsa.Densify (fillZero)
open VsaIris.Interp (AbortCode)

/-! ## Types -/

section Types

open Vsa.While.Types

/-- For a well-typed program, a runtime error is a non-type error. -/
theorem wellTyped_err_iff {Δ : TyEnv} {p : Program} (hwt : WellTyped Δ p) :
    BigStepErr p ↔ ExecSeqErrN initSt 0 0 p :=
  ⟨wellTyped_err hwt, bigStepErr_of_errN⟩

/-- **Machine-level type safety, sharpened.** For a well-typed program loaded
in `c`: exit `0` is exactly the big-step behaviour; every nonzero exit is `70`
or `1`; the binary fails (nonzero exit or divergence) exactly when the program
reaches a non-type runtime error or diverges; and a program that reaches a
non-type runtime error never exits `0`: the binary diverges or exits `70` or
`1`. -/
theorem wellTyped_trichotomy {Δ : TyEnv} {p : Program} {c : Vsa.Machine.Config}
    (hwt : WellTyped Δ p) (hL : Loaded interpRunLayout p (fillZero c)) :
    (∀ out, Halts c out 0 ↔ BigStep p out) ∧
    (∀ out e, Halts c out e → e ≠ 0 → AbortCode e) ∧
    (((∃ out e, Halts c out e ∧ e ≠ 0) ∨ Diverges c) ↔
      (ExecSeqErrN initSt 0 0 p ∨ BigStepDiverges p)) ∧
    (ExecSeqErrN initSt 0 0 p → Diverges c ∨ ∃ out e, Halts c out e ∧ AbortCode e) := by
  have h := endToEnd_trichotomy p c hL
  exact ⟨h.clean, h.fail_code, h.fails_iff.trans (or_congr_left (wellTyped_err_iff hwt)),
    fun herr => h.err_mach (bigStepErr_of_errN herr)⟩

/-- A well-typed program that does not diverge exits nonzero only on a
non-type runtime error, with code `70` or `1`. -/
theorem wellTyped_terminating_halt {Δ : TyEnv} {p : Program} {c : Vsa.Machine.Config}
    (hwt : WellTyped Δ p) (hL : Loaded interpRunLayout p (fillZero c))
    (hnd : ¬ BigStepDiverges p) {out : String} {e : Nat} (hh : Halts c out e) (he : e ≠ 0) :
    AbortCode e ∧ ExecSeqErrN initSt 0 0 p := by
  have h := endToEnd_trichotomy p c hL
  refine ⟨h.fail_code out e hh he, ?_⟩
  rcases h.fail_spec out e hh he with herr | hd
  · exact wellTyped_err hwt herr
  · exact absurd hd hnd

end Types

/-! ## Abstract interpretation -/

section AbsInt

open Vsa.AbsInt

variable {A : Type} [AbsDom A]

/-- **No alarms on the machine.** If the analysis reports no alarm, the binary
fails (a nonzero exit, always `70` or `1`, or a divergent run) exactly when the
program diverges in the semantics. -/
theorem noAlarm_machine (cfg : Cfg) {p : Program} {c : Vsa.Machine.Config}
    (hal : alarms (A := A) cfg p = []) (hL : Loaded interpRunLayout p (fillZero c)) :
    (∀ out e, Halts c out e → e ≠ 0 → AbortCode e ∧ BigStepDiverges p) ∧
    (Diverges c → BigStepDiverges p) ∧
    (((∃ out e, Halts c out e ∧ e ≠ 0) ∨ Diverges c) ↔ BigStepDiverges p) := by
  have h := endToEnd_trichotomy p c hL
  have hne := no_error_of_no_alarms (A := A) cfg hal
  refine ⟨fun out e hh he => ⟨h.fail_code out e hh he,
      (h.fail_spec out e hh he).resolve_left hne⟩,
    fun hd => (h.div_spec hd).resolve_left hne,
    h.fails_iff.trans ⟨fun hx => hx.resolve_left hne, .inr⟩⟩

/-- **An alarm-free terminating program exits `0`.** If the analysis reports no
alarm and the program does not diverge, the binary halts with exit `0` and the
program's big-step output, and has no other behaviour. -/
theorem noAlarm_terminating (cfg : Cfg) {p : Program} {c : Vsa.Machine.Config}
    (hal : alarms (A := A) cfg p = []) (hL : Loaded interpRunLayout p (fillZero c))
    (hnd : ¬ BigStepDiverges p) :
    ∃ out, BigStep p out ∧ Halts c out 0 ∧
      (∀ out' e, Halts c out' e → out' = out ∧ e = 0) ∧ ¬ Diverges c := by
  have h := endToEnd_trichotomy p c hL
  rcases trichotomy_unconditional p with ⟨out, hb⟩ | herr | hd
  · have hh := (h.clean out).2 hb
    exact ⟨out, hb, hh, fun out' e hh' => hh'.deterministic hh, fun hd => hd.not_halts hh⟩
  · exact absurd herr (no_error_of_no_alarms (A := A) cfg hal)
  · exact absurd hd hnd

end AbsInt

/-! ## Program logic -/

section Logic

open Iris Vsa.While.Logic

/-- **Exact adequacy on the machine.** A program proved in the logic from
`initOwn` has no runtime error and does not diverge; the binary halts with
exit `0` and an output satisfying the postcondition, and every halt of the
binary is that one. -/
theorem adequacy_exact {p : Program} {Q : String → Prop}
    (hp : initOwn ⊢ wpSeq 0 0 p (PostOut Q)) {c : Vsa.Machine.Config}
    (hL : Loaded interpRunLayout p (fillZero c)) :
    ¬ BigStepErr p ∧ ¬ BigStepDiverges p ∧
      ∃ out, Q out ∧ BigStep p out ∧ Halts c out 0 ∧
        (∀ out' e, Halts c out' e → out' = out ∧ e = 0) := by
  obtain ⟨out, hb, hQ⟩ := adequacy_bigStep hp
  have hh := ((endToEnd_trichotomy p c hL).clean out).2 hb
  exact ⟨bigStep_not_err hb, bigStep_not_diverges hb,
    out, hQ, hb, hh, fun out' e hh' => hh'.deterministic hh⟩

end Logic

end Vsa.Sim.EndToEnd

#print axioms Vsa.Sim.EndToEnd.wellTyped_trichotomy
#print axioms Vsa.Sim.EndToEnd.wellTyped_terminating_halt
#print axioms Vsa.Sim.EndToEnd.noAlarm_machine
#print axioms Vsa.Sim.EndToEnd.noAlarm_terminating
#print axioms Vsa.Sim.EndToEnd.adequacy_exact
