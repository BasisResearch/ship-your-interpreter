import VsaIris.Interp.EndToEndTrichotomy
import VsaIris.Interp.TypeSafety
import VsaIris.AbsInt.Machine
import VsaIris.WhileLogic.Machine

namespace Vsa.Sim.EndToEnd

open Vsa.While
open Vsa.Machine (Halts Diverges)
open Vsa.Refine (Loaded)
open Vsa.Sim.LayoutInstance (interpRunLayout)
open Vsa.Densify (fillZero)
open VsaIris.Interp (AbortCode)

section Types

open Vsa.While.Types

theorem wellTyped_err_iff {Δ : TyEnv} {p : Program} (hwt : WellTyped Δ p) :
    BigStepErr p ↔ ExecSeqErrN initSt 0 0 p :=
  ⟨wellTyped_err hwt, bigStepErr_of_errN⟩

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

section AbsInt

open Vsa.AbsInt

variable {A : Type} [AbsDom A]

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

section Logic

open Iris Vsa.While.Logic

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
