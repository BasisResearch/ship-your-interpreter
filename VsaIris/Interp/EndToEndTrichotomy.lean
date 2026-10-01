import VsaIris.Interp.EndToEnd
import Vsa.While.Exclusive
import Vsa.While.StmtDispatchClose

namespace Vsa.Sim.EndToEnd

open Vsa.While
open Vsa.Machine (Halts Diverges)
open Vsa.Refine (Loaded)
open Vsa.Sim.LayoutInstance (interpRunLayout)
open Vsa.Densify (fillZero halts_fillZero diverges_fillZero)
open VsaIris.Interp (AbortCode)

structure EndToEndTrichotomy (p : Program) (c : Vsa.Machine.Config) : Prop where

  clean : ∀ out, Halts c out 0 ↔ BigStep p out

  fail_code : ∀ out e, Halts c out e → e ≠ 0 → AbortCode e

  fail_spec : ∀ out e, Halts c out e → e ≠ 0 → BigStepErr p ∨ BigStepDiverges p

  div_spec : Diverges c → BigStepErr p ∨ BigStepDiverges p

  err_mach : BigStepErr p → Diverges c ∨ ∃ out e, Halts c out e ∧ AbortCode e

  div_mach : BigStepDiverges p → Diverges c ∨ ∃ out e, Halts c out e ∧ AbortCode e

theorem endToEnd_trichotomy_loaded :
    ∀ p c, Loaded interpRunLayout p c → EndToEndTrichotomy p c := by
  intro p c hL
  have hclean := (endToEnd_refinement_loaded p c hL).1
  have hpart := VsaIris.Interp.partialSim_iris p c hL

  have hnb_halt : ∀ out e, Halts c out e → e ≠ 0 → ¬ ∃ out', BigStep p out' := by
    rintro out e hh he ⟨out', hb⟩
    exact he ((hh.deterministic ((hclean out').1 hb)).2)
  have hnb_div : Diverges c → ¬ ∃ out', BigStep p out' :=
    (endToEnd_refinement_loaded p c hL).2
  have hstuck : (¬ ∃ out, BigStep p out) →
      Diverges c ∨ ∃ out e, Halts c out e ∧ AbortCode e := by
    intro hnb
    rcases hpart with hd | ⟨out, e, hh, ⟨-, hb⟩ | hcode⟩
    · exact .inl hd
    · exact absurd ⟨out, hb⟩ hnb
    · exact .inr ⟨out, e, hh, hcode⟩
  refine ⟨fun out => (hclean out).symm, ?_, ?_, ?_, ?_, ?_⟩
  · intro out e hh he
    rcases hpart with hd | ⟨out', e', hh', ⟨rfl, -⟩ | hcode⟩
    · exact (hd.not_halts hh).elim
    · exact (he (hh.deterministic hh').2).elim
    · rwa [(hh.deterministic hh').2]
  · intro out e hh he
    exact err_or_div_of_not_bigStep trichotomy_unconditional (hnb_halt out e hh he)
  · intro hd
    exact err_or_div_of_not_bigStep trichotomy_unconditional (hnb_div hd)
  · intro herr
    exact hstuck fun ⟨_, hb⟩ => bigStep_not_err hb herr
  · intro hdiv
    exact hstuck fun ⟨_, hb⟩ => bigStep_not_diverges hb hdiv

theorem endToEnd_trichotomy :
    ∀ p c, Loaded interpRunLayout p (fillZero c) → EndToEndTrichotomy p c := by
  intro p c hL
  have h := endToEnd_trichotomy_loaded p (fillZero c) hL
  refine ⟨fun out => (halts_fillZero c out 0).trans (h.clean out),
    fun out e hh => h.fail_code out e ((halts_fillZero c out e).1 hh),
    fun out e hh => h.fail_spec out e ((halts_fillZero c out e).1 hh),
    fun hd => h.div_spec ((diverges_fillZero c).1 hd),
    fun herr => ?_, fun hdiv => ?_⟩
  · rcases h.err_mach herr with hd | ⟨out, e, hh, hc⟩
    · exact .inl ((diverges_fillZero c).2 hd)
    · exact .inr ⟨out, e, (halts_fillZero c out e).2 hh, hc⟩
  · rcases h.div_mach hdiv with hd | ⟨out, e, hh, hc⟩
    · exact .inl ((diverges_fillZero c).2 hd)
    · exact .inr ⟨out, e, (halts_fillZero c out e).2 hh, hc⟩

theorem EndToEndTrichotomy.fails_iff {p : Program} {c : Vsa.Machine.Config}
    (h : EndToEndTrichotomy p c) :
    ((∃ out e, Halts c out e ∧ e ≠ 0) ∨ Diverges c) ↔ (BigStepErr p ∨ BigStepDiverges p) := by
  constructor
  · rintro (⟨out, e, hh, he⟩ | hd)
    · exact h.fail_spec out e hh he
    · exact h.div_spec hd
  · rintro (herr | hdiv)
    · rcases h.err_mach herr with hd | ⟨out, e, hh, hc⟩
      · exact .inr hd
      · exact .inl ⟨out, e, hh, hc.ne_zero⟩
    · rcases h.div_mach hdiv with hd | ⟨out, e, hh, hc⟩
      · exact .inr hd
      · exact .inl ⟨out, e, hh, hc.ne_zero⟩

theorem exactlyOne (p : Program) : ExactlyOne p where
  some := trichotomy_unconditional p
  term_not_err := fun ⟨_, h⟩ => bigStep_not_err h
  term_not_div := fun ⟨_, h⟩ => bigStep_not_diverges h
  err_not_div := err_not_diverges

end Vsa.Sim.EndToEnd

#print axioms Vsa.Sim.EndToEnd.endToEnd_trichotomy
#print axioms Vsa.Sim.EndToEnd.EndToEndTrichotomy.fails_iff
#print axioms Vsa.Sim.EndToEnd.exactlyOne
#print axioms VsaIris.Interp.partialSim_iris
