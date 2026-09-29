import VsaIris.Interp.EndToEnd
import Vsa.While.Exclusive
import Vsa.While.StmtDispatchClose

/-!
# The behavioural trichotomy on the binary

`Vsa.While` splits every program into exactly one of three outcomes
(`trichotomy_unconditional`, and `Vsa/While/Exclusive.lean` for exclusivity):
it terminates (`BigStep`), hits a runtime error (`BigStepErr`), or runs
forever (`BigStepDiverges`). This file relates the three outcomes to the
machine behaviour of the interpreter binary, at every loaded configuration:

* `Halts c out 0 ↔ BigStep p out` (`endToEnd_refinement`);
* every nonzero exit is `70` or `1` (`AbortCode`), and it happens only for
  programs that error or diverge;
* a divergent machine run happens only for programs that error or diverge;
* a program that errors or diverges makes the machine diverge or exit `70`
  or `1`.

So `(∃ out e, Halts c out e ∧ e ≠ 0) ∨ Diverges c ↔ BigStepErr p ∨
BigStepDiverges p` (`EndToEndTrichotomy.fails_iff`).

**What is not claimed, and why.** The machine does not separate the two
failing outcomes: `BigStepErr p → ∃ out, Halts c out 70` and
`BigStepDiverges p → Diverges c` are both false for the binary. The heap is
the fixed interval `[_end, __heap_end)` (`Vsa.Sim.DlHeap.heapStart`,
`heapEnd`, about 126 MiB), the interpreter never frees an environment frame
(`env_new`, `c/src/env.c:13`), and `Loaded` only guarantees heap capacity for
*terminating* derivations (`DlHeap.InitialAllocatorAt.capacity`). The program
`while (true) { { } }` diverges in the semantics, while the binary allocates
one frame per iteration and leaves through `xmalloc`'s `exit(1)` ("out of
memory"); a program that runs such a loop for `10^8` iterations and then
divides by zero errs in the semantics and exits `1` on the binary. Both
outcomes are covered by `AbortCode`.
-/

namespace Vsa.Sim.EndToEnd

open Vsa.While
open Vsa.Machine (Halts Diverges)
open Vsa.Refine (Loaded)
open Vsa.Sim.LayoutInstance (interpRunLayout)
open Vsa.Densify (fillZero halts_fillZero diverges_fillZero)
open VsaIris.Interp (AbortCode)

/-- The behavioural trichotomy of the binary at a configuration `c` holding
program `p`. -/
structure EndToEndTrichotomy (p : Program) (c : Vsa.Machine.Config) : Prop where
  /-- Clean termination is exactly the big-step behaviour. -/
  clean : ∀ out, Halts c out 0 ↔ BigStep p out
  /-- Every nonzero exit code is `70` (runtime error, top-level abrupt status)
  or `1` (out of memory). -/
  fail_code : ∀ out e, Halts c out e → e ≠ 0 → AbortCode e
  /-- A nonzero exit happens only for a program that errors or diverges. -/
  fail_spec : ∀ out e, Halts c out e → e ≠ 0 → BigStepErr p ∨ BigStepDiverges p
  /-- A divergent run happens only for a program that errors or diverges. -/
  div_spec : Diverges c → BigStepErr p ∨ BigStepDiverges p
  /-- A program that errors never exits `0`: the machine diverges or exits
  with an `AbortCode`. -/
  err_mach : BigStepErr p → Diverges c ∨ ∃ out e, Halts c out e ∧ AbortCode e
  /-- A program that diverges never exits `0`: the machine diverges or exits
  with an `AbortCode`. -/
  div_mach : BigStepDiverges p → Diverges c ∨ ∃ out e, Halts c out e ∧ AbortCode e

/-- The trichotomy at a configuration that is literally `Loaded`. -/
theorem endToEnd_trichotomy_loaded :
    ∀ p c, Loaded interpRunLayout p c → EndToEndTrichotomy p c := by
  intro p c hL
  have hclean := (endToEnd_refinement_loaded p c hL).1
  have hpart := VsaIris.Interp.partialSim_iris p c hL
  -- a machine behaviour other than a clean exit rules out a big-step behaviour
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

/-- **THE END-TO-END TRICHOTOMY.** For every WHILE program loaded in the
interpreter's memory (`Loaded interpRunLayout p (fillZero c)`, as in
`endToEnd_refinement`): the binary exits `0` with output `out` exactly when
`out` is the program's big-step behaviour; every other exit is `70` or `1`;
a failing exit or a divergent run happens only for a program that errors or
diverges; and such a program never exits `0`. -/
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

/-- The failing behaviours of the binary are exactly the failing outcomes of
the semantics. -/
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

/-- Every program has exactly one semantic outcome (`trichotomy_unconditional`
and `Vsa/While/Exclusive.lean`). -/
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
