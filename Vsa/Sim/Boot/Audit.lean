import Vsa.Sim.Boot.EndToEnd
import Vsa.Sim.Boot.Elf
import Vsa.Sim.Boot.Gen.Functions1
import Vsa.Sim.Boot.Gen.Functions2
import Vsa.Sim.Boot.Gen.ErrDivzero
import Vsa.Sim.Boot.Gen.ErrUndefined

/-!
# REVIEW2 audit (lane V2): kernel-checked corollaries of `endToEnd_refinement`

Everything here is a *corollary*; nothing is assumed. `scripts/check_final_axioms.sh`
audits the axioms of every theorem below.

* §1: `IrisHoles` is trivially inhabited; the theorem with no hypotheses.
* §2: non-trivial conclusions at the real entry states, and the capstones at
  ANY entry configuration (`*_halts_entry`, REVIEW2.md P8): the state the
  binary reaches satisfies their three hypotheses — `EntryRegs`, an empty
  console, the entry view as a partial view of its memory — which
  `experiments/review-v2/Replay.lean` checks natively.
* §3: the runtime-error programs have no `BigStep` (the cost evaluator is
  `stuck`, one kernel `decide`), never halt cleanly, and diverge or exit
  nonzero.
* §4: the machine and source notions are the real ones (`rfl` unfoldings).
-/

open Vsa.While Vsa.Machine Vsa.Refine Vsa.Sim.LayoutInstance Vsa.Densify Vsa.Sim.Boot

namespace ReviewV2

/-! ## 1. `IrisHoles` is trivially inhabited; the theorem is unconditional -/

example : VsaIris.Interp.IrisHoles := ⟨⟩

theorem endToEnd_unconditional :
    ∀ p c, Loaded interpRunLayout p (fillZero c) →
      (∀ out, BigStep p out ↔ Halts c out 0) ∧ (Diverges c → ¬ ∃ out, BigStep p out) :=
  Vsa.Sim.EndToEnd.endToEnd_refinement ⟨⟩

/-- The concrete entry configuration of the proof ELF (loader memory + traced stores). -/
abbrev cProof : Config :=
  bootConfig (bootMem Gen.Proof.script Gen.Proof.log) Gen.Proof.regs Gen.Proof.entrySteps

/-! ## 2. Non-trivial conclusions at the real entry states -/

theorem proofElf_halts_unconditional : Halts cProof "55\n2500\n36\n" 0 := proofElf_halts ⟨⟩

/-- **The capstone at any entry configuration** (P8): registers satisfying
`EntryRegs` (`GoodState`, `PC`, `htif_payload_writes`, the traced `x1 … x31`), an
empty console, and a memory the entry view is a partial view of — the state
the binary reaches after `Gen.Proof.entrySteps` steps satisfies all three
(`Replay.lean`). -/
theorem proofElf_halts_entry {σ : MState} (E : EntryRegs σ Gen.Proof.regs)
    (hout : output σ = "") (hv : PartialView σ.mem (bootView Gen.Proof.script Gen.Proof.runs))
    {tick : Nat} (htick : tick < 2) (steps : Nat) :
    Halts ⟨σ, tick, steps⟩ "55\n2500\n36\n" 0 :=
  ((endToEnd_unconditional _ _ (Gen.Proof.prog_eq ▸ Gen.Proof.loadedEntry_fill E hout hv htick steps)).1 _).mp
    Vsa.While.Validation.whileWl_valid

theorem arithmetic_halts_entry {σ : MState} (E : EntryRegs σ Gen.Arithmetic.regs)
    (hout : output σ = "") (hv : PartialView σ.mem (bootView Gen.Arithmetic.script Gen.Arithmetic.runs))
    {tick : Nat} (htick : tick < 2) (steps : Nat) :
    Halts ⟨σ, tick, steps⟩
      "7\n9\n3\n1\n-2\n26\n1000000000000\n4\nfalse true false\ntrue true false true\ntrue true true false\nfalse true true false\n"
      0 :=
  ((endToEnd_unconditional _ _ (Gen.Arithmetic.prog_eq ▸ Gen.Arithmetic.loadedEntry_fill E hout hv htick steps)).1 _).mp
    Vsa.While.Validation.arithmetic_valid

/-- `Halts` is not trivially true: the same state does not halt with output `""`,
nor with exit code 1. -/
theorem proofElf_not_halts_empty : ¬ Halts cProof "" 0 := by
  intro h
  have := (Halts.deterministic h proofElf_halts_unconditional).1
  simp at this

theorem proofElf_not_halts_exit1 : ¬ Halts cProof "55\n2500\n36\n" 1 := by
  intro h
  have := (Halts.deterministic h proofElf_halts_unconditional).2
  omega

/-- `BigStep` is the only behaviour: any clean halt of the proof ELF prints `55 2500 36`. -/
theorem proofElf_clean_halt_unique (out : String) (h : Halts cProof out 0) : out = "55\n2500\n36\n" :=
  (Halts.deterministic h proofElf_halts_unconditional).1

theorem proofElf_not_diverges : ¬ Diverges cProof :=
  fun hd => hd.not_halts proofElf_halts_unconditional

theorem arithmetic_halts_unconditional :
    Halts (bootConfig (bootMem Gen.Arithmetic.script Gen.Arithmetic.log) Gen.Arithmetic.regs
      Gen.Arithmetic.entrySteps)
      "7\n9\n3\n1\n-2\n26\n1000000000000\n4\nfalse true false\ntrue true false true\ntrue true true false\nfalse true true false\n"
      0 := arithmetic_halts ⟨⟩

theorem for_halts_unconditional :
    Halts (bootConfig (bootMem Gen.For.script Gen.For.log) Gen.For.regs Gen.For.entrySteps)
      "1\n2\nFizz\n4\nBuzz\nFizz\n7\n8\nFizz\nBuzz\n11\nFizz\n13\n14\nFizzBuzz\n5050\n37\n3\n01234\n"
      0 := for_halts ⟨⟩

theorem strings_halts_unconditional :
    Halts (bootConfig (bootMem Gen.Strings.script Gen.Strings.log) Gen.Strings.regs
      Gen.Strings.entrySteps)
      "hello world\nvalue: 42\n12\ntrue true\ntrue true\nline1\nline2\ntab\there\nquote: \"hi\"\n"
      0 := strings_halts ⟨⟩

theorem scope_halts_unconditional :
    Halts (bootConfig (bootMem Gen.Scope.script Gen.Scope.log) Gen.Scope.regs
      Gen.Scope.entrySteps) "2\n3\n1\n20\n14 5\n3\nasserts ok\n" 0 := scope_halts ⟨⟩

/-! ## 3. Runtime-error programs: no `BigStep`, no clean halt, not silent -/

/-- `Res.stuck`, as a Bool (for one kernel `decide`). -/
def isStuck : Res SOut → Bool
  | .stuck => true
  | _ => false

theorem isStuck_eq {r : Res SOut} (h : isStuck r = true) : r = .stuck := by
  cases r <;> simp [isStuck] at h ⊢

theorem errDivzero_eval_stuck : isStuck (execSeqEval 1000 initSt 0 0 Gen.ErrDivzero.prog) = true := by
  decide +kernel

theorem errUndefined_eval_stuck : isStuck (execSeqEval 1000 initSt 0 0 Gen.ErrUndefined.prog) = true := by
  decide +kernel

/-- The source semantics assigns `err_divzero.wl` no behaviour. -/
theorem errDivzero_noBigStep : ¬ ∃ out, BigStep Gen.ErrDivzero.prog out := by
  rintro ⟨out, st', hseq, _⟩
  obtain ⟨n, hc⟩ := execSeq_cost_exists hseq
  exact execSeqCost_none_of_stuck (isStuck_eq errDivzero_eval_stuck) st' .normal n hc

theorem errUndefined_noBigStep : ¬ ∃ out, BigStep Gen.ErrUndefined.prog out := by
  rintro ⟨out, st', hseq, _⟩
  obtain ⟨n, hc⟩ := execSeq_cost_exists hseq
  exact execSeqCost_none_of_stuck (isStuck_eq errUndefined_eval_stuck) st' .normal n hc

abbrev cDiv : Config :=
  bootConfig (bootMem Gen.ErrDivzero.script Gen.ErrDivzero.log) Gen.ErrDivzero.regs Gen.ErrDivzero.entrySteps
abbrev cUndef : Config :=
  bootConfig (bootMem Gen.ErrUndefined.script Gen.ErrUndefined.log) Gen.ErrUndefined.regs
    Gen.ErrUndefined.entrySteps

/-- The binary, from the real entry state of `err_divzero.wl`, never halts with exit code 0. -/
theorem errDivzero_never_clean : ∀ out, ¬ Halts cDiv out 0 := fun out h =>
  errDivzero_noBigStep ⟨out, ((endToEnd_unconditional _ _ Gen.ErrDivzero.loaded).1 out).mpr h⟩

theorem errUndefined_never_clean : ∀ out, ¬ Halts cUndef out 0 := fun out h =>
  errUndefined_noBigStep ⟨out, ((endToEnd_unconditional _ _ Gen.ErrUndefined.loaded).1 out).mpr h⟩

/-- … and, by the stuck simulation, it diverges or halts with a nonzero exit code
(the emulator: `runtime error [line 1]: division by zero`, exit 70). -/
theorem errDivzero_stuck : Diverges cDiv ∨ ∃ out e, Halts cDiv out e ∧ e ≠ 0 := by
  rcases (VsaIris.Interp.interpSim_iris ⟨⟩).stuck_sim _ _ Gen.ErrDivzero.loaded errDivzero_noBigStep
    with h | ⟨out, e, h, he⟩
  · exact Or.inl ((diverges_fillZero _).2 h)
  · exact Or.inr ⟨out, e, (halts_fillZero _ _ _).2 h, he⟩

theorem errUndefined_stuck : Diverges cUndef ∨ ∃ out e, Halts cUndef out e ∧ e ≠ 0 := by
  rcases (VsaIris.Interp.interpSim_iris ⟨⟩).stuck_sim _ _ Gen.ErrUndefined.loaded errUndefined_noBigStep
    with h | ⟨out, e, h, he⟩
  · exact Or.inl ((diverges_fillZero _).2 h)
  · exact Or.inr ⟨out, e, (halts_fillZero _ _ _).2 h, he⟩

theorem errDivzero_never_clean_entry {σ : MState} (E : EntryRegs σ Gen.ErrDivzero.regs)
    (hout : output σ = "") (hv : PartialView σ.mem (bootView Gen.ErrDivzero.script Gen.ErrDivzero.runs))
    {tick : Nat} (htick : tick < 2) (steps : Nat) :
    ∀ out, ¬ Halts ⟨σ, tick, steps⟩ out 0 := fun out h =>
  errDivzero_noBigStep ⟨out,
    ((endToEnd_unconditional _ _ (Gen.ErrDivzero.loadedEntry_fill E hout hv htick steps)).1 out).mpr h⟩

/-! ## 4. The machine notions are the real ones (definitional unfoldings, checked by `rfl`) -/

example : Halts = fun (c : Config) (out : String) (e : Nat) =>
    ∃ c' σf, Steps c c' ∧ Halted c' e σf ∧ output σf = out := rfl
example : Diverges = fun (c : Config) => ∀ n, ∃ c', StepsN n c c' := rfl
example : output = fun (σ : MState) => String.join σ.sailOutput.toList := rfl
example : BigStep = fun (p : Program) (out : String) =>
    ∃ st', ExecSeq initSt 0 0 p st' .normal ∧ st'.out = out := rfl
example : bootMem = fun (script : Nat) (L : PackedLog) =>
    Vsa.Sim.writeLog (loadedMem script) L.log := rfl
example : loadedMem = fun (script : Nat) => loaderMem bootPieces (imageByte script) := rfl
example : Gen.Proof.prog = Vsa.While.Programs.whileWl := Gen.Proof.prog_eq

end ReviewV2

#print axioms ReviewV2.endToEnd_unconditional
#print axioms ReviewV2.proofElf_halts_unconditional
#print axioms ReviewV2.proofElf_not_halts_empty
#print axioms ReviewV2.proofElf_not_diverges
#print axioms ReviewV2.arithmetic_halts_unconditional
#print axioms ReviewV2.for_halts_unconditional
#print axioms ReviewV2.strings_halts_unconditional
#print axioms ReviewV2.scope_halts_unconditional
#print axioms ReviewV2.errDivzero_noBigStep
#print axioms ReviewV2.errDivzero_never_clean
#print axioms ReviewV2.errDivzero_stuck
#print axioms ReviewV2.errUndefined_stuck
#print axioms ReviewV2.proofElf_halts_entry
#print axioms ReviewV2.arithmetic_halts_entry
#print axioms ReviewV2.errDivzero_never_clean_entry
#print axioms Vsa.Sim.Boot.Gen.Proof.loaded
#print axioms Vsa.Sim.Boot.Gen.While.loaded
#print axioms Vsa.Sim.Boot.Gen.Arithmetic.loaded
#print axioms Vsa.Sim.Boot.Gen.For.loaded
#print axioms Vsa.Sim.Boot.Gen.Scope.loaded
#print axioms Vsa.Sim.Boot.Gen.Strings.loaded
#print axioms Vsa.Sim.Boot.Gen.Functions1.loaded
#print axioms Vsa.Sim.Boot.Gen.Functions2.loaded
#print axioms Vsa.Sim.Boot.Gen.ErrDivzero.loaded
#print axioms Vsa.Sim.Boot.Gen.ErrUndefined.loaded
#print axioms Vsa.Sim.Boot.proofElf_halts
#print axioms Vsa.Sim.Boot.while_halts
#print axioms Vsa.Sim.Boot.arithmetic_halts
#print axioms Vsa.Sim.Boot.for_halts
#print axioms Vsa.Sim.Boot.scope_halts
#print axioms Vsa.Sim.Boot.strings_halts
#print axioms Vsa.Sim.Boot.initializeMemory_eq
#print axioms Vsa.Sim.EndToEnd.endToEnd_refinement
#print axioms VsaIris.Interp.interpSim_iris
#print axioms VsaIris.Interp.IrisHoles.proved
