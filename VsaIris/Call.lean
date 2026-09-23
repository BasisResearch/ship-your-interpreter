import VsaIris.Step

/-!
# Instruction and function specifications, MachCSL style

Paper §4.3-4.6 and Figures 7-8. Every specification is a wand that ends in
the run's total WP: the caller supplies, as its last premise, "the rest of
the run" from the state the callee returns in. There are no Hoare
postconditions; the return is a continuation (`RET`'s spec, Figure 8b,
hands `pc ↦ r` to it).

Instruction leaves take an *exec fact* about the model as a hypothesis
(MachCSL's leaf lemmas discharge it by evaluating the Sail decoder, see
claude-notes/design/execution-model.md "Decode: the fast concrete-state
bridge"; VSA already has these facts as `StepObs`/`segEval` results).
-/

namespace VsaIris

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] {M : MachineModel}

/-- `instr i` (paper Fig. 8): the instruction bytes at `i`, read-only and
persistent, as `kernel_text` provides them (MachCSL `text_pointsto … □`,
execution-model.md "Kernel CODE bytes are ↦ₓ□"). -/
def instrAt (i : Nat) (code : List (BitVec 8)) : IProp GF :=
  sepL (code.zipIdx) (fun p => (i + p.2) ↦ₘ□ p.1)

instance (i : Nat) (code : List (BitVec 8)) : Persistent (instrAt (GF := GF) i code) := by
  unfold instrAt; infer_instance

/-- The read footprint an instruction fetch contributes. -/
def codeFoot (i : Nat) (code : List (BitVec 8)) : List (Nat × DFrac × BitVec 8) :=
  code.zipIdx.map (fun p => (i + p.2, DFrac.discard, p.1))

theorem instrAt_eq (i : Nat) (code : List (BitVec 8)) :
    instrAt (GF := GF) i code = sepL (codeFoot i code) (fun p => p.1 ↦ₘ{p.2.1} p.2.2) := by
  unfold instrAt codeFoot
  generalize code.zipIdx = l
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [sepL_cons, List.map_cons, ih]

/-- The exec fact for `ret` (`jalr x0, 0(ra)`) at `i`. -/
def RetExec (M : MachineModel) (i : Nat) (code : List (BitVec 8)) : Prop :=
  ∀ r σ, M.ok σ → FootHolds (M := M) σ [(ra, DFrac.own 1, r)] (codeFoot i code)
      [(PC, BitVec.ofNat 64 i, r)] [] →
    ∃ σ', M.step σ = .next σ' ∧ M.ok σ' ∧ LocalStep (M := M) σ σ' [(PC, BitVec.ofNat 64 i, r)] [] ∧
      M.out σ' = M.out σ

/-- The exec fact for `jal ra, tgt` at `i`. -/
def JalExec (M : MachineModel) (i : Nat) (code : List (BitVec 8)) (tgt : BitVec 64) : Prop :=
  ∀ v σ, M.ok σ → FootHolds (M := M) σ [] (codeFoot i code)
      [(PC, BitVec.ofNat 64 i, tgt), (ra, v, BitVec.ofNat 64 (i + 4))] [] →
    ∃ σ', M.step σ = .next σ' ∧ M.ok σ' ∧
      LocalStep (M := M) σ σ' [(PC, BitVec.ofNat 64 i, tgt), (ra, v, BitVec.ofNat 64 (i + 4))] [] ∧
      M.out σ' = M.out σ

/-- **RET** (paper Fig. 8b). -/
theorem wp_ret {Φ : Nat × String → IProp GF} {i : Nat} {code : List (BitVec 8)} {r : BitVec 64}
    (hexec : RetExec M i code) :
    instrAt (GF := GF) i code ∗ PC ↦ᵣ BitVec.ofNat 64 i ∗ ra ↦ᵣ r ∗
      (PC ↦ᵣ r -∗ ra ↦ᵣ r -∗ mTWP M Φ) ⊢ mTWP M Φ := by
  iintro ⟨#Hi, Hpc, Hra, Hk⟩
  iapply wp_local_step [(ra, DFrac.own 1, r)] (codeFoot i code) [(PC, BitVec.ofNat 64 i, r)] []
    (fun σ hok h => hexec r σ hok h)
  unfold footPre footPost
  rw [← instrAt_eq]
  simp only [sepL_cons, sepL_nil]
  iframe Hi Hra Hpc
  iintro ⟨⟨Hra, -⟩, -, ⟨Hpc, -⟩, -⟩
  iapply Hk $$ Hpc Hra

/-- **JAL** to a call target: `ra` becomes the return address `i + 4`. -/
theorem wp_jal {Φ : Nat × String → IProp GF} {i : Nat} {code : List (BitVec 8)}
    {tgt v : BitVec 64} (hexec : JalExec M i code tgt) :
    instrAt (GF := GF) i code ∗ PC ↦ᵣ BitVec.ofNat 64 i ∗ ra ↦ᵣ v ∗
      (PC ↦ᵣ tgt -∗ ra ↦ᵣ BitVec.ofNat 64 (i + 4) -∗ mTWP M Φ) ⊢ mTWP M Φ := by
  iintro ⟨#Hi, Hpc, Hra, Hk⟩
  iapply wp_local_step [] (codeFoot i code)
    [(PC, BitVec.ofNat 64 i, tgt), (ra, v, BitVec.ofNat 64 (i + 4))] [] (fun σ hok h => hexec v σ hok h)
  unfold footPre footPost
  rw [← instrAt_eq]
  simp only [sepL_cons, sepL_nil]
  iframe Hi Hpc Hra
  iintro ⟨-, -, ⟨Hpc, Hra, -⟩, -⟩
  iapply Hk $$ Hpc Hra

/-- A function specification in MachCSL's continuation style (paper Fig. 7,
`SpecKalloc.v:30-56` `wp_kalloc_sconf_body`): for every return address `r`
and every global postcondition `Φ`, entering at `entry` with `ra ↦ r` and
the precondition, and handing over the continuation from `pc ↦ r` with the
postcondition, runs to completion. It is persistent, like MachCSL's specs
(a `Module Type` parameter), so a caller may use it any number of times. -/
def fnSpec (entry : BitVec 64) (P Q : BitVec 64 → IProp GF) : IProp GF :=
  iprop(□ ∀ (r : BitVec 64) (Φ : Nat × String → IProp GF),
    PC ↦ᵣ entry -∗ ra ↦ᵣ r -∗ P r -∗
      (PC ↦ᵣ r -∗ ra ↦ᵣ r -∗ Q r -∗ mTWP M Φ) -∗ mTWP M Φ)

instance (entry : BitVec 64) (P Q : BitVec 64 → IProp GF) :
    Persistent (fnSpec (M := M) entry P Q) := by
  unfold fnSpec; infer_instance

/-- **Call.** A `jal ra, entry` at `i` into a function meeting `fnSpec`: the
caller hands over the precondition and gets the postcondition back at
`i + 4`. Whatever else the caller owns is framed by the continuation wand;
the callee's spec never mentions it (paper §4.6 "Framing ownership"). -/
theorem wp_call {Φ : Nat × String → IProp GF} {i : Nat} {code : List (BitVec 8)}
    {entry v : BitVec 64} {P Q : BitVec 64 → IProp GF} (hexec : JalExec M i code entry) :
    instrAt (GF := GF) i code ∗ fnSpec (M := M) entry P Q ∗ PC ↦ᵣ BitVec.ofNat 64 i ∗ ra ↦ᵣ v ∗
      P (BitVec.ofNat 64 (i + 4)) ∗
      (PC ↦ᵣ BitVec.ofNat 64 (i + 4) -∗ ra ↦ᵣ BitVec.ofNat 64 (i + 4) -∗
        Q (BitVec.ofNat 64 (i + 4)) -∗ mTWP M Φ)
    ⊢ mTWP M Φ := by
  unfold fnSpec
  iintro ⟨#Hi, #Hspec, Hpc, Hra, HP, Hk⟩
  iapply wp_jal hexec
  iframe Hi Hpc Hra
  iintro Hpc Hra
  iapply Hspec $$ %(BitVec.ofNat 64 (i + 4)) %Φ Hpc Hra HP Hk

end

end VsaIris
