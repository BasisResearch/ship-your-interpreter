import VsaIris.MachWP

namespace VsaIris

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] {M : MachineModel}

def instrAt (i : Nat) (code : List (BitVec 8)) : IProp GF :=
  sepL (code.zipIdx) (fun p => (i + p.2) ↦ₘ□ p.1)

instance (i : Nat) (code : List (BitVec 8)) : Persistent (instrAt (GF := GF) i code) := by
  unfold instrAt; infer_instance

def codeFoot (i : Nat) (code : List (BitVec 8)) : List (Nat × DFrac × BitVec 8) :=
  code.zipIdx.map (fun p => (i + p.2, DFrac.discard, p.1))

theorem instrAt_eq (i : Nat) (code : List (BitVec 8)) :
    instrAt (GF := GF) i code = sepL (codeFoot i code) (fun p => p.1 ↦ₘ{p.2.1} p.2.2) := by
  unfold instrAt codeFoot
  generalize code.zipIdx = l
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [sepL_cons, List.map_cons, ih]

def JalExec (M : MachineModel) (i : Nat) (code : List (BitVec 8)) (tgt : BitVec 64) : Prop :=
  ∀ v σ, M.ok σ → FootHolds (M := M) σ [] (codeFoot i code)
      [(PC, BitVec.ofNat 64 i, tgt), (ra, v, BitVec.ofNat 64 (i + 4))] [] →
    ∃ σ', M.step σ = .next σ' ∧ M.ok σ' ∧
      LocalStep (M := M) σ σ' [(PC, BitVec.ofNat 64 i, tgt), (ra, v, BitVec.ofNat 64 (i + 4))] [] ∧
      M.out σ' = M.out σ

theorem wp_jalW (Wp : MachWP (GF := GF) M) {Φ : Nat × String → IProp GF} {i : Nat}
    {code : List (BitVec 8)} {tgt v : BitVec 64} (hexec : JalExec M i code tgt) :
    instrAt (GF := GF) i code ∗ PC ↦ᵣ BitVec.ofNat 64 i ∗ ra ↦ᵣ v ∗
      (PC ↦ᵣ tgt -∗ ra ↦ᵣ BitVec.ofNat 64 (i + 4) -∗ Wp.lat (Wp.W Φ)) ⊢ Wp.W Φ := by
  iintro ⟨#Hi, Hpc, Hra, Hk⟩
  iapply Wp.local_stepL [] (codeFoot i code)
    [(PC, BitVec.ofNat 64 i, tgt), (ra, v, BitVec.ofNat 64 (i + 4))] [] (fun σ hok h => hexec v σ hok h)
  unfold footPre footPost
  rw [← instrAt_eq]
  simp only [sepL_cons, sepL_nil]
  iframe Hi Hpc Hra
  iintro ⟨-, -, ⟨Hpc, Hra, -⟩, -⟩
  iapply Hk $$ Hpc Hra

def fnSpecW (Wp : MachWP (GF := GF) M) (entry : BitVec 64) (P Q : BitVec 64 → IProp GF) :
    IProp GF :=
  iprop(□ ∀ (r : BitVec 64) (Φ : Nat × String → IProp GF),
    PC ↦ᵣ entry -∗ ra ↦ᵣ r -∗ P r -∗
      (PC ↦ᵣ r -∗ ra ↦ᵣ r -∗ Q r -∗ Wp.W Φ) -∗ Wp.W Φ)

instance (Wp : MachWP (GF := GF) M) (entry : BitVec 64) (P Q : BitVec 64 → IProp GF) :
    Persistent (fnSpecW Wp entry P Q) := by
  unfold fnSpecW; infer_instance

theorem wp_callW (Wp : MachWP (GF := GF) M) {Φ : Nat × String → IProp GF} {i : Nat}
    {code : List (BitVec 8)} {entry v : BitVec 64} {P Q : BitVec 64 → IProp GF}
    (hexec : JalExec M i code entry) :
    instrAt (GF := GF) i code ∗ fnSpecW Wp entry P Q ∗ PC ↦ᵣ BitVec.ofNat 64 i ∗ ra ↦ᵣ v ∗
      P (BitVec.ofNat 64 (i + 4)) ∗
      (PC ↦ᵣ BitVec.ofNat 64 (i + 4) -∗ ra ↦ᵣ BitVec.ofNat 64 (i + 4) -∗
        Q (BitVec.ofNat 64 (i + 4)) -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  unfold fnSpecW
  iintro ⟨#Hi, #Hspec, Hpc, Hra, HP, Hk⟩
  iapply wp_jalW Wp hexec
  iframe Hi Hpc Hra
  iintro Hpc Hra
  iapply Wp.lat_intro
  iapply Hspec $$ %(BitVec.ofNat 64 (i + 4)) %Φ Hpc Hra HP Hk

end

end VsaIris
