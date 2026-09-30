import VsaIris.Call

namespace VsaIris

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] {M : MachineModel}

def fnSpecAbort (Wp : MachWP (GF := GF) M) (entry : BitVec 64)
    (P Q : BitVec 64 → IProp GF) (A : IProp GF) : IProp GF :=
  iprop(□ ∀ (r : BitVec 64) (Φ : Nat × String → IProp GF),
    PC ↦ᵣ entry -∗ ra ↦ᵣ r -∗ P r -∗
      ((PC ↦ᵣ r -∗ ra ↦ᵣ r -∗ Q r -∗ Wp.W Φ) ∧ (A -∗ Wp.W Φ)) -∗ Wp.W Φ)

instance (Wp : MachWP (GF := GF) M) (entry : BitVec 64) (P Q : BitVec 64 → IProp GF)
    (A : IProp GF) : Persistent (fnSpecAbort Wp entry P Q A) := by
  unfold fnSpecAbort; infer_instance

theorem wp_callAbort (Wp : MachWP (GF := GF) M) {Φ : Nat × String → IProp GF} {i : Nat}
    {code : List (BitVec 8)} {entry v : BitVec 64} {P Q : BitVec 64 → IProp GF}
    {A : IProp GF} (hexec : JalExec M i code entry) :
    instrAt (GF := GF) i code ∗ fnSpecAbort Wp entry P Q A ∗ PC ↦ᵣ BitVec.ofNat 64 i ∗
      ra ↦ᵣ v ∗ P (BitVec.ofNat 64 (i + 4)) ∗
      ((PC ↦ᵣ BitVec.ofNat 64 (i + 4) -∗ ra ↦ᵣ BitVec.ofNat 64 (i + 4) -∗
          Q (BitVec.ofNat 64 (i + 4)) -∗ Wp.W Φ) ∧ (A -∗ Wp.W Φ))
    ⊢ Wp.W Φ := by
  unfold fnSpecAbort
  iintro ⟨#Hi, #Hspec, Hpc, Hra, HP, Hk⟩
  iapply wp_jalW Wp hexec
  iframe Hi Hpc Hra
  iintro Hpc Hra
  iapply Wp.lat_intro
  iapply Hspec $$ %(BitVec.ofNat 64 (i + 4)) %Φ Hpc Hra HP Hk

theorem wp_callAbort_later {Φ : Nat × String → IProp GF} {i : Nat} {code : List (BitVec 8)}
    {entry v : BitVec 64} {P Q : BitVec 64 → IProp GF} {A : IProp GF}
    (hexec : JalExec M i code entry) :
    instrAt (GF := GF) i code ∗ ▷ fnSpecAbort (wpW M) entry P Q A ∗
      PC ↦ᵣ BitVec.ofNat 64 i ∗ ra ↦ᵣ v ∗ P (BitVec.ofNat 64 (i + 4)) ∗
      ((PC ↦ᵣ BitVec.ofNat 64 (i + 4) -∗ ra ↦ᵣ BitVec.ofNat 64 (i + 4) -∗
          Q (BitVec.ofNat 64 (i + 4)) -∗ mWP M Φ) ∧ (A -∗ mWP M Φ))
    ⊢ mWP M Φ := by
  unfold fnSpecAbort
  refine .trans ?_ (wp_jalW (wpW M) (Φ := Φ) (v := v) hexec)
  iintro ⟨#Hi, Hspec, Hpc, Hra, HP, Hk⟩
  iframe Hi Hpc Hra
  iintro Hpc Hra
  simp only [wpW_lat, wpW_W]
  inext
  iapply Hspec $$ %(BitVec.ofNat 64 (i + 4)) %Φ Hpc Hra HP Hk

end

end VsaIris
