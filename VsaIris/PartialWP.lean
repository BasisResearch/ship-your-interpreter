import VsaIris.Step
import Iris.ProgramLogic.Lifting

namespace VsaIris

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] (M : MachineModel)

abbrev mWP (Φ : Nat × String → IProp GF) : IProp GF :=
  iprop(cpuTok -∗ WP (MachineModel.Loop M) @ Stuckness.NotStuck; ⊤ {{ Φ }})

end

section Rules

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] {M : MachineModel}

theorem wp_stepRule {Φ : Nat × String → IProp GF} :
    StepRule M (fun P => iprop(▷ P)) (WP (MachineModel.Loop M) @ Stuckness.NotStuck; ⊤ {{ Φ }}) := by
  unfold StepRule
  iintro H
  iapply wp_lift_step_fupd rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  imod H $$ %σ₁ Hσ with ⟨%⟨σ', hσ'⟩, H⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨_, _, _, _, MachineModel.primStep_loop_next M hσ'⟩
  iintro %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨hκ, heₜ, (⟨σn, hn, he, hs⟩ | ⟨e, out, hh, _, _⟩)⟩ :=
    MachineModel.primStep_loop_inv M Hstep
  · subst hκ heₜ he hs
    imod H $$ %_ %hn with ⟨Hσ, Hwp⟩
    imodintro
    inext
    imod Hclose with -
    imodintro
    isplitl [Hσ]
    · iexact Hσ
    isplitl [Hwp]
    · iexact Hwp
    iapply BigSepL.bigSepL_nil.2
    iempintro
  · rw [hσ'] at hh; cases hh

theorem wpP_exec_halt {Φ : Nat × String → IProp GF} :
    (∀ σ, mstateInterp (GF := GF) M σ ={⊤}=∗
        ⌜∃ e out, M.step σ = .halt e out⌝ ∗
        ∀ e out, ⌜M.step σ = .halt e out⌝ ={⊤}=∗ mstateInterp M σ ∗ Φ (e, out))
    ⊢ mWP M Φ := by
  iintro H Htok
  iapply wp_lift_atomic_step (s := Stuckness.NotStuck) rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  ihave ⟨%c, Hc, %hc, Htok, Hσ⟩ := fullInterp_cpu (M := M) $$ Hσ Htok
  imod H $$ Hσ with ⟨%⟨e, out, hh⟩, H⟩
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, _, _, _, MachineModel.primStep_loop_halt M hh⟩
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨hκ, heₜ, (⟨σn, hn, _, _⟩ | ⟨e', out', hh', rfl, rfl⟩)⟩ :=
    MachineModel.primStep_loop_inv M Hstep
  · rw [hh] at hn; cases hn
  · subst hκ heₜ
    imod H $$ %e' %out' %hh' with ⟨Hσ, HΦ⟩
    imodintro
    isplitl [Hc Hσ]
    · iapply fullInterp_of_cpu (M := M) c hc $$ [Hc Hσ]
      iframe Hc Hσ
    isplitl [HΦ]
    · iexists (e', out')
      iframe HΦ
      ipureintro; rfl
    iapply BigSepL.bigSepL_nil.2
    iempintro

theorem fupd_mTWP {Φ : Nat × String → IProp GF} :
    (|={⊤}=> mTWP (GF := GF) M Φ) ⊢ mTWP M Φ := by
  iintro H Htok
  iapply twp.fupd_twp
  imod H
  imodintro
  iapply H $$ Htok

theorem fupd_mWP {Φ : Nat × String → IProp GF} :
    (|={⊤}=> mWP (GF := GF) M Φ) ⊢ mWP M Φ := by
  iintro H Htok
  iapply fupd_wp
  imod H
  imodintro
  iapply H $$ Htok

end Rules

end VsaIris
