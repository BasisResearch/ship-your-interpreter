import VsaIris.Step
import Iris.ProgramLogic.Lifting

/-!
# The partial weakest precondition of the machine loop

`mWP M Φ` is MachCSL's `wp CpuLoop` (xv6iris `iris/RiscvPtsto.v:2804-2809`,
`wp_triv`) with an exit postcondition: the CPU token, then the partial WP of
the loop (iris-lean `ProgramLogic/WeakestPre.lean`) over the same lagging
state interpretation as the total `mTWP` (`Ptsto.fullInterp`).

Partial means: the machine is never stuck and every exit satisfies `Φ`;
divergence is allowed. That is the safety statement `stuck_sim` needs
(INTERP_DESIGN.md §1). Because the partial WP is a guarded fixpoint, each
machine step pays for one `▷`: `wp_stepRule` is the kernel's single-step rule
at `lat := ▷`, which gives every segment rule a later on its continuation
(`MachWP.runL` at `wpW`, INTERP_DESIGN.md's `run_later`). Löb consumes it at
the three recursive entry points.
-/

namespace VsaIris

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] (M : MachineModel)

/-- `wp CpuLoop` (RiscvPtsto.v:2809), partial, with an exit postcondition.
Its prover receives the CPU token, as for `mTWP`. -/
abbrev mWP (Φ : Nat × String → IProp GF) : IProp GF :=
  iprop(cpuTok -∗ WP (MachineModel.Loop M) @ Stuckness.NotStuck; ⊤ {{ Φ }})

end

section Rules

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] {M : MachineModel}

/-- The partial loop WP satisfies the single-step rule with one later
(iris-lean `wp_lift_step_fupd`). -/
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

/-- The exit rule of the partial WP (the partial twin of `wp_exec_halt`). -/
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

/-- The total WP implies the partial one (iris-lean `twp.to_wp`). Used only
where a partial proof reuses a result proved in total mode alone. -/
theorem twp_wp {Φ : Nat × String → IProp GF} : mTWP (GF := GF) M Φ ⊢ mWP M Φ := by
  iintro H Htok
  iapply twp.to_wp
  iapply H $$ Htok

/-- Fancy updates in front of the total loop WP are absorbed. -/
theorem fupd_mTWP {Φ : Nat × String → IProp GF} :
    (|={⊤}=> mTWP (GF := GF) M Φ) ⊢ mTWP M Φ := by
  iintro H Htok
  iapply twp.fupd_twp
  imod H
  imodintro
  iapply H $$ Htok

/-- Fancy updates in front of the partial loop WP are absorbed. -/
theorem fupd_mWP {Φ : Nat × String → IProp GF} :
    (|={⊤}=> mWP (GF := GF) M Φ) ⊢ mWP M Φ := by
  iintro H Htok
  iapply fupd_wp
  imod H
  imodintro
  iapply H $$ Htok

end Rules

end VsaIris
