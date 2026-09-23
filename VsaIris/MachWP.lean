import VsaIris.PartialWP

/-!
# `MachWP`: the WP interface every block is proved against

INTERP_DESIGN.md §1. A block of machine code (a reflected segment, a helper
call, a fuel-bounded loop) is proved ONCE, for an abstract `Wp : MachWP M`,
and serves both directions of the refinement:

* `twpW M` (total, `mTWP`) for `term_sim`;
* `wpW M` (partial, `mWP`) for `stuck_sim`.

The interface is the lag kernel (`Lag.lean`) at the WP level (`lagRun`), the
exit rule (`halt`), and update absorption (`fupd`). `lat` is the modality one
machine step pays for: the identity for `twpW`, `▷` for `wpW`. Block lemmas
use the later-free rules (`MachWP.run`, `wp_localRunW`); only the mode-specific
Löb proofs of the three recursive entry points use `MachWP.runL` at `wpW`
(INTERP_DESIGN.md's `run_later`), where `lat` is definitionally `▷`.

F2 adds a `putc` field (the console step) and restates `halt` against the
console cell.
-/

namespace VsaIris

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- The WP interface (INTERP_DESIGN.md §1, "The shared interface"). -/
structure MachWP (M : MachineModel) where
  /-- The weakest precondition of the rest of the run, with an exit
  postcondition. -/
  W : (Nat × String → IProp GF) → IProp GF
  /-- The modality one machine step pays for (`id` total, `▷` partial). -/
  lat : IProp GF → IProp GF
  lat_intro : ∀ P, P ⊢ lat P
  /-- The lag kernel: own a run's footprint, and prove the rest of the run from
  the committed footprint of every possible end state. -/
  lagRun : ∀ {Φ : Nat × String → IProp GF} {Fp : IProp GF} {Fp' : M.State → IProp GF}
    {Pre : M.State → Prop} {Post : M.State → M.State → Prop} {K : Nat},
    LagFoot M Fp Fp' Pre Post K →
      Fp ∗ (∀ σ σf, ⌜Post σ σf⌝ -∗ Fp' σf -∗ lat (W Φ)) ⊢ W Φ
  /-- The exit rule (`wp_exec_halt`). -/
  halt : ∀ {Φ : Nat × String → IProp GF},
    (∀ σ, mstateInterp (GF := GF) M σ ={⊤}=∗
        ⌜∃ e out, M.step σ = .halt e out⌝ ∗
        ∀ e out, ⌜M.step σ = .halt e out⌝ ={⊤}=∗ mstateInterp M σ ∗ Φ (e, out))
    ⊢ W Φ
  /-- Fancy updates (ghost allocation, discarding fractions) are absorbed. -/
  fupd : ∀ {Φ : Nat × String → IProp GF}, (|={⊤}=> W Φ) ⊢ W Φ

variable {M : MachineModel}

/-- The total instance. -/
def twpW (M : MachineModel) : MachWP (GF := GF) M where
  W := mTWP M
  lat P := P
  lat_intro _ := .rfl
  lagRun {Φ} {_ Fp' _ Post K} hf := by
    have next : ∀ σ σf, Post σ σf →
        cpuTok ∗ Fp' σf ∗ iprop(∀ σ σf, ⌜Post σ σf⌝ -∗ Fp' σf -∗ mTWP M Φ) ⊢
          WP (MachineModel.Loop M) @ Stuckness.NotStuck; ⊤ [{ Φ }] := by
      intro σ σf hp
      iintro ⟨Htok, Hf, Hk⟩
      iapply Hk $$ %σ %σf %hp Hf Htok
    iintro ⟨Hf, Hk⟩ Htok
    iapply lag_run (M := M) (lat := fun P => P) (fun _ => .rfl) twp_stepRule hf _ next K 0
      (by omega)
    unfold cpuTok
    iframe Htok Hf Hk
  halt := wp_exec_halt
  fupd := fupd_mTWP

/-- The partial instance. -/
def wpW (M : MachineModel) : MachWP (GF := GF) M where
  W := mWP M
  lat P := iprop(▷ P)
  lat_intro _ := later_intro
  lagRun {Φ} {_ Fp' _ Post K} hf := by
    have next : ∀ σ σf, Post σ σf →
        cpuTok ∗ Fp' σf ∗ iprop(∀ σ σf, ⌜Post σ σf⌝ -∗ Fp' σf -∗ ▷ mWP M Φ) ⊢
          ▷ WP (MachineModel.Loop M) @ Stuckness.NotStuck; ⊤ {{ Φ }} := by
      intro σ σf hp
      iintro ⟨Htok, Hf, Hk⟩
      ihave Hw := Hk $$ %σ %σf %hp Hf
      inext
      iapply Hw $$ Htok
    iintro ⟨Hf, Hk⟩ Htok
    iapply lag_run (M := M) (lat := fun P => iprop(▷ P)) (fun _ => later_intro) wp_stepRule hf
      _ next K 0 (by omega)
    unfold cpuTok
    iframe Htok Hf Hk
  halt := wpP_exec_halt
  fupd := fupd_mWP

@[simp] theorem twpW_W : (twpW (GF := GF) M).W = mTWP M := rfl
@[simp] theorem wpW_W : (wpW (GF := GF) M).W = mWP M := rfl
@[simp] theorem wpW_lat (P : IProp GF) : (wpW (GF := GF) M).lat P = iprop(▷ P) := rfl

namespace MachWP

variable (Wp : MachWP (GF := GF) M)

/-- **The segment rule, with the step modality** (`run_later` at `wpW`). A
`RunFact` run of `n + 1` steps: own its footprint, and prove the rest of the
run, under `Wp.lat`, from the updated footprint. Everything else the caller
owns is framed by the wand. -/
theorem runL {Φ : Nat × String → IProp GF} (n : Nat)
    (RR : List (Nat × DFrac × BitVec 64)) (MR : List (Nat × DFrac × BitVec 8))
    (RW : List (Nat × BitVec 64 × BitVec 64)) (MW : List (Nat × BitVec 8 × BitVec 8))
    (hexec : RunFact M n RR MR RW MW) :
    footPre (GF := GF) RR MR RW MW ∗ (footPost RR MR RW MW -∗ Wp.lat (Wp.W Φ)) ⊢ Wp.W Φ := by
  iintro ⟨Hf, Hk⟩
  iapply Wp.lagRun hexec.lagFoot
  iframe Hf
  iintro %_ %_ %_ Hf
  iapply Hk $$ Hf

/-- **The segment rule** (`wp_run`), for either WP. -/
theorem run {Φ : Nat × String → IProp GF} (n : Nat)
    (RR : List (Nat × DFrac × BitVec 64)) (MR : List (Nat × DFrac × BitVec 8))
    (RW : List (Nat × BitVec 64 × BitVec 64)) (MW : List (Nat × BitVec 8 × BitVec 8))
    (hexec : RunFact M n RR MR RW MW) :
    footPre (GF := GF) RR MR RW MW ∗ (footPost RR MR RW MW -∗ Wp.W Φ) ⊢ Wp.W Φ := by
  iintro ⟨Hf, Hk⟩
  iapply Wp.runL n RR MR RW MW hexec
  iframe Hf
  iintro Hf
  iapply Wp.lat_intro
  iapply Hk $$ Hf

/-- `wp_instr` in footprint form: the one-step case of `run`. -/
theorem local_step {Φ : Nat × String → IProp GF}
    (RR : List (Nat × DFrac × BitVec 64)) (MR : List (Nat × DFrac × BitVec 8))
    (RW : List (Nat × BitVec 64 × BitVec 64)) (MW : List (Nat × BitVec 8 × BitVec 8))
    (hexec : ∀ σ, M.ok σ → FootHolds (M := M) σ RR MR RW MW →
      ∃ σ', M.step σ = .next σ' ∧ M.ok σ' ∧ LocalStep (M := M) σ σ' RW MW) :
    footPre (GF := GF) RR MR RW MW ∗ (footPost RR MR RW MW -∗ Wp.W Φ) ⊢ Wp.W Φ :=
  Wp.run 0 RR MR RW MW fun σ hok hf => by
    obtain ⟨σ', hs, hok', hloc⟩ := hexec σ hok hf
    exact ⟨σ', .succ hs (.zero σ'), hok', hloc⟩

/-- The one-step rule with the step modality. -/
theorem local_stepL {Φ : Nat × String → IProp GF}
    (RR : List (Nat × DFrac × BitVec 64)) (MR : List (Nat × DFrac × BitVec 8))
    (RW : List (Nat × BitVec 64 × BitVec 64)) (MW : List (Nat × BitVec 8 × BitVec 8))
    (hexec : ∀ σ, M.ok σ → FootHolds (M := M) σ RR MR RW MW →
      ∃ σ', M.step σ = .next σ' ∧ M.ok σ' ∧ LocalStep (M := M) σ σ' RW MW) :
    footPre (GF := GF) RR MR RW MW ∗ (footPost RR MR RW MW -∗ Wp.lat (Wp.W Φ)) ⊢ Wp.W Φ :=
  Wp.runL 0 RR MR RW MW fun σ hok hf => by
    obtain ⟨σ', hs, hok', hloc⟩ := hexec σ hok hf
    exact ⟨σ', .succ hs (.zero σ'), hok', hloc⟩

end MachWP

/-! ## The historical names, at the total instance -/

/-- **The segment rule** for the total WP. If from every well-formed state
satisfying the footprint the machine runs `n + 1` steps with an effect
confined to the written cells (`RunFact`), then owning the footprint and
proving the rest of the run from the updated footprint proves the run.
Everything the caller owns outside the footprint is framed by the wand (paper
§4.6). -/
theorem wp_run {Φ : Nat × String → IProp GF} (n : Nat)
    (RR : List (Nat × DFrac × BitVec 64)) (MR : List (Nat × DFrac × BitVec 8))
    (RW : List (Nat × BitVec 64 × BitVec 64)) (MW : List (Nat × BitVec 8 × BitVec 8))
    (hexec : RunFact M n RR MR RW MW) :
    footPre (GF := GF) RR MR RW MW ∗ (footPost RR MR RW MW -∗ mTWP M Φ) ⊢ mTWP M Φ :=
  (twpW M).run n RR MR RW MW hexec

/-- `wp_instr` in footprint form for the total WP. -/
theorem wp_local_step {Φ : Nat × String → IProp GF}
    (RR : List (Nat × DFrac × BitVec 64)) (MR : List (Nat × DFrac × BitVec 8))
    (RW : List (Nat × BitVec 64 × BitVec 64)) (MW : List (Nat × BitVec 8 × BitVec 8))
    (hexec : ∀ σ, M.ok σ → FootHolds (M := M) σ RR MR RW MW →
      ∃ σ', M.step σ = .next σ' ∧ M.ok σ' ∧ LocalStep (M := M) σ σ' RW MW) :
    footPre (GF := GF) RR MR RW MW ∗ (footPost RR MR RW MW -∗ mTWP M Φ) ⊢ mTWP M Φ :=
  (twpW M).local_step RR MR RW MW hexec

/-- **`run_later`**: the partial segment rule, whose continuation may assume
a later. Löb pays for recursion with it. -/
theorem wp_run_later {Φ : Nat × String → IProp GF} (n : Nat)
    (RR : List (Nat × DFrac × BitVec 64)) (MR : List (Nat × DFrac × BitVec 8))
    (RW : List (Nat × BitVec 64 × BitVec 64)) (MW : List (Nat × BitVec 8 × BitVec 8))
    (hexec : RunFact M n RR MR RW MW) :
    footPre (GF := GF) RR MR RW MW ∗ (footPost RR MR RW MW -∗ ▷ mWP M Φ) ⊢ mWP M Φ :=
  (wpW M).runL n RR MR RW MW hexec

end

end VsaIris
