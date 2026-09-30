import VsaIris.PartialWP

namespace VsaIris

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

structure MachWP (M : MachineModel) where

  W : (Nat × String → IProp GF) → IProp GF

  lat : IProp GF → IProp GF
  lat_intro : ∀ P, P ⊢ lat P

  lagRun : ∀ {Φ : Nat × String → IProp GF} {Fp : IProp GF} {Fp' : M.State → IProp GF}
    {Pre : M.State → Prop} {Post : M.State → M.State → Prop} {K : Nat},
    LagFoot M Fp Fp' Pre Post K →
      Fp ∗ (∀ σ σf, ⌜Post σ σf⌝ -∗ Fp' σf -∗ lat (W Φ)) ⊢ W Φ

  halt : ∀ {Φ : Nat × String → IProp GF},
    (∀ σ, mstateInterp (GF := GF) M σ ={⊤}=∗
        ⌜∃ e out, M.step σ = .halt e out⌝ ∗
        ∀ e out, ⌜M.step σ = .halt e out⌝ ={⊤}=∗ mstateInterp M σ ∗ Φ (e, out))
    ⊢ W Φ

  fupd : ∀ {Φ : Nat × String → IProp GF}, (|={⊤}=> W Φ) ⊢ W Φ

variable {M : MachineModel}

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

theorem local_stepL {Φ : Nat × String → IProp GF}
    (RR : List (Nat × DFrac × BitVec 64)) (MR : List (Nat × DFrac × BitVec 8))
    (RW : List (Nat × BitVec 64 × BitVec 64)) (MW : List (Nat × BitVec 8 × BitVec 8))
    (hexec : ∀ σ, M.ok σ → FootHolds (M := M) σ RR MR RW MW →
      ∃ σ', M.step σ = .next σ' ∧ M.ok σ' ∧ LocalStep (M := M) σ σ' RW MW ∧
        M.out σ' = M.out σ) :
    footPre (GF := GF) RR MR RW MW ∗ (footPost RR MR RW MW -∗ Wp.lat (Wp.W Φ)) ⊢ Wp.W Φ :=
  Wp.runL 0 RR MR RW MW fun σ hok hf => by
    obtain ⟨σ', hs, hok', hloc, hout⟩ := hexec σ hok hf
    exact ⟨σ', .succ hs (.zero σ'), hok', hloc, hout⟩

theorem haltConsole {Φ : Nat × String → IProp GF}
    (RR : List (Nat × DFrac × BitVec 64)) (MR : List (Nat × DFrac × BitVec 8)) (e : Nat)
    (s : String) (hh : HaltFact M RR MR e) :
    footPre (GF := GF) RR MR [] [] ∗ consoleOwn s ∗ Φ (e, s) ⊢ Wp.W Φ := by
  iintro ⟨Hf, Hs, HΦ⟩
  iapply Wp.halt
  unfold mstateInterp regInterp memInterp conInterp
  iintro %σ ⟨⟨%mr, Hmr, %hr⟩, ⟨%mm, Hmm, %hm⟩, ⟨%mo, Hmo, %ho⟩, %hok⟩
  ihave ⟨Hmr, Hmm, Hf, %hfoot⟩ := foot_lookup (M := M) mr mm RR MR [] [] $$ [Hmr Hmm Hf]
  · iframe Hmr Hmm Hf
  unfold consoleOwn
  ihave %hs := ghost_map_lookup $$ Hmo Hs
  have hstep := hh σ hok (hfoot σ hr hm)
  rw [ho s hs] at hstep
  imodintro
  isplitr
  · ipureintro; exact ⟨_, _, hstep⟩
  iintro %e' %out' %hh'
  rw [hstep] at hh'
  cases hh'
  imodintro
  iframe HΦ
  isplitl [Hmr]
  · iexists mr; iframe Hmr; ipureintro; exact hr
  isplitl [Hmm]
  · iexists mm; iframe Hmm; ipureintro; exact hm
  isplitl [Hmo]
  · iexists mo; iframe Hmo; ipureintro; exact ho
  ipureintro; exact hok

end MachWP

end

end VsaIris
