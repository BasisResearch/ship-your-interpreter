import VsaIris.Vsa.Console
import Vsa.Sim.Muldi3Spec
import Vsa.Sim.SegToTripleFramed

/-!
# One observed ALU step as a run fact

The segment model (`MKind`) has no `sltiu`; `longjmp`'s `seqz a0,a1` is one.
VSA proves such a step as an observation `ReadsLikePost σ' (sigmaPost_alu …)`
(`JmpSites.site_80007074_jmp`). `aluObs_runFact` turns any such observation
of a write to GPR `rd` into the `RunFact` of `Wp.run`: the PC advances by 4,
`rd` takes the new value, every other register and all memory are unchanged,
nothing is printed.
-/

namespace VsaIris.Inst

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open LeanRV64DExecutable Sail
open Vsa.Machine (Config Step MState)
open Vsa.Sim

theorem gpr_avoids_noise' : ∀ n, n < 32 → 1 ≤ n → ∀ rr ∈ noiseRegs, (rr == gprReg n) = false := by
  decide

/-- **An observed ALU step writing `a0`**, at `i` with the code bytes `code`,
reading the registers `RR`. -/
theorem aluA0_runFact (live : Nat → Prop) (i : Nat) (MR : List (Nat × DFrac × BitVec 8))
    (RR : List (Nat × DFrac × BitVec 64)) (old new : BitVec 64)
    (hsite : ∀ c : Config, VsaOk live c →
      FootHolds (M := vsaModel live) c RR MR
        [(VsaIris.PC, BitVec.ofNat 64 i, BitVec.ofNat 64 (i + 4)), (10, old, new)] [] →
      ∃ (σ' : MState) (i' : Nat) (vm : BitVec 64),
        Step ⟨c.σ, c.tick, c.steps⟩ ⟨σ', i', c.steps + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
        σ'.mem = c.σ.mem ∧
        ReadsLikePost σ' (sigmaPost_alu c.σ (BitVec.ofNat 64 i) vm Register.x10 new)) :
    RunFact (vsaModel live) 0 RR MR
      [(VsaIris.PC, BitVec.ofNat 64 i, BitVec.ofNat 64 (i + 4)), (10, old, new)] [] := by
  intro c hok hfoot
  have hok : VsaOk live c := hok
  obtain ⟨σ', i', vm, hs, hi', hG', hmem, hobs⟩ := hsite c hok hfoot
  have hother : ∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
      (∀ m ∈ ([10] : List Nat), (gprReg m == R) = false) → σ'.regs.get? R = c.σ.regs.get? R := by
    intro R hn hw
    rw [hobs.1 R (hn _ (by decide)) (hn _ (by decide)) (hn _ (by decide))]
    exact get?_sigmaPost_alu _ _ _ _ _ R (hn _ (by decide)) (hn _ (by decide))
      (hw 10 (by simp)) (hn _ (by decide)) (hn _ (by decide))
  have hgpr : ∀ n, 1 ≤ n → n ≤ 31 → n ≠ 10 → gprGet σ' n = gprGet c.σ n := fun n h1 h31 hne =>
    gprGet_of_frame n h1 h31 (gpr_avoids_noise' n (by omega) h1)
      (fun m hm => by
        simp only [List.mem_singleton] at hm; subst hm
        exact gprReg_beq_false 10 (by omega) n (by omega) (by omega) h1 (Ne.symm hne))
      hother
  have hrdv : gprGet σ' 10 = some new :=
    obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  have hpc' : σ'.regs.get? Register.PC = some (BitVec.addInt (BitVec.ofNat 64 i) 4) :=
    obs_alu_pc hobs
  refine ⟨⟨σ', i', c.steps + 1⟩, .succ (vsaStep_of_step hs) (.zero _),
    ⟨hG', hi', fun n h1 h31 => ?_, fun a ha => ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · by_cases hn : n = 10
    · subst hn; rw [hrdv]; rfl
    · rw [hgpr n h1 h31 hn]; exact hok.gpr n h1 h31
  · change (σ'.mem[a]?).isSome; rw [hmem]; exact hok.live a ha
  · rw [hother _ (by decide) (fun m hm => by simp at hm; subst hm; rfl)]; exact hok.htifIdle
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hp
    rcases hp with rfl | rfl
    · change pcVal σ' = _
      unfold pcVal; rw [hpc', addInt_ofNat_four]; rfl
    · change vsaReg _ 10 = new
      rw [vsaReg_gpr (by decide)]; simp only [hrdv]; rfl
  · intro k hk
    have hk1 : VsaIris.PC ≠ k := hk _ List.mem_cons_self
    have hk2 : (10 : Nat) ≠ k := hk _ (.tail _ List.mem_cons_self)
    change vsaReg _ k = vsaReg c k
    rw [vsaReg_gpr (Ne.symm hk1), vsaReg_gpr (c := c) (Ne.symm hk1)]
    by_cases hr : 1 ≤ k ∧ k ≤ 31
    · rw [hgpr k hr.1 hr.2 (Ne.symm hk2)]
    · rw [gprGet_none (by omega), gprGet_none (by omega)]
  · intro p hp; cases hp
  · intro k _
    change (σ'.mem[k]?).getD 0 = (c.σ.mem[k]?).getD 0
    rw [hmem]
  · show Vsa.Machine.output σ' = Vsa.Machine.output c.σ
    unfold Vsa.Machine.output; rw [hobs.2]

section Wp

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- **The rule** for an observed ALU step writing `a0`, for either WP. `MR`
is the read footprint the observation needs (the code, at least). -/
theorem wp_aluA0W {live : Nat → Prop} (Wp : MachWP (GF := GF) (vsaModel live))
    {Φ : Nat × String → IProp GF} (i : Nat) (MR : List (Nat × DFrac × BitVec 8))
    (RR : List (Nat × DFrac × BitVec 64)) (old new : BitVec 64)
    (hsite : ∀ c : Config, VsaOk live c →
      FootHolds (M := vsaModel live) c RR MR
        [(VsaIris.PC, BitVec.ofNat 64 i, BitVec.ofNat 64 (i + 4)), (10, old, new)] [] →
      ∃ (σ' : MState) (i' : Nat) (vm : BitVec 64),
        Step ⟨c.σ, c.tick, c.steps⟩ ⟨σ', i', c.steps + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
        σ'.mem = c.σ.mem ∧
        ReadsLikePost σ' (sigmaPost_alu c.σ (BitVec.ofNat 64 i) vm Register.x10 new)) :
    sepL MR (fun p => p.1 ↦ₘ{p.2.1} p.2.2) ∗ VsaIris.PC ↦ᵣ BitVec.ofNat 64 i ∗
      (10 : Nat) ↦ᵣ old ∗ sepL RR (fun p => p.1 ↦ᵣ{p.2.1} p.2.2) ∗
      (VsaIris.PC ↦ᵣ BitVec.ofNat 64 (i + 4) -∗ (10 : Nat) ↦ᵣ new -∗
        sepL RR (fun p => p.1 ↦ᵣ{p.2.1} p.2.2) -∗ sepL MR (fun p => p.1 ↦ₘ{p.2.1} p.2.2) -∗
        Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨HMR, Hpc, Ha0, HRR, Hk⟩
  iapply Wp.run 0 RR MR _ [] (aluA0_runFact live i MR RR old new hsite)
  unfold footPre footPost
  simp only [sepL_cons, sepL_nil]
  iframe HRR HMR Hpc Ha0
  iintro ⟨HRR, HMR, ⟨Hpc, Ha0, -⟩, -⟩
  iapply Hk $$ Hpc Ha0 HRR HMR

end Wp

end VsaIris.Inst
