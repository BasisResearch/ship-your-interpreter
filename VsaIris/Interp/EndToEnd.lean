import VsaIris.Interp.TopEntryBoot
import VsaIris.Interp.TermSim
import VsaIris.Interp.StuckSim
import VsaIris.Interp.Holes
import VsaIris.Interp.SupplyBoot
import VsaIris.Adequacy
import Vsa.Refinement

/-!
# The end-to-end theorem on the Iris route (package A)

INTERP_DESIGN.md §5.2-§5.4. From `Loaded interpRunLayout p c`:

* `term_sim_iris`: a big-step behaviour `BigStep p out` gives a costed
  derivation (`Boot.regime_of_bigStep`), the counted boundary world
  (`world_of_boundary`), the total recursion (`interpSeqT_all`), `interp_run`'s
  whole run (`interpRun_total_top`: `main` returns 0, `exit(0)` quiet), and
  total adequacy (`vsa_adequacy_exit`): `Halts c out 0`.
* `stuck_sim_iris`: the uncounted world, the Löb (`specsP_all`), the whole
  run (`interpRun_partial_top`: a normal end hands a derivation, which the
  hypothesis refutes; every other end exits nonzero), and partial adequacy
  (`vsa_adequacyP_nonzero`).
* `endToEnd_refinement`: `Vsa.Refine.refinement` (unchanged) of the two.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.Sym
open Vsa.While Vsa.RuntimeRepr Vsa.Sim.LayoutInstance

/-- The helper specs of the total and partial cases, for every Iris
instance, from the holes. -/
structure Supplies : Prop where
  term : ∀ {GF : BundledGFunctors} [G : MachGS .hasLC GF] [I : InterpGS GF] (N : NativeAddrs),
    NativeEntries N → TermSupply (GF := GF) topLive N inpTop
  stuck : ∀ {GF : BundledGFunctors} [G : MachGS .hasLC GF] [I : InterpGS GF] (N : NativeAddrs),
    NativeEntries N → StuckSupply (GF := GF) topLive N inpTop

section

variable {GF : BundledGFunctors} [G : MachGS .hasLC GF] [I : InterpGS GF]

/-- The partial specs under the error context, as `interp_run`'s loop takes
them. -/
theorem execSpecsP_top {N : NativeAddrs} (S : StuckSupply (GF := GF) topLive N inpTop) :
    errCtx (GF := GF) inpTop ⊢
      execSpecsP (vsaModel topLive) N vsaLayoutP vsaRoomB inpTop (evalCore N vsaLayoutP vsaRoomB inpTop) := by
  refine .trans ?_ (execSpecsP_of_disps S.hlive _)
  refine (specsP_all S).trans ?_
  unfold execDispsP
  iintro #H
  imodintro
  inext
  iintro %st %d %env %sm
  iapply and_elim_r $$ H

end

/-- Bind the boundary's ghost names. -/
theorem boundary_bind {c : Vsa.Machine.Config} {p : Program} (b : Boot c p) (ρ : Regime)
    (hρ : RegimeOK b.top ρ) {R Q : IProp MachGF} [MachGS .hasLC MachGF]
    (h : ∀ γf γc : GName, (letI : InterpGS MachGF := ⟨γf, γc⟩; bootRes b ρ) ∗ R ⊢ |==> Q) :
    (([∗map] k ↦ v ∈ b.bytes b.G, iprop(k ↦ₘ v)) ∗ consoleOwn (GF := MachGF) (Vsa.Machine.output c.σ)) ∗ R
      ⊢ |==> Q := by
  iintro ⟨Hw, HR⟩
  imod world_of_boundary b ρ hρ $$ Hw with Hx
  icases Hx with ⟨%γf, %γc, Hb⟩
  iapply h γf γc
  iframe Hb HR

theorem wp_of_bupd {GF : BundledGFunctors} [MachGS .hasLC GF] {M : MachineModel}
    (Wp : MachWP (GF := GF) M) {Φ : Nat × String → IProp GF} : (|==> Wp.W Φ) ⊢ Wp.W Φ :=
  BIUpdateFUpdate.fupd_of_bupd.trans Wp.fupd

/-- **`term_sim` on the Iris route.** -/
theorem term_sim_of (Sp : Supplies) (H : Newlib.NewlibHoles) :
    ∀ p c out, Vsa.Refine.Loaded interpRunLayout p c → BigStep p out →
      Vsa.Machine.Halts c out 0 := by
  intro p c out hL hb
  obtain ⟨b⟩ := boot_of_loaded hL
  obtain ⟨st', n, D, hout, hρ⟩ := b.regime_of_bigStep hb
  have hA : AdequacyHyp MachGF (vsaModel topLive) (regMap (vsaReg c) topRegs) (b.bytes b.G)
      (Vsa.Machine.output c.σ) (fun v => v = (0, st'.out)) := by
    intro G
    show ⊢ _ -∗ _ -∗ _ -∗ (twpW (GF := MachGF) (vsaModel topLive)).W (fun v => iprop(⌜v = (0, st'.out)⌝))
    iintro Hr Hm Hc
    ihave Hr := sepL_of_regMap (vsaReg c) topRegs topRegs_nodup $$ Hr
    iapply wp_of_bupd (twpW (vsaModel topLive)) (Φ := fun v => iprop(⌜v = (0, st'.out)⌝))
    iapply boundary_bind b _ hρ (R := sepL topRegs (fun r => r ↦ᵣ vsaReg c r)) (fun γf γc =>
      interpRun_total_top (I := ⟨γf, γc⟩) H topLive_interp topLive_code b D
        (interpSeqT_all (I := ⟨γf, γc⟩)
          (@Supplies.term Sp MachGF _ ⟨γf, γc⟩ b.N (nativeEntries_of b.ready.native_addrs)) D))
    iframe Hm Hc Hr
  obtain ⟨e, out', hh, heq⟩ := vsa_adequacy_exit (GF := MachGF) topLive c
    (regMap (vsaReg c) topRegs) (b.bytes b.G) (regAgree_regMap (M := vsaModel topLive) c topRegs)
    (b.bytes_agree b.G topLive) (vsaOk_of_ready b.ready) (fun v => v = (0, st'.out)) hA
  cases heq; rw [hout] at hh; exact hh

/-- **`stuck_sim` on the Iris route.** -/
theorem stuck_sim_of (Sp : Supplies) (H : Newlib.NewlibHoles) :
    ∀ p c, Vsa.Refine.Loaded interpRunLayout p c → (¬ ∃ out, BigStep p out) →
      Vsa.Machine.Diverges c ∨ ∃ out e, Vsa.Machine.Halts c out e ∧ e ≠ 0 := by
  intro p c hL hnb
  obtain ⟨b⟩ := boot_of_loaded hL
  have hA : AdequacyHypP MachGF (vsaModel topLive) (regMap (vsaReg c) topRegs) (b.bytes b.G)
      (Vsa.Machine.output c.σ) (fun v => v.1 ≠ 0) := by
    intro G
    show ⊢ _ -∗ _ -∗ _ -∗ (wpW (GF := MachGF) (vsaModel topLive)).W (fun v => iprop(⌜v.1 ≠ 0⌝))
    iintro Hr Hm Hc
    ihave Hr := sepL_of_regMap (vsaReg c) topRegs topRegs_nodup $$ Hr
    iapply wp_of_bupd (wpW (vsaModel topLive)) (Φ := fun v => iprop(⌜v.1 ≠ 0⌝))
    iapply boundary_bind b _ (regimeOK_uncounted b.top) (R := sepL topRegs (fun r => r ↦ᵣ vsaReg c r))
      (fun γf γc => interpRun_partial_top (I := ⟨γf, γc⟩) H topLive_interp topLive_code b
        (execSpecsP_top (I := ⟨γf, γc⟩)
          (@Supplies.stuck Sp MachGF _ ⟨γf, γc⟩ b.N (nativeEntries_of b.ready.native_addrs)))
        (fun st' hst => absurd ⟨st'.out, st', hst, rfl⟩ hnb)
        (fun e o he => by ipureintro; exact he))
    iframe Hm Hc Hr
  exact vsa_adequacyP_nonzero topLive c (regMap (vsaReg c) topRegs) (b.bytes b.G)
    (regAgree_regMap (M := vsaModel topLive) c topRegs) (b.bytes_agree b.G topLive)
    (vsaOk_of_ready b.ready) hA

end VsaIris.Interp
