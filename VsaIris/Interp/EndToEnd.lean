import VsaIris.Interp.TopEntryBoot
import VsaIris.Interp.TermSim
import VsaIris.Interp.StuckSim
import VsaIris.Interp.SupplyBoot
import VsaIris.Interp.Supply
import VsaIris.Adequacy
import Vsa.Refinement
import Vsa.Densify

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.Sym
open Vsa.While Vsa.RuntimeRepr Vsa.Sim.LayoutInstance

section

variable {GF : BundledGFunctors} [G : MachGS .hasLC GF] [I : InterpGS GF]

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

theorem partial_sim_of (Sp : Supplies) (H : Newlib.NewlibHoles) :
    ∀ p c, Vsa.Refine.Loaded interpRunLayout p c →
      Vsa.Machine.Diverges c ∨ ∃ out e, Vsa.Machine.Halts c out e ∧
        (e = 0 ∧ BigStep p out ∨ AbortCode e) := by
  intro p c hL
  obtain ⟨b⟩ := boot_of_loaded hL
  have hA : AdequacyHypP MachGF (vsaModel topLive) (regMap (vsaReg c) topRegs) (b.bytes b.G)
      (Vsa.Machine.output c.σ) (fun v => v.1 = 0 ∧ BigStep p v.2 ∨ AbortCode v.1) := by
    intro G
    show ⊢ _ -∗ _ -∗ _ -∗ (wpW (GF := MachGF) (vsaModel topLive)).W
      (fun v => iprop(⌜v.1 = 0 ∧ BigStep p v.2 ∨ AbortCode v.1⌝))
    iintro Hr Hm Hc
    ihave Hr := sepL_of_regMap (vsaReg c) topRegs topRegs_nodup $$ Hr
    iapply wp_of_bupd (wpW (vsaModel topLive))
      (Φ := fun v => iprop(⌜v.1 = 0 ∧ BigStep p v.2 ∨ AbortCode v.1⌝))
    iapply boundary_bind b _ (regimeOK_uncounted b.top) (R := sepL topRegs (fun r => r ↦ᵣ vsaReg c r))
      (fun γf γc => interpRun_partial_top (I := ⟨γf, γc⟩) H topLive_interp topLive_code b
        (execSpecsP_top (I := ⟨γf, γc⟩)
          (@Supplies.stuck Sp MachGF _ ⟨γf, γc⟩ b.N (nativeEntries_of b.ready.native_addrs)))
        (fun st' hst => by ipureintro; exact Or.inl ⟨rfl, st', hst, rfl⟩)
        (fun e o he => by ipureintro; exact Or.inr he))
    iframe Hm Hc Hr
  exact vsa_adequacyP topLive c (regMap (vsaReg c) topRegs) (b.bytes b.G)
    (regAgree_regMap (M := vsaModel topLive) c topRegs) (b.bytes_agree b.G topLive)
    (vsaOk_of_ready b.ready) _ hA

theorem stuck_codes_of (Sp : Supplies) (H : Newlib.NewlibHoles) :
    ∀ p c, Vsa.Refine.Loaded interpRunLayout p c → (¬ ∃ out, BigStep p out) →
      Vsa.Machine.Diverges c ∨ ∃ out e, Vsa.Machine.Halts c out e ∧ AbortCode e := by
  intro p c hL hnb
  rcases partial_sim_of Sp H p c hL with hd | ⟨out, e, hh, ⟨-, hb⟩ | hcode⟩
  · exact .inl hd
  · exact absurd ⟨out, hb⟩ hnb
  · exact .inr ⟨out, e, hh, hcode⟩

theorem stuck_sim_of (Sp : Supplies) (H : Newlib.NewlibHoles) :
    ∀ p c, Vsa.Refine.Loaded interpRunLayout p c → (¬ ∃ out, BigStep p out) →
      Vsa.Machine.Diverges c ∨ ∃ out e, Vsa.Machine.Halts c out e ∧ e ≠ 0 := by
  intro p c hL hnb
  rcases stuck_codes_of Sp H p c hL hnb with hd | ⟨out, e, hh, hcode⟩
  · exact .inl hd
  · exact .inr ⟨out, e, hh, hcode.ne_zero⟩

end VsaIris.Interp

namespace VsaIris.Interp

theorem newlibHoles_proved : VsaIris.Newlib.NewlibHoles :=
  VsaIris.Newlib.NewlibCore.full (VsaIris.Newlib.NewlibCoreAt.proved _) VsaIris.Newlib.fprintf_ok
    VsaIris.Sym.snprintf_ok

theorem interpSim_iris : Vsa.Refine.InterpSim Vsa.Sim.LayoutInstance.interpRunLayout :=
  ⟨term_sim_of supplies_of newlibHoles_proved, stuck_sim_of supplies_of newlibHoles_proved⟩

theorem partialSim_iris : ∀ p c, Vsa.Refine.Loaded Vsa.Sim.LayoutInstance.interpRunLayout p c →
    Vsa.Machine.Diverges c ∨ ∃ out e, Vsa.Machine.Halts c out e ∧
      (e = 0 ∧ Vsa.While.BigStep p out ∨ AbortCode e) :=
  partial_sim_of supplies_of newlibHoles_proved

end VsaIris.Interp

namespace Vsa.Sim.EndToEnd

open Vsa.While
open Vsa.Machine (Halts Diverges)
open Vsa.Refine (Loaded)
open Vsa.Sim.LayoutInstance (interpRunLayout)

open Vsa.Densify (fillZero halts_fillZero diverges_fillZero)

theorem endToEnd_refinement_loaded :
    ∀ p c, Loaded interpRunLayout p c →
      (∀ out, BigStep p out ↔ Halts c out 0) ∧
      (Diverges c → ¬ ∃ out, BigStep p out) :=
  Vsa.Refine.refinement VsaIris.Interp.interpSim_iris

theorem endToEnd_refinement :
    ∀ p c, Loaded interpRunLayout p (fillZero c) →
      (∀ out, BigStep p out ↔ Halts c out 0) ∧
      (Diverges c → ¬ ∃ out, BigStep p out) := by
  intro p c hL
  obtain ⟨h1, h2⟩ := endToEnd_refinement_loaded p (fillZero c) hL
  exact ⟨fun out => (h1 out).trans (halts_fillZero c out 0).symm,
    fun hd => h2 ((diverges_fillZero c).1 hd)⟩

end Vsa.Sim.EndToEnd
