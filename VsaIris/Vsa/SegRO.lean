import VsaIris.Vsa.AluStep

/-!
# Segments reading read-only registers

`wp_segW` owns every register of its pin list `L` exclusively. A segment
that reads a register the caller holds only persistently — `gp`, at every
`ld a5,1120(gp)` (`_impure_ptr`) — splits its pins: `Lw`, owned and written,
and `Lr`, read at any fraction and never written. `seg_runFactR` is
`seg_runFact` with that split; `wp_segRW` its rule.
-/

namespace VsaIris.Inst

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open LeanRV64DExecutable
open Vsa.Machine (Config Step Steps StepsN MState output)
open Vsa.Sim

/-- Written registers of a split segment: the PC and every written pin. -/
def segRWw (bs : List BBlock) (Lw Lr : GRegs) (lds : List (List (BitVec 8))) (pc0 : BitVec 64) :
    List (Nat × BitVec 64 × BitVec 64) :=
  (VsaIris.PC, pc0, evalBlocksPC pc0 (SegEvalState.init (Lw ++ Lr) lds) bs) ::
    Lw.map fun p => (p.1, p.2, finReg bs (Lw ++ Lr) lds p.1)

theorem seg_runFactR (live : Nat → Prop) (bs : List BBlock) (Lw Lr : GRegs)
    (lds : List (List (BitVec 8))) (pc0 : BitVec 64) (dq : DFrac)
    (MR : List (Nat × DFrac × BitVec 8)) (W : List (Nat × BitVec 8)) (n : Nat)
    (hlen : evalBlocksFuel bs = n + 1)
    (hwf : ChainOK pc0 (keysG (Lw ++ Lr)) bs) (hkeys : KeysOK (keysG (Lw ++ Lr)))
    (hwr : ∀ k ∈ wrChain bs, k ∈ keysG Lw)
    (hcover : ∀ a, (∀ p ∈ W, p.1 ≠ a) → OutL (segOut bs (Lw ++ Lr) lds).log a)
    (hfacts : ∀ c : Config, VsaOk live c →
      FootHolds (M := vsaModel live) c (Lr.map fun p => (p.1, dq, p.2)) MR
        (segRWw bs Lw Lr lds pc0) (segMW bs (Lw ++ Lr) lds W) →
      ChainFacts c.σ.mem c.σ.mem (Lw ++ Lr) lds bs) :
    RunFact (vsaModel live) n (Lr.map fun p => (p.1, dq, p.2)) MR (segRWw bs Lw Lr lds pc0)
      (segMW bs (Lw ++ Lr) lds W) := by
  intro c hok hfoot
  have hok : VsaOk live c := hok
  obtain ⟨hRR, hMR, hRW, hMW⟩ := hfoot
  have hfacts' := hfacts c hok ⟨hRR, hMR, hRW, hMW⟩
  have hpc : c.σ.regs.get? Register.PC = some pc0 := by
    have h := hRW _ List.mem_cons_self
    change pcVal c.σ = pc0 at h
    obtain ⟨v, hv⟩ := hok.good.PC
    unfold pcVal at h
    rw [hv] at h ⊢
    exact congrArg some h
  obtain ⟨vm, hmi⟩ := hok.good.minstret
  have hkeyL : ∀ p ∈ Lw ++ Lr, 1 ≤ p.1 ∧ p.1 ≤ 31 := fun p hp => hkeys p.1 (mem_keysG_of_mem hp)
  have hL : GHolds c.σ (Lw ++ Lr) := gholds_of_forall _ fun p hp => by
    have h1 := (hkeyL p hp).1; have h31 := (hkeyL p hp).2
    rcases List.mem_append.mp hp with hp | hp
    · exact gprGet_eq_of_vsaReg hok h1 h31
        (hRW (p.1, p.2, finReg bs (Lw ++ Lr) lds p.1)
          (.tail _ (List.mem_map_of_mem (f := fun p => (p.1, p.2, finReg bs (Lw ++ Lr) lds p.1)) hp)))
    · exact gprGet_eq_of_vsaReg hok h1 h31
        (hRR (p.1, dq, p.2) (List.mem_map_of_mem (f := fun p => (p.1, dq, p.2)) hp))
  obtain ⟨σ', i', hs, hi', hG', hmem', hout', hpc', _, hregs, hframe⟩ :=
    segEval_sound bs c.σ c.tick c.steps pc0 vm (Lw ++ Lr) lds hok.good hpc hmi hL hkeys hfacts'
      hwf hok.tick
  have hN : StepsN (n + 1) c ⟨σ', i', c.steps + evalBlocksFuel bs⟩ := by
    have h := Vsa.Machine.Steps.toN_of_stepsEq (k := evalBlocksFuel bs) hs rfl
    rw [show n + 1 = evalBlocksFuel bs from hlen.symm]
    exact h
  have hkout : ∀ k ∈ keysG (Lw ++ Lr), k ∈ keysG (segOut bs (Lw ++ Lr) lds).regs := fun k hk => by
    rw [evalBlocks_regs]; exact mem_keysG_runChain bs (Lw ++ Lr) lds hk
  have hkw : ∀ k ∈ keysG Lw, k ∈ keysG (Lw ++ Lr) := fun k hk => by
    obtain ⟨v, hv⟩ := exists_of_mem_keysG hk
    exact mem_keysG_of_mem (List.mem_append_left _ hv)
  have hwrne : ∀ k, k ∉ wrChain bs → 1 ≤ k → k ≤ 31 →
      ∀ m ∈ wrChain bs, (gprReg m == gprReg k) = false := fun k hk h1 h31 m hm => by
    have hm' := hkeys m (hkw m (hwr m hm))
    exact gprReg_beq_false m (by omega) k (by omega) hm'.1 h1 (fun e => hk (e ▸ hm))
  have hframeK : ∀ k, k ∉ wrChain bs → 1 ≤ k → k ≤ 31 → gprGet σ' k = gprGet c.σ k :=
    fun k hk h1 h31 =>
      gprGet_of_frame k h1 h31 (gpr_avoids_noise' k (by omega) h1) (hwrne k hk h1 h31) hframe
  have hfin : ∀ k ∈ keysG (Lw ++ Lr), gprGet σ' k = some (finReg bs (Lw ++ Lr) lds k) :=
    fun k hk => by
      obtain ⟨w, hw⟩ := lookupG_of_mem (hkout k hk)
      unfold finReg
      rw [hw]
      exact gholds_lookup _ hregs hw
  refine ⟨⟨σ', i', c.steps + evalBlocksFuel bs⟩, reachesN_of_stepsN hN, ?_, ?_,
    show output σ' = output c.σ by unfold output; rw [hout']⟩
  · refine ⟨hG', hi', fun k h1 h31 => ?_, fun a ha => ?_, ?_⟩
    · by_cases hk : k ∈ wrChain bs
      · rw [hfin k (hkw k (hwr k hk))]; rfl
      · rw [hframeK k hk h1 h31]; exact hok.gpr k h1 h31
    · show ((σ'.mem)[a]?).isSome
      rw [hmem']
      exact writeLog_present _ _ _ (hok.live a ha)
    · rw [hframe _ (by decide) (fun m _ => gprReg_htif_payload m)]
      exact hok.htifIdle
  · constructor
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · change vsaReg _ VsaIris.PC = _
        unfold vsaReg pcVal
        rw [ite_eq_left rfl]
        simp only [hpc']
        rfl
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        have hq' := hkeyL q (List.mem_append_left _ hq)
        change vsaReg _ q.1 = finReg bs (Lw ++ Lr) lds q.1
        rw [vsaReg_gpr (by unfold VsaIris.PC; omega)]
        simp only [hfin q.1 (hkw q.1 (mem_keysG_of_mem hq))]
        rfl
    · intro k hk
      have hkpc : k ≠ VsaIris.PC := fun e => hk _ List.mem_cons_self e.symm
      have hkL : k ∉ keysG Lw := fun hkL => by
        obtain ⟨v, hv⟩ := exists_of_mem_keysG hkL
        exact hk (k, v, finReg bs (Lw ++ Lr) lds k)
          (.tail _ (List.mem_map_of_mem
            (f := fun p => (p.1, p.2, finReg bs (Lw ++ Lr) lds p.1)) hv)) rfl
      change vsaReg _ k = vsaReg c k
      rw [vsaReg_gpr hkpc, vsaReg_gpr (c := c) hkpc]
      by_cases hr : 1 ≤ k ∧ k ≤ 31
      · rw [hframeK k (fun hw => hkL (hwr k hw)) hr.1 hr.2]
      · rw [gprGet_none (by omega), gprGet_none (by omega)]
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      change ((σ'.mem)[q.1]?).getD 0 =
        ((writeLog (wbase W) (segOut bs (Lw ++ Lr) lds).log)[q.1]?).getD 0
      rw [hmem']
      apply writeLog_getD_congr
      obtain ⟨o', ho', hg⟩ := wbase_get hq
      rw [hg]
      exact hMW (q.1, o', _) (List.mem_map_of_mem ho')
    · intro k hk
      change ((σ'.mem)[k]?).getD 0 = ((c.σ.mem)[k]?).getD 0
      rw [hmem', writeLog_out _ _ _ (hcover k fun p hp e =>
        hk (p.1, p.2, _) (List.mem_map_of_mem hp) e)]

section Wp

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- **The segment rule with read-only pins**, for either WP. -/
theorem wp_segRW {Φ : Nat × String → IProp GF} (live : Nat → Prop)
    (Wp : MachWP (GF := GF) (vsaModel live)) (bs : List BBlock) (Lw Lr : GRegs)
    (lds : List (List (BitVec 8))) (pc0 : BitVec 64) (dq : DFrac)
    (MR : List (Nat × DFrac × BitVec 8)) (W : List (Nat × BitVec 8)) (n : Nat)
    (hlen : evalBlocksFuel bs = n + 1)
    (hwf : ChainOK pc0 (keysG (Lw ++ Lr)) bs) (hkeys : KeysOK (keysG (Lw ++ Lr)))
    (hwr : ∀ k ∈ wrChain bs, k ∈ keysG Lw)
    (hcover : ∀ a, (∀ p ∈ W, p.1 ≠ a) → OutL (segOut bs (Lw ++ Lr) lds).log a)
    (hfacts : ∀ c : Config, VsaOk live c →
      FootHolds (M := vsaModel live) c (Lr.map fun p => (p.1, dq, p.2)) MR
        (segRWw bs Lw Lr lds pc0) (segMW bs (Lw ++ Lr) lds W) →
      ChainFacts c.σ.mem c.σ.mem (Lw ++ Lr) lds bs) :
    VsaIris.PC ↦ᵣ pc0 ∗ sepL Lw (fun p => p.1 ↦ᵣ p.2) ∗ sepL Lr (fun p => p.1 ↦ᵣ{dq} p.2) ∗
      sepL W (fun p => p.1 ↦ₘ p.2) ∗ sepL MR (fun p => p.1 ↦ₘ{p.2.1} p.2.2) ∗
      (VsaIris.PC ↦ᵣ evalBlocksPC pc0 (SegEvalState.init (Lw ++ Lr) lds) bs -∗
        sepL Lw (fun p => p.1 ↦ᵣ finReg bs (Lw ++ Lr) lds p.1) -∗
        sepL Lr (fun p => p.1 ↦ᵣ{dq} p.2) -∗
        sepL W (fun p => p.1 ↦ₘ newByte bs (Lw ++ Lr) lds W p.1) -∗
        sepL MR (fun p => p.1 ↦ₘ{p.2.1} p.2.2) -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨Hpc, HLw, HLr, HW, HMR, Hk⟩
  iapply Wp.run n (Lr.map fun p => (p.1, dq, p.2)) MR (segRWw bs Lw Lr lds pc0)
    (segMW bs (Lw ++ Lr) lds W)
    (seg_runFactR live bs Lw Lr lds pc0 dq MR W n hlen hwf hkeys hwr hcover hfacts)
  unfold footPre footPost segRWw segMW
  simp only [sepL_cons, sepL_map]
  iframe HLr HMR Hpc HLw HW
  iintro ⟨HLr, HMR, ⟨Hpc, HLw⟩, HW⟩
  iapply Hk $$ Hpc HLw HLr HW HMR

end Wp

end VsaIris.Inst
