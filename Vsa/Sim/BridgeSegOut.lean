import Vsa.Sim.BridgeSeg

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Alloc

/-- A reflected `jal` step that also exposes preservation of the output
stream.  `BridgeSeg.JalStep` omits this machine field. -/
def JalStepO (calleeEntry link : BitVec 64) (σp : MState) (ip up : Nat) : Prop :=
  ∃ (σ2 : MState) (i2 : Nat),
    Step ⟨σp, ip, up⟩ ⟨σ2, i2, up + 1⟩ ∧ i2 < 2 ∧ GoodState σ2 ∧
    σ2.mem = σp.mem ∧
    σ2.sailOutput = σp.sailOutput ∧
    σ2.regs.get? Register.PC = some calleeEntry ∧
    σ2.regs.get? Register.x1 = some link ∧
    (∃ w, σ2.regs.get? Register.minstret = some w) ∧
    (∀ (n : Nat), 1 ≤ n → n ≤ 31 → n ≠ 1 →
      ∀ (w : BitVec 64), gprGet σp n = some w → gprGet σ2 n = some w) ∧
    (∀ R, AbiPreserved R = true → σ2.regs.get? R = σp.regs.get? R)

/- Output-preserving upgrade of `jalStep_of_obs`. -/
theorem jalStepO_of_obs {σp σ2 : MState} {ip up i2 : Nat}
    {jalPC vm : BitVec 64} {imm : BitVec 21} {calleeEntry link : BitVec 64}
    (hstep : Step ⟨σp, ip, up⟩ ⟨σ2, i2, up + 1⟩) (hi2 : i2 < 2)
    (hG2 : GoodState σ2) (hmem : σ2.mem = σp.mem)
    (hobs : ReadsLikePost σ2
      (sigmaPost_jal σp jalPC vm imm Register.x1 link))
    (hce : jalPC + sign_extend (m := 64) imm = calleeEntry) :
    JalStepO calleeEntry link σp ip up := by
  obtain ⟨σ', i', hs, hi', hG', hmem', hpc', hra', hmi', hnonra', habi'⟩ :=
    jalStep_of_obs hstep hi2 hG2 hmem hobs hce
  have hdest : (⟨σ', i', up + 1⟩ : Config) = ⟨σ2, i2, up + 1⟩ :=
    Step.deterministic hs hstep
  cases hdest
  refine ⟨σ2, i2, hs, hi', hG', hmem', ?_, hpc', hra', hmi', hnonra', habi'⟩
  rw [hobs.out, sailOutput_sigmaPost_jal]

#print axioms jalStepO_of_obs

/-- Execute a reflected segment and its `jal`, preserving `sailOutput` across
both finite machine pieces. -/
theorem bridgeOfSegOut (bs : List BBlock) (L : GRegs)
    (lds : List (List (BitVec 8)))
    (σ : MState) (i u : Nat) (pc0 calleeEntry link vm : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some pc0)
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hmem : σ.mem = m0)
    (hL : GHolds σ L)
    (hkeys : KeysOK (keysG L))
    (hfacts : ChainFacts σ.mem σ.mem L lds bs)
    (hi : i < 2)
    (hwf : ChainOK pc0 (keysG L) bs)
    (hAvoid : WrChainAvoidAbi bs)
    (hKeysOut : KeysOK (keysG (evalBlocks bs (SegEvalState.init L lds)).regs))
    (hRaOut : KeysAvoidRa (evalBlocks bs (SegEvalState.init L lds)).regs)
    (hjal : ∀ (σ' : MState) (i' u' : Nat),
      GoodState σ' → i' < 2 →
      σ'.regs.get? Register.PC = some (evalBlocksPC pc0 (SegEvalState.init L lds) bs) →
      (∃ w, σ'.regs.get? Register.minstret = some w) →
      σ'.mem = writeLog m0 (evalBlocks bs (SegEvalState.init L lds)).log →
      GHolds σ' (evalBlocks bs (SegEvalState.init L lds)).regs →
      JalStepO calleeEntry link σ' i' u') :
    ∃ (σ2 : MState) (i2 : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ2, i2, u + evalBlocksFuel bs + 1⟩ ∧ i2 < 2 ∧ GoodState σ2 ∧
      σ2.regs.get? Register.PC = some calleeEntry ∧
      σ2.regs.get? Register.x1 = some link ∧
      (∃ w, σ2.regs.get? Register.minstret = some w) ∧
      GHolds σ2 (evalBlocks bs (SegEvalState.init L lds)).regs ∧
      σ2.mem = writeLog m0 (evalBlocks bs (SegEvalState.init L lds)).log ∧
      σ2.sailOutput = σ.sailOutput ∧
      (∀ R, AbiPreserved R = true → σ2.regs.get? R = σ.regs.get? R) := by
  obtain ⟨σ', i', hs, hi', hG', hmem', hout', hpc', hmi', hregs, hframe⟩ :=
    segEval_sound bs σ i u pc0 vm L lds hG hpc hmi hL hkeys hfacts hwf hi
  have habiBody : ∀ R, AbiPreserved R = true → σ'.regs.get? R = σ.regs.get? R :=
    abiFrame_of_wrChain hAvoid hframe
  rw [hmem] at hmem'
  obtain ⟨σ2, i2, hstep2, hi2, hG2, hmem2, hout2, hpc2, hra2, hmi2,
      hnonra2, habiJal⟩ :=
    hjal σ' i' (u + evalBlocksFuel bs) hG' hi' hpc' hmi' hmem' hregs
  refine ⟨σ2, i2, Steps.trans hs (Steps.single hstep2), hi2, hG2, hpc2, hra2,
    hmi2, ?_, ?_, ?_, ?_⟩
  · exact gholds_of_jal hnonra2 _ hKeysOut hRaOut hregs
  · rw [hmem2]; exact hmem'
  · rw [hout2]; exact hout'
  · intro R hR; exact (habiJal R hR).trans (habiBody R hR)

#print axioms bridgeOfSegOut

end Vsa.Sim
