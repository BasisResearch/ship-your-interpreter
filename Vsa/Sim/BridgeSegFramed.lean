import Vsa.Sim.BridgeSeg

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.Alloc (AbiPreserved)

namespace Vsa.Sim

set_option maxHeartbeats 1600000
set_option maxRecDepth 1000000

theorem regAvoids_ne {P : Register → Bool} {R X : Register}
    (hR : P R = true) (hX : P X = false) : (X == R) = false := by
  rcases hXR : (X == R) with _ | _
  · rfl
  · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hR; exact absurd hR (by decide)

def WrChainAvoids (P : Register → Bool) (bs : List BBlock) : Prop :=
  ∀ n ∈ wrChain bs, P (gprReg n) = false

instance (P : Register → Bool) (bs : List BBlock) : Decidable (WrChainAvoids P bs) := by
  unfold WrChainAvoids; infer_instance

theorem noise_avoids {P : Register → Bool} (hnoiseP : ∀ rr ∈ noiseRegs, P rr = false)
    {R : Register} (hR : P R = true) : ∀ rr ∈ noiseRegs, (rr == R) = false :=
  fun rr hrr => regAvoids_ne hR (hnoiseP rr hrr)

theorem wrChain_avoids {P : Register → Bool} {bs : List BBlock}
    (hAvoid : WrChainAvoids P bs) {R : Register} (hR : P R = true) :
    ∀ n ∈ wrChain bs, (gprReg n == R) = false :=
  fun n hn => regAvoids_ne hR (hAvoid n hn)

theorem frame_of_wrChain_avoids {P : Register → Bool} {bs : List BBlock}
    {σ' σ : MState}
    (hnoiseP : ∀ rr ∈ noiseRegs, P rr = false)
    (hAvoid : WrChainAvoids P bs)
    (hframe : ∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
      (∀ n ∈ wrChain bs, (gprReg n == R) = false) →
      σ'.regs.get? R = σ.regs.get? R) :
    ∀ R, P R = true → σ'.regs.get? R = σ.regs.get? R :=
  fun R hR => hframe R (noise_avoids hnoiseP hR) (wrChain_avoids hAvoid hR)

end Vsa.Sim
