import Vsa.Sim.WriteLogNF
import Vsa.Sim.BlockTactics2

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Alloc (AbiPreserved)

namespace Vsa.Sim

def WrChainAvoidAbi (bs : List BBlock) : Prop :=
  ∀ n ∈ wrChain bs, AbiPreserved (gprReg n) = false

theorem noise_ne_abi {R : Register} (hR : AbiPreserved R = true) :
    ∀ rr ∈ noiseRegs, (rr == R) = false := by
  intro rr hrr
  simp only [noiseRegs, List.mem_cons, List.not_mem_nil, or_false] at hrr
  rcases hrr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact abiPreserved_ne hR (by decide)

theorem wrChain_ne_abi {bs : List BBlock} (hAvoid : WrChainAvoidAbi bs)
    {R : Register} (hR : AbiPreserved R = true) :
    ∀ n ∈ wrChain bs, (gprReg n == R) = false :=
  fun n hn => abiPreserved_ne hR (hAvoid n hn)

theorem abiFrame_of_wrChain {bs : List BBlock} {σ' σ : MState}
    (hAvoid : WrChainAvoidAbi bs)
    (hframe : ∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
      (∀ n ∈ wrChain bs, (gprReg n == R) = false) →
      σ'.regs.get? R = σ.regs.get? R) :
    ∀ R, AbiPreserved R = true → σ'.regs.get? R = σ.regs.get? R :=
  fun R hR => hframe R (noise_ne_abi hR) (wrChain_ne_abi hAvoid hR)

end Vsa.Sim
