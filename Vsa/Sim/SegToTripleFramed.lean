import Vsa.Sim.BlockAdapter
import Vsa.Sim.DeriveCase

open LeanRV64DExecutable Vsa Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic (Triple)

namespace Vsa.Sim

def FrameOK (ks : List Nat) (bs : List BBlock) : Prop :=
  (∀ n ∈ ks, (1 ≤ n ∧ n ≤ 31) ∧
    (∀ rr ∈ noiseRegs, (rr == gprReg n) = false) ∧
    (∀ m ∈ wrChain bs, (gprReg m == gprReg n) = false)) ∧
  (∀ m ∈ wrChain bs, (gprReg m == Register.htif_payload_writes) = false ∧
    (gprReg m == Register.htif_tohost) = false)

instance instDecFrameOK (ks : List Nat) (bs : List BBlock) :
    Decidable (FrameOK ks bs) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem gprGet_of_frame {σ' σ : MState} {wrs : List Nat} (n : Nat)
    (h1 : 1 ≤ n) (h31 : n ≤ 31)
    (hnoise : ∀ rr ∈ noiseRegs, (rr == gprReg n) = false)
    (hwr : ∀ m ∈ wrs, (gprReg m == gprReg n) = false)
    (hframe : ∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
      (∀ m ∈ wrs, (gprReg m == R) = false) →
      σ'.regs.get? R = σ.regs.get? R) :
    gprGet σ' n = gprGet σ n := by
  gpr_cases n => exact hframe (gprReg _) hnoise hwr

end Vsa.Sim
