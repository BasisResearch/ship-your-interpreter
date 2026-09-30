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
  match n, h1, h31, hnoise, hwr with
  | 1, _, _, hn, hw => exact hframe (gprReg 1) hn hw
  | 2, _, _, hn, hw => exact hframe (gprReg 2) hn hw
  | 3, _, _, hn, hw => exact hframe (gprReg 3) hn hw
  | 4, _, _, hn, hw => exact hframe (gprReg 4) hn hw
  | 5, _, _, hn, hw => exact hframe (gprReg 5) hn hw
  | 6, _, _, hn, hw => exact hframe (gprReg 6) hn hw
  | 7, _, _, hn, hw => exact hframe (gprReg 7) hn hw
  | 8, _, _, hn, hw => exact hframe (gprReg 8) hn hw
  | 9, _, _, hn, hw => exact hframe (gprReg 9) hn hw
  | 10, _, _, hn, hw => exact hframe (gprReg 10) hn hw
  | 11, _, _, hn, hw => exact hframe (gprReg 11) hn hw
  | 12, _, _, hn, hw => exact hframe (gprReg 12) hn hw
  | 13, _, _, hn, hw => exact hframe (gprReg 13) hn hw
  | 14, _, _, hn, hw => exact hframe (gprReg 14) hn hw
  | 15, _, _, hn, hw => exact hframe (gprReg 15) hn hw
  | 16, _, _, hn, hw => exact hframe (gprReg 16) hn hw
  | 17, _, _, hn, hw => exact hframe (gprReg 17) hn hw
  | 18, _, _, hn, hw => exact hframe (gprReg 18) hn hw
  | 19, _, _, hn, hw => exact hframe (gprReg 19) hn hw
  | 20, _, _, hn, hw => exact hframe (gprReg 20) hn hw
  | 21, _, _, hn, hw => exact hframe (gprReg 21) hn hw
  | 22, _, _, hn, hw => exact hframe (gprReg 22) hn hw
  | 23, _, _, hn, hw => exact hframe (gprReg 23) hn hw
  | 24, _, _, hn, hw => exact hframe (gprReg 24) hn hw
  | 25, _, _, hn, hw => exact hframe (gprReg 25) hn hw
  | 26, _, _, hn, hw => exact hframe (gprReg 26) hn hw
  | 27, _, _, hn, hw => exact hframe (gprReg 27) hn hw
  | 28, _, _, hn, hw => exact hframe (gprReg 28) hn hw
  | 29, _, _, hn, hw => exact hframe (gprReg 29) hn hw
  | 30, _, _, hn, hw => exact hframe (gprReg 30) hn hw
  | 31, _, _, hn, hw => exact hframe (gprReg 31) hn hw
  | n + 32, _, h31, _, _ => exact absurd h31 (by omega)

end Vsa.Sim
