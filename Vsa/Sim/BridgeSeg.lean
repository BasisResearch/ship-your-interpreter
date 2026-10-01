import Vsa.Sim.BlockTactics2
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.EnvNewSpec

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.Alloc (AbiPreserved)

namespace Vsa.Sim

set_option maxHeartbeats 1600000
set_option maxRecDepth 1000000

def JalStep (calleeEntry link : BitVec 64) (σp : MState) (ip up : Nat) : Prop :=
  ∃ (σ2 : MState) (i2 : Nat),
    Step ⟨σp, ip, up⟩ ⟨σ2, i2, up + 1⟩ ∧ i2 < 2 ∧ GoodState σ2 ∧
    σ2.mem = σp.mem ∧
    σ2.regs.get? Register.PC = some calleeEntry ∧
    σ2.regs.get? Register.x1 = some link ∧
    (∃ w, σ2.regs.get? Register.minstret = some w) ∧

    (∀ (n : Nat), 1 ≤ n → n ≤ 31 → n ≠ 1 →
      ∀ (w : BitVec 64), gprGet σp n = some w → gprGet σ2 n = some w) ∧

    (∀ R, AbiPreserved R = true → σ2.regs.get? R = σp.regs.get? R)

theorem jalStep_of_obs {σp σ2 : MState} {ip up i2 : Nat}
    {jalPC vm : BitVec 64} {imm : BitVec 21} {calleeEntry link : BitVec 64}
    (hstep : Step ⟨σp, ip, up⟩ ⟨σ2, i2, up + 1⟩) (hi2 : i2 < 2) (hG2 : GoodState σ2)
    (hmem : σ2.mem = σp.mem)
    (hobs : ReadsLikePost σ2 (sigmaPost_jal σp jalPC vm imm Register.x1 link))
    (hce : jalPC + sign_extend (m := 64) imm = calleeEntry) :
    JalStep calleeEntry link σp ip up := by
  refine ⟨σ2, i2, hstep, hi2, hG2, hmem, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hce]; exact obs_jal_pc_env hobs
  · exact obs_jal_rd_env hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact obs_jal_minstret_env hobs
  ·
    intro n hn1 hn31 hne w hw
    match n, hn1, hn31, hne, hw with
    | 0, h, _, _, _ => exact absurd h (by omega)
    | 1, _, _, hne, _ => exact absurd rfl hne
    | 2, _, _, _, hw => exact obs_jal_other_env hobs Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 3, _, _, _, hw => exact obs_jal_other_env hobs Register.x3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 4, _, _, _, hw => exact obs_jal_other_env hobs Register.x4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 5, _, _, _, hw => exact obs_jal_other_env hobs Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 6, _, _, _, hw => exact obs_jal_other_env hobs Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 7, _, _, _, hw => exact obs_jal_other_env hobs Register.x7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 8, _, _, _, hw => exact obs_jal_other_env hobs Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 9, _, _, _, hw => exact obs_jal_other_env hobs Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 10, _, _, _, hw => exact obs_jal_other_env hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 11, _, _, _, hw => exact obs_jal_other_env hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 12, _, _, _, hw => exact obs_jal_other_env hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 13, _, _, _, hw => exact obs_jal_other_env hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 14, _, _, _, hw => exact obs_jal_other_env hobs Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 15, _, _, _, hw => exact obs_jal_other_env hobs Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 16, _, _, _, hw => exact obs_jal_other_env hobs Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 17, _, _, _, hw => exact obs_jal_other_env hobs Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 18, _, _, _, hw => exact obs_jal_other_env hobs Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 19, _, _, _, hw => exact obs_jal_other_env hobs Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 20, _, _, _, hw => exact obs_jal_other_env hobs Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 21, _, _, _, hw => exact obs_jal_other_env hobs Register.x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 22, _, _, _, hw => exact obs_jal_other_env hobs Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 23, _, _, _, hw => exact obs_jal_other_env hobs Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 24, _, _, _, hw => exact obs_jal_other_env hobs Register.x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 25, _, _, _, hw => exact obs_jal_other_env hobs Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 26, _, _, _, hw => exact obs_jal_other_env hobs Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 27, _, _, _, hw => exact obs_jal_other_env hobs Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 28, _, _, _, hw => exact obs_jal_other_env hobs Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 29, _, _, _, hw => exact obs_jal_other_env hobs Register.x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 30, _, _, _, hw => exact obs_jal_other_env hobs Register.x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 31, _, _, _, hw => exact obs_jal_other_env hobs Register.x31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | k+32, _, h, _, _ => exact absurd h (by omega)
  ·
    intro R hR
    exact (hobs.1 R (abiPreserved_ne hR (by decide)) (abiPreserved_ne hR (by decide))
        (abiPreserved_ne hR (by decide))).trans
      (get?_sigmaPost_jal σp jalPC vm imm Register.x1 link R
        (abiPreserved_ne hR (by decide)) (abiPreserved_ne hR (by decide))
        (abiPreserved_ne hR (by decide)) (abiPreserved_ne hR (by decide))
        (abiPreserved_ne hR (by decide)))

end Vsa.Sim
