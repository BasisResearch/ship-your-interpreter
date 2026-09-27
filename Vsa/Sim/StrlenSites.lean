import Vsa.Sim.StepObs
import Vsa.Sim.ExecuteAlu
import Vsa.Sim.ExecuteBranch
import Vsa.Sim.ExecuteLoad
import Vsa.Sim.MemLoadTotal
import Vsa.Sim.RegAccess
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part16
import Vsa.Sim.DecodeTable.Batch01Part28
import Vsa.Sim.DecodeTable.Batch02Part26
import Vsa.Sim.DecodeTable.Batch03Part15
import Vsa.Sim.DecodeTable.Batch03Part16
import Vsa.Sim.DecodeTable.Batch03Part23
import Vsa.Sim.DecodeTable.Batch04Part13
import Vsa.Sim.DecodeTable.Batch04Part14
import Vsa.Sim.DecodeTable.Batch04Part16
import Vsa.Sim.DecodeTable.Batch04Part18
import Vsa.Sim.DecodeTable.Batch04Part19
import Vsa.Sim.DecodeTable.Batch04Part29
import Vsa.Sim.DecodeTable.Batch05Part01
import Vsa.Sim.DecodeTable.Batch06Part25
import Vsa.Sim.DecodeTable.Batch07Part28
import Vsa.Sim.DecodeTable.Batch08Part14
import Vsa.Sim.DecodeTable.Batch08Part30
import Vsa.Sim.DecodeTable.Batch11Part20
import Vsa.Sim.DecodeTable.Batch13Part06
import Vsa.Sim.DecodeTable.Batch15Part25
import Vsa.Sim.DecodeTable.Batch15Part26
import Vsa.Sim.DecodeTable.Batch16Part11
import Vsa.Sim.DecodeTable.Batch16Part13
import Vsa.Sim.DecodeTable.Batch16Part21
import Vsa.Sim.DecodeTable.Batch16Part22
import Vsa.Sim.DecodeTable.Batch16Part23
import Vsa.Sim.DecodeTable.Batch16Part24
import Vsa.Sim.DecodeTable.Batch16Part25
import Vsa.Sim.DecodeTable.Batch16Part26
import Vsa.Sim.DecodeTable.Batch16Part28
import Vsa.Sim.Code.Strlen

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code (StrlenLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem exec_snez_a0_a5 (σ : MState) (pc : BitVec 64) (v15 : BitVec 64)
    (hx15 : σ.regs.get? Register.x15 = some v15) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0f#5, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, rop.SLTU))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x10 (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) v15)))) := by
  have hx15₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  exact execute_rtype_sltu_char (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0a#5)
    (0#64) v15 (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x10 (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) v15))))
    (rX_bits_zero _) (rX_bits_x15 _ v15 hx15₂)
    (wX_bits_x10 _ (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) v15))))

theorem snez_a0_a5_word :
    (((0x00#8).append (0xf0#8)).append (0x35#8)).append (0x33#8) = (0x00f03533#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem snez_a0_a5_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xf0#8)).append (0x35#8)).append (0x33#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem site_80006d64
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d64#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10
          (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) v15)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d64 hmem
  exact stepObs_alu σ i u (0x80006d64#64) vminstret (0x00f03533#32)
    (instruction.RTYPE (regidx.Regidx 0x0f#5, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, rop.SLTU))
    Register.x10 (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) v15)))
    (0x33#8) (0x35#8) (0xf0#8) (0x00#8)
    hG hpc hminstret snez_a0_a5_word snez_a0_a5_notrvc
    (Vsa.Sim.DecodeTable.decode_00f03533 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_snez_a0_a5 σ (0x80006d64#64) v15 hx15)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

end Vsa.Sim
