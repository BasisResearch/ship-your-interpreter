import Vsa.Sim.DecodeTable.Batch03Part15
import Vsa.Sim.DecodeTable.Batch03Part16
import Vsa.Sim.DecodeTable.Batch03Part31
import Vsa.Sim.DecodeTable.Batch04Part09
import Vsa.Sim.DecodeTable.Batch07Part23
import Vsa.Sim.DecodeTable.Batch08Part13
import Vsa.Sim.DecodeTable.Batch08Part14
import Vsa.Sim.DecodeTable.Batch08Part19
import Vsa.Sim.DecodeTable.Batch09Part18
import Vsa.Sim.DecodeTable.Batch11Part23
import Vsa.Sim.DecodeTable.Batch16Part21
import Vsa.Sim.MemcpySites2
import Vsa.Sim.DecodeTable.Batch03Part21
import Vsa.Sim.DecodeTable.Batch03Part23
import Vsa.Sim.DecodeTable.Batch04Part11
import Vsa.Sim.DecodeTable.Batch16Part27

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code (MemcpyLoaded memcpy_at_80006bc8 memcpy_at_80006bcc memcpy_at_80006bd0 memcpy_at_80006bd4 memcpy_at_80006bd8 memcpy_at_80006bdc memcpy_at_80006be0 memcpy_at_80006be4 memcpy_at_80006be8 memcpy_at_80006bec memcpy_at_80006bf0 memcpy_at_80006bf4 memcpy_at_80006bf8 memcpy_at_80006c3c)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem exec_bd8 (σ : MState) (pc : BitVec 64) (v12 : BitVec 64)
    (hx12 : σ.regs.get? Register.x12 = some v12) :
    (execute (instruction.ITYPE (0x008#12, regidx.Regidx 0x0c#5, regidx.Regidx 0x0c#5, iop.SLTIU))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x12
            (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v12 (sign_extend (m := 64) (0x008#12)))))) := by
  have h₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x12 = some v12 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx12
  exact execute_itype_sltiu_char (0x008#12) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0c#5) v12
    (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x12
      (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v12 (sign_extend (m := 64) (0x008#12))))))
    (rX_bits_x12 _ v12 h₂)
    (wX_bits_x12 _ (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v12 (sign_extend (m := 64) (0x008#12))))))

theorem site_80006bd8
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006bd8#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x12
          (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v12 (sign_extend (m := 64) (0x008#12)))))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006bd8 hmem
  exact stepObs_alu σ i u (0x80006bd8#64) vminstret (0x00863613#32)
    (instruction.ITYPE (0x008#12, regidx.Regidx 0x0c#5, regidx.Regidx 0x0c#5, iop.SLTIU))
    Register.x12 (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v12 (sign_extend (m := 64) (0x008#12)))))
    (0x13#8) (0x36#8) (0x86#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00863613 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bd8 σ (0x80006bd8#64) v12 hx12)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

end Vsa.Sim
