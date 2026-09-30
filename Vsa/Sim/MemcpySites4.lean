import Vsa.Sim.DecodeNF
import Vsa.Sim.MemcpySites2

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code (MemcpyLoaded)

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
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.TextIn.pin4L hmem 0x80006bd8 0x80006bd9 0x80006bda 0x80006bdb (b0 := (0x13 : BitVec 8)) (b1 := (0x36 : BitVec 8)) (b2 := (0x86 : BitVec 8)) (b3 := (0x00 : BitVec 8)) (by decide)
  exact stepObs_alu σ i u (0x80006bd8#64) vminstret (0x00863613#32)
    (instruction.ITYPE (0x008#12, regidx.Regidx 0x0c#5, regidx.Regidx 0x0c#5, iop.SLTIU))
    Register.x12 (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v12 (sign_extend (m := 64) (0x008#12)))))
    (0x13#8) (0x36#8) (0x86#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.decodeW (w := 0x00863613#32) (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bd8 σ (0x80006bd8#64) v12 hx12)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

end Vsa.Sim
