import Vsa.Sim.ValueSites
import Vsa.Sim.DivSites
import Vsa.Sim.Code.Longjmp
import Vsa.Sim.DecodeNF

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem w_0015b513_jmp : ((((0x00#8).append (0x15#8)).append (0xb5#8)).append (0x13#8)) = (0x0015b513#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_0015b513_jmp : Sail.BitVec.extractLsb ((((0x00#8).append (0x15#8)).append (0xb5#8)).append (0x13#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem exec_seqz_jmp (σ : MState) (pc : BitVec 64) (v11 : BitVec 64)
    (hx11 : σ.regs.get? Register.x11 = some v11) :
    (execute (instruction.ITYPE (0x001#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0a#5, iop.SLTIU))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x10
            (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v11 (sign_extend (m := 64) (0x001#12)))))) := by
  have hx11₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx11
  exact execute_itype_sltiu_char (0x001#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0a#5) v11
    (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x10
      (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v11 (sign_extend (m := 64) (0x001#12))))))
    (rX_bits_x11 _ v11 hx11₂)
    (wX_bits_x10 _ (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v11 (sign_extend (m := 64) (0x001#12))))))

theorem site_80007074_jmp
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : LongjmpLoaded σ.mem)
    (hpcv : pc = (0x80007074#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10
          (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v11 (sign_extend (m := 64) (0x001#12)))))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.TextIn.pin4L hmem 0x80007074 0x80007075 0x80007076 0x80007077 (b0 := (0x13 : BitVec 8)) (b1 := (0xb5 : BitVec 8)) (b2 := (0x15 : BitVec 8)) (b3 := (0x00 : BitVec 8)) (by decide)
  exact stepObs_alu σ i u (0x80007074#64) vminstret (0x0015b513#32)
    (instruction.ITYPE (0x001#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0a#5, iop.SLTIU))
    Register.x10 (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v11 (sign_extend (m := 64) (0x001#12)))))
    (0x13#8) (0xb5#8) (0x15#8) (0x00#8)
    hG hpc hminstret w_0015b513_jmp nr_0015b513_jmp
    (Vsa.Sim.decodeW (w := 0x0015b513#32) (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_seqz_jmp σ (0x80007074#64) v11 hx11)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

end Vsa.Sim
