import Vsa.Sim.EnvGetSites
import Vsa.Sim.DecodeNF

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem site_80002c60_eg2
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbase : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hbase : σ.regs.get? Register.x9 = some vbase)
    (hmem : Env_getLoaded σ.mem)
    (hpcv : pc = (0x80002c60#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) (0x000#12)).toNat)
    (hhiram : (vbase + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) (0x000#12)).toNat)
    (halign : (vbase + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0)
    (d0 : σ.mem[(vbase + sign_extend (m := 64) (0x000#12)).toNat]? = some b0)
    (d1 : σ.mem[(vbase + sign_extend (m := 64) (0x000#12)).toNat + 1]? = some b1)
    (d2 : σ.mem[(vbase + sign_extend (m := 64) (0x000#12)).toNat + 2]? = some b2)
    (d3 : σ.mem[(vbase + sign_extend (m := 64) (0x000#12)).toNat + 3]? = some b3)
    (d4 : σ.mem[(vbase + sign_extend (m := 64) (0x000#12)).toNat + 4]? = some b4)
    (d5 : σ.mem[(vbase + sign_extend (m := 64) (0x000#12)).toNat + 5]? = some b5)
    (d6 : σ.mem[(vbase + sign_extend (m := 64) (0x000#12)).toNat + 6]? = some b6)
    (d7 : σ.mem[(vbase + sign_extend (m := 64) (0x000#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10
          (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.TextIn.pin4L hmem 0x80002c60 0x80002c61 0x80002c62 0x80002c63 (b0 := (0x03 : BitVec 8)) (b1 := (0xb5 : BitVec 8)) (b2 := (0x04 : BitVec 8)) (b3 := (0x00 : BitVec 8)) (by decide)
  have hbase₂ : (afterNextPC (afterPrelude σ) (0x80002c60#64)).regs.get? Register.x9 = some vbase := by
    rw [get?_afterNextPC σ (0x80002c60#64) _ (by decide) (by decide)]; exact hbase
  exact stepObs_alu σ i u (0x80002c60#64) vminstret (0x0004b503#32)
    (instruction.LOAD (0x000#12, regidx.Regidx 0x09#5, regidx.Regidx 0x0a#5, false, 8))
    Register.x10 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x03#8) (0xb5#8) (0x04#8) (0x00#8)
    hG hpc hminstret w_0004b503_eg nr_0004b503_eg
    (Vsa.Sim.decodeW (w := 0x0004b503#32) (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80002c60#64) (0x000#12) (regidx.Regidx 0x09#5) (regidx.Regidx 0x0a#5)
      (sigma3_alu σ (0x80002c60#64) Register.x10
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      vbase b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x9 _ vbase hbase₂)
      (wX_bits_x10 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign d0 d1 d2 d3 d4 d5 d6 d7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

end Vsa.Sim
