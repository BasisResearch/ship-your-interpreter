import Vsa.Sim.Skeleton
import Vsa.Sim.Retire
import Vsa.Sim.ExecuteJump
import Vsa.Sim.Frame

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

abbrev sigma3_jal (σ : MState) (pc : BitVec 64) (imm : BitVec 21)
    (rd_reg : Register) (link : RegisterType rd_reg) : MState :=
  {({(afterNextPC (afterPrelude σ) pc) with
      regs := (afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC
        (pc + sign_extend (m := 64) imm)} : MState) with
    regs := (({(afterNextPC (afterPrelude σ) pc) with
      regs := (afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC
        (pc + sign_extend (m := 64) imm)} : MState)).regs.insert rd_reg link}

theorem try_step_jal
    (σ : MState) (u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (imm : BitVec 21) (rd : regidx) (rd_reg : Register)
    (link : RegisterType rd_reg)
    (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.JAL (imm, rd)) (afterPrelude σ))
    (htgt : (pc + sign_extend (m := 64) imm).toNat % 4 = 0)
    (hrd_npc : (rd_reg == Register.nextPC) = false)
    (hrd_mi : (rd_reg == Register.minstret_increment) = false)
    (hrd_ms : (rd_reg == Register.minstret) = false)
    (hrd_hart : (rd_reg == Register.hart_state) = false)
    (hwr : (wX_bits rd (BitVec.addInt pc 4)).run
        {(afterNextPC (afterPrelude σ) pc) with
          regs := (afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC
            (pc + sign_extend (m := 64) imm)}
        = .ok () (sigma3_jal σ pc imm rd_reg link)) :
    (try_step u true).run σ
      = .ok false
          {(({(sigma3_jal σ pc imm rd_reg link) with regs := (sigma3_jal σ pc imm rd_reg link).regs.insert Register.PC (pc + sign_extend (m := 64) imm)}) : MState) with
            regs := (({(sigma3_jal σ pc imm rd_reg link) with regs := (sigma3_jal σ pc imm rd_reg link).regs.insert Register.PC (pc + sign_extend (m := 64) imm)}) : MState).regs.insert Register.minstret (BitVec.addInt vminstret 1)} := by
  exact try_step_retire (Fetched.of_bytes hG hpc hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec)
    (execute_jal_char imm rd _ pc _ _ _ (by reg_reads []) (by reg_reads [hpc]) (by reg_reads [hG.misa]) htgt hwr)
    ⟨by reg_reads [hrd_hart, hG.hart_state], by reg_reads [hrd_npc], by reg_reads [hrd_mi],
     by reg_reads [hrd_ms, hminstret]⟩

abbrev sigma3_jalr (σ : MState) (pc : BitVec 64) (tgt : BitVec 64)
    (rd_reg : Register) (link : RegisterType rd_reg) : MState :=
  {({(afterNextPC (afterPrelude σ) pc) with
      regs := (afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC tgt} : MState) with
    regs := (({(afterNextPC (afterPrelude σ) pc) with
      regs := (afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC tgt} : MState)).regs.insert rd_reg link}

abbrev sigma3_jump_x0 (σ : MState) (pc : BitVec 64) (tgt : BitVec 64) : MState :=
  {(afterNextPC (afterPrelude σ) pc) with
    regs := (afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC tgt}

abbrev sigmaPost_jal (σ : MState) (pc vminstret : BitVec 64) (imm : BitVec 21)
    (rd_reg : Register) (link : RegisterType rd_reg) : MState :=
  {(({(sigma3_jal σ pc imm rd_reg link) with regs := (sigma3_jal σ pc imm rd_reg link).regs.insert Register.PC (pc + sign_extend (m := 64) imm)}) : MState) with
    regs := (({(sigma3_jal σ pc imm rd_reg link) with regs := (sigma3_jal σ pc imm rd_reg link).regs.insert Register.PC (pc + sign_extend (m := 64) imm)}) : MState).regs.insert Register.minstret (BitVec.addInt vminstret 1)}

abbrev sigmaPost_jalr (σ : MState) (pc vminstret tgt : BitVec 64)
    (rd_reg : Register) (link : RegisterType rd_reg) : MState :=
  {(({(sigma3_jalr σ pc tgt rd_reg link) with regs := (sigma3_jalr σ pc tgt rd_reg link).regs.insert Register.PC tgt}) : MState) with
    regs := (({(sigma3_jalr σ pc tgt rd_reg link) with regs := (sigma3_jalr σ pc tgt rd_reg link).regs.insert Register.PC tgt}) : MState).regs.insert Register.minstret (BitVec.addInt vminstret 1)}

abbrev sigmaPost_jump_x0 (σ : MState) (pc vminstret tgt : BitVec 64) : MState :=
  {(({(sigma3_jump_x0 σ pc tgt) with regs := (sigma3_jump_x0 σ pc tgt).regs.insert Register.PC tgt}) : MState) with
    regs := (({(sigma3_jump_x0 σ pc tgt) with regs := (sigma3_jump_x0 σ pc tgt).regs.insert Register.PC tgt}) : MState).regs.insert Register.minstret (BitVec.addInt vminstret 1)}

theorem get?_sigmaPost_jal (σ : MState) (pc vminstret : BitVec 64) (imm : BitVec 21)
    (rd_reg : Register) (link : RegisterType rd_reg) (R : Register)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h3 : (rd_reg == R) = false) (h4 : (Register.nextPC == R) = false)
    (h5 : (Register.minstret_increment == R) = false) :
    (sigmaPost_jal σ pc vminstret imm rd_reg link).regs.get? R = σ.regs.get? R := by
  reg_reads [h1, h2, h3, h4, h5]

theorem get?_sigmaPost_jalr (σ : MState) (pc vminstret tgt : BitVec 64)
    (rd_reg : Register) (link : RegisterType rd_reg) (R : Register)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h3 : (rd_reg == R) = false) (h4 : (Register.nextPC == R) = false)
    (h5 : (Register.minstret_increment == R) = false) :
    (sigmaPost_jalr σ pc vminstret tgt rd_reg link).regs.get? R = σ.regs.get? R := by
  reg_reads [h1, h2, h3, h4, h5]

theorem get?_sigmaPost_jump_x0 (σ : MState) (pc vminstret tgt : BitVec 64) (R : Register)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h4 : (Register.nextPC == R) = false) (h5 : (Register.minstret_increment == R) = false) :
    (sigmaPost_jump_x0 σ pc vminstret tgt).regs.get? R = σ.regs.get? R := by
  reg_reads [h1, h2, h4, h5]

theorem goodstate_sigmaPost_jal (σ : MState) (pc vminstret : BitVec 64) (imm : BitVec 21)
    (rd_reg : Register) (hrd : NonPinned rd_reg) (link : RegisterType rd_reg)
    (hG : GoodState σ) : GoodState (sigmaPost_jal σ pc vminstret imm rd_reg link) := by
  exact ((((hG.insert_nonpinned (by decide) _).insert_nonpinned (by decide) _).insert_nonpinned
    (by decide) _).insert_nonpinned (r := rd_reg) hrd link).retirePost _ _

end Vsa.Sim
