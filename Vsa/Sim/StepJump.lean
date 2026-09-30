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

end Vsa.Sim
