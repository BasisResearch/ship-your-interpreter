import Vsa.Sim.Skeleton
import Vsa.Sim.Retire
import Vsa.Sim.StepAddi
import Vsa.Sim.ExecuteAlu
import Vsa.Sim.Frame

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

abbrev sigma3_alu (σ : MState) (pc : BitVec 64) (rd_reg : Register)
    (v : RegisterType rd_reg) : MState :=
  {(afterNextPC (afterPrelude σ) pc) with
    regs := (afterNextPC (afterPrelude σ) pc).regs.insert rd_reg v}

abbrev sigmaPost_alu (σ : MState) (pc vminstret : BitVec 64) (rd_reg : Register)
    (v : RegisterType rd_reg) : MState :=
  {(({(sigma3_alu σ pc rd_reg v) with regs := (sigma3_alu σ pc rd_reg v).regs.insert Register.PC (BitVec.addInt pc 4)}) : MState) with
    regs := (({(sigma3_alu σ pc rd_reg v) with regs := (sigma3_alu σ pc rd_reg v).regs.insert Register.PC (BitVec.addInt pc 4)}) : MState).regs.insert Register.minstret (BitVec.addInt vminstret 1)}

theorem get?_sigmaPost_alu (σ : MState) (pc vminstret : BitVec 64) (rd_reg : Register)
    (v : RegisterType rd_reg) (R : Register)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h3 : (rd_reg == R) = false) (h4 : (Register.nextPC == R) = false)
    (h5 : (Register.minstret_increment == R) = false) :
    (sigmaPost_alu σ pc vminstret rd_reg v).regs.get? R = σ.regs.get? R := by
  reg_reads [h1, h2, h3, h4, h5]

end Vsa.Sim
