import Vsa.Sim.RamReadPins
import Vsa.Sim.StepObs
import Vsa.Sim.ExecuteAlu
import Vsa.Sim.ExecuteBranch
import Vsa.Sim.ExecuteLoad
import Vsa.Sim.ExecuteStore
import Vsa.Sim.MemStore
import Vsa.Sim.RegAccess
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part10
import Vsa.Sim.DecodeTable.Batch01Part14
import Vsa.Sim.DecodeTable.Batch01Part15
import Vsa.Sim.DecodeTable.Batch01Part20
import Vsa.Sim.DecodeTable.Batch01Part21
import Vsa.Sim.DecodeTable.Batch01Part22
import Vsa.Sim.DecodeTable.Batch01Part23
import Vsa.Sim.DecodeTable.Batch01Part29
import Vsa.Sim.DecodeTable.Batch01Part32
import Vsa.Sim.DecodeTable.Batch03Part03
import Vsa.Sim.DecodeTable.Batch03Part22
import Vsa.Sim.DecodeTable.Batch03Part30
import Vsa.Sim.DecodeTable.Batch04Part24
import Vsa.Sim.DecodeTable.Batch10Part12
import Vsa.Sim.DecodeTable.Batch12Part01
import Vsa.Sim.DecodeTable.Batch12Part02
import Vsa.Sim.DecodeTable.Batch12Part03
import Vsa.Sim.DecodeTable.Batch14Part09
import Vsa.Sim.DecodeTable.Batch14Part13
import Vsa.Sim.DecodeTable.Batch15Part01
import Vsa.Sim.DecodeTable.Batch16Part08
import Vsa.Sim.ValueSites
import Vsa.Sim.Code.Eval_expr

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem exec_slli_a5_ee (σ : MState) (pc : BitVec 64) (v15 : BitVec 64)
    (hx15 : σ.regs.get? Register.x15 = some v15) :
    (execute (instruction.SHIFTIOP (0x02#6, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, sop.SLLI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x15 (shift_bits_left v15 (Sail.BitVec.extractLsb (0x02#6) 5 0))) := by
  have h₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  exact execute_shiftiop_slli_char (0x02#6) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5) v15
    (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x15 (shift_bits_left v15 (Sail.BitVec.extractLsb (0x02#6) 5 0)))
    (rX_bits_x15 _ v15 h₂)
    (wX_bits_x15 _ (shift_bits_left v15 (Sail.BitVec.extractLsb (0x02#6) 5 0)))

end Vsa.Sim
