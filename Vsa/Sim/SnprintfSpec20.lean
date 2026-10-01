import Vsa.Sim.SnprintfSpec19
import Vsa.Sim.DecodeNF
import Vsa.Sim.RamReadPins

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

abbrev NotWrittenSr (R : Register) : Prop :=
  (Register.x18 == R) = false ∧ (Register.x19 == R) = false ∧
  (Register.x20 == R) = false ∧ (Register.x21 == R) = false ∧
  NotWrittenSp R

theorem NotWrittenSr.sp {R : Register} (h : NotWrittenSr R) : NotWrittenSp R := h.2.2.2.2

end Vsa.Sim
