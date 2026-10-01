import Vsa.Sim.SnprintfSpec5
import Vsa.Sim.DecodeNF
import Vsa.Sim.EnvDefSpec2
import Vsa.Sim.StrcmpSpecCond
import Vsa.Sim.ValueEqualSpec2

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

abbrev NotWrittenMv (R : Register) : Prop :=
  (Register.x11 == R) = false ∧ (Register.x13 == R) = false ∧
  (Register.x14 == R) = false ∧ (Register.x15 == R) = false ∧
  (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
  (Register.minstret == R) = false ∧ (Register.minstret_increment == R) = false ∧
  (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
  (Register.mip == R) = false

end Vsa.Sim
