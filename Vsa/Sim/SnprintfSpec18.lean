import Vsa.Sim.SnprintfSpec5
import Vsa.Sim.DecodeTable.Batch07Part26
import Vsa.Sim.DecodeTable.Batch07Part05
import Vsa.Sim.DecodeTable.Batch06Part32
import Vsa.Sim.DecodeTable.Batch06Part15
import Vsa.Sim.DecodeTable.Batch09Part23
import Vsa.Sim.DecodeTable.Batch16Part14
import Vsa.Sim.DecodeTable.Batch01Part11
import Vsa.Sim.DecodeTable.Batch02Part02
import Vsa.Sim.DecodeTable.Batch02Part05
import Vsa.Sim.DecodeTable.Batch02Part17
import Vsa.Sim.DecodeTable.Batch02Part21
import Vsa.Sim.DecodeTable.Batch02Part28
import Vsa.Sim.DecodeTable.Batch03Part17
import Vsa.Sim.DecodeTable.Batch04Part07
import Vsa.Sim.DecodeTable.Batch05Part07
import Vsa.Sim.DecodeTable.Batch05Part10
import Vsa.Sim.DecodeTable.Batch05Part11
import Vsa.Sim.DecodeTable.Batch05Part22
import Vsa.Sim.DecodeTable.Batch05Part31
import Vsa.Sim.DecodeTable.Batch06Part10
import Vsa.Sim.DecodeTable.Batch06Part18
import Vsa.Sim.DecodeTable.Batch07Part08
import Vsa.Sim.DecodeTable.Batch07Part18
import Vsa.Sim.DecodeTable.Batch08Part21
import Vsa.Sim.DecodeTable.Batch08Part22
import Vsa.Sim.DecodeTable.Batch08Part24
import Vsa.Sim.DecodeTable.Batch08Part27
import Vsa.Sim.DecodeTable.Batch08Part31
import Vsa.Sim.DecodeTable.Batch09Part22
import Vsa.Sim.DecodeTable.Batch09Part24
import Vsa.Sim.DecodeTable.Batch09Part25
import Vsa.Sim.DecodeTable.Batch09Part26
import Vsa.Sim.DecodeTable.Batch10Part29
import Vsa.Sim.DecodeTable.Batch10Part30
import Vsa.Sim.DecodeTable.Batch11Part04
import Vsa.Sim.DecodeTable.Batch11Part27
import Vsa.Sim.DecodeTable.Batch11Part29
import Vsa.Sim.DecodeTable.Batch11Part31
import Vsa.Sim.DecodeTable.Batch12Part03
import Vsa.Sim.DecodeTable.Batch12Part07
import Vsa.Sim.DecodeTable.Batch12Part08
import Vsa.Sim.DecodeTable.Batch12Part16
import Vsa.Sim.DecodeTable.Batch12Part18
import Vsa.Sim.DecodeTable.Batch12Part21
import Vsa.Sim.DecodeTable.Batch13Part02
import Vsa.Sim.DecodeTable.Batch13Part04
import Vsa.Sim.DecodeTable.Batch14Part05
import Vsa.Sim.DecodeTable.Batch14Part31
import Vsa.Sim.DecodeTable.Batch15Part21
import Vsa.Sim.DecodeTable.Batch15Part22
import Vsa.Sim.DecodeTable.Batch16Part17
import Vsa.Sim.DecodeTable.Batch16Part20
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
