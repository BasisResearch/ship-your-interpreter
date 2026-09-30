import Vsa.Sim.StepObs
import Vsa.Sim.ExecuteAlu
import Vsa.Sim.ExecuteBranch
import Vsa.Sim.ExecuteLoad
import Vsa.Sim.MemLoadTotal
import Vsa.Sim.RegAccess
import Vsa.Sim.DecodeTable.Batch01Part01
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part09
import Vsa.Sim.DecodeTable.Batch01Part18
import Vsa.Sim.DecodeTable.Batch01Part20
import Vsa.Sim.DecodeTable.Batch01Part21
import Vsa.Sim.DecodeTable.Batch02Part22
import Vsa.Sim.DecodeTable.Batch02Part23
import Vsa.Sim.DecodeTable.Batch03Part13
import Vsa.Sim.DecodeTable.Batch03Part16
import Vsa.Sim.DecodeTable.Batch03Part20
import Vsa.Sim.DecodeTable.Batch03Part21
import Vsa.Sim.DecodeTable.Batch04Part03
import Vsa.Sim.DecodeTable.Batch04Part16
import Vsa.Sim.DecodeTable.Batch04Part30
import Vsa.Sim.DecodeTable.Batch05Part01
import Vsa.Sim.DecodeTable.Batch05Part03
import Vsa.Sim.DecodeTable.Batch05Part14
import Vsa.Sim.DecodeTable.Batch05Part15
import Vsa.Sim.DecodeTable.Batch05Part16
import Vsa.Sim.DecodeTable.Batch05Part17
import Vsa.Sim.DecodeTable.Batch06Part04
import Vsa.Sim.DecodeTable.Batch06Part21
import Vsa.Sim.DecodeTable.Batch06Part22
import Vsa.Sim.DecodeTable.Batch06Part23
import Vsa.Sim.DecodeTable.Batch07Part03
import Vsa.Sim.DecodeTable.Batch07Part06
import Vsa.Sim.DecodeTable.Batch07Part10
import Vsa.Sim.DecodeTable.Batch07Part11
import Vsa.Sim.DecodeTable.Batch08Part02
import Vsa.Sim.DecodeTable.Batch09Part10
import Vsa.Sim.DecodeTable.Batch09Part17
import Vsa.Sim.DecodeTable.Batch09Part18
import Vsa.Sim.DecodeTable.Batch09Part28
import Vsa.Sim.DecodeTable.Batch09Part29
import Vsa.Sim.DecodeTable.Batch11Part22
import Vsa.Sim.DecodeTable.Batch11Part25
import Vsa.Sim.DecodeTable.Batch15Part02
import Vsa.Sim.DecodeTable.Batch15Part27
import Vsa.Sim.DecodeTable.Batch16Part05
import Vsa.Sim.DecodeTable.Batch16Part09
import Vsa.Sim.DecodeTable.Batch16Part25
import Vsa.Sim.StrlenMagic
import Vsa.Sim.Code.Strcmp

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code (StrcmpLoaded)
open Vsa.Sim.DecodeTable

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

end Vsa.Sim
