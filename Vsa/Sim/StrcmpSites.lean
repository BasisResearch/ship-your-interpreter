import Vsa.Sim.StepObs
import Vsa.Sim.ExecuteAlu
import Vsa.Sim.ExecuteBranch
import Vsa.Sim.ExecuteLoad
import Vsa.Sim.MemLoadTotal
import Vsa.Sim.RegAccess
import Vsa.Sim.DecodeNF
import Vsa.Sim.StrlenMagic
import Vsa.Sim.Code.Strcmp

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code (StrcmpLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

end Vsa.Sim
