import Vsa.Sim.DivLoops
import Vsa.Sim.Code.«__umoddi3»
import Vsa.Sim.Code.«__divdi3»
import Vsa.Sim.Code.«__moddi3»
import Vsa.Sim.DecodeNF

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

end Vsa.Sim
