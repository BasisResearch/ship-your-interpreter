import Vsa.Sim.JmpSpec
import Vsa.Refinement

open LeanRV64DExecutable Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps Halted Halts output)
open Vsa.Logic
open Vsa.While
open Vsa.Sim.Code (LongjmpLoaded)

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

end Vsa.Sim
