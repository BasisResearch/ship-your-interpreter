import Vsa.Sim.TermSimClose
import Vsa.Sim.EvalChildArm

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

end Vsa.Sim

namespace Vsa.Sim.Rows

open Vsa.Sim

local notation "SpecSt" => Vsa.While.St

end Vsa.Sim.Rows
