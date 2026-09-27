import Vsa.While.Cost
import Vsa.Sim.DecodeTable.Batch02Part02
import Vsa.Sim.DecodeTable.Batch02Part03
import Vsa.Sim.DecodeTable.Batch02Part04
import Vsa.Sim.DecodeTable.Batch02Part28
import Vsa.Sim.DecodeTable.Batch03Part07
import Vsa.Sim.DecodeTable.Batch03Part18
import Vsa.Sim.DecodeTable.Batch03Part19
import Vsa.Sim.DecodeTable.Batch04Part19
import Vsa.Sim.DecodeTable.Batch04Part27
import Vsa.Sim.DecodeTable.Batch05Part06
import Vsa.Sim.DecodeTable.Batch05Part11
import Vsa.Sim.DecodeTable.Batch05Part13
import Vsa.Sim.DecodeTable.Batch06Part02
import Vsa.Sim.DecodeTable.Batch06Part17
import Vsa.Sim.DecodeTable.Batch10Part13
import Vsa.Sim.DecodeTable.Batch13Part11
import Vsa.Sim.DecodeTable.Batch15Part06
import Vsa.Sim.DecodeTable.Batch15Part12
import Vsa.Sim.DecodeTable.Batch15Part13
import Vsa.Sim.DecodeTable.Batch15Part18
import Vsa.Sim.DecodeTable.Batch16Part06
import Vsa.Sim.DecodeTable.Batch16Part11
import Vsa.Sim.EvalRecCommon
import Vsa.Sim.ExecBrkCont
import Vsa.Sim.StrcmpSites
import Vsa.Sim.TripleCat

namespace Vsa.Sim

open LeanRV64DExecutable Sail
open Register
open Vsa.Machine (Config)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

local notation "SpecSt" => Vsa.While.St

end Vsa.Sim
