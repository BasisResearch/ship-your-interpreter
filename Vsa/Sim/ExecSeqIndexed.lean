import Vsa.While.Cost
import Vsa.Sim.DecodeNF
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
