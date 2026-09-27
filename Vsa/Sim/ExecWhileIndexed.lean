import Vsa.Sim.ExecWhile2
import Vsa.Sim.InterpEntry
import Vsa.Sim.TermSimAssembly
import Vsa.Sim.TripleCat
import Vsa.Sim.RecursiveStepGeom

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
