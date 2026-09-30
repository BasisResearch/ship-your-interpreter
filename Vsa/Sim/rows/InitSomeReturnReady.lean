import Vsa.Sim.rows.InitSomeReturn
import Vsa.While.StoreBodiesBoundPreservation

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (Config Steps)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim.ScaffoldRows

local notation "SpecSt" => Vsa.While.St

end Vsa.Sim.ScaffoldRows
