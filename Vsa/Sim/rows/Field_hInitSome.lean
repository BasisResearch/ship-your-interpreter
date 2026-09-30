import Vsa.Sim.rows.ScaffoldRows
import Vsa.Sim.rows.StmtForLoopSegPreB

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim.ScaffoldRows

local notation "SpecSt" => Vsa.While.St

end Vsa.Sim.ScaffoldRows
