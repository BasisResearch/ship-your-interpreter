import Vsa.Sim.TermSimAssembly
import Vsa.Refinement

namespace Vsa.Sim.TermSimClose

open Vsa.While
open Vsa.Machine (Config Halts)
open Vsa.Refine (Layout Loaded InterpSim)

local notation "SpecSt" => Vsa.While.St

end Vsa.Sim.TermSimClose
