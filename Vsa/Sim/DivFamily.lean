import Vsa.Sim.DivergeSim
import Vsa.Sim.InterpSimBundle

namespace Vsa.Sim.DivFamily

open Vsa.While
open Vsa.Machine (Config Halts Diverges)
open Vsa.Refine (Layout Loaded)
open Vsa.Sim

local notation "SpecSt" => Vsa.While.St

end Vsa.Sim.DivFamily
