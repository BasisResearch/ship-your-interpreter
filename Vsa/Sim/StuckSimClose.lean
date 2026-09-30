import Vsa.Sim.DivergeSim
import Vsa.Refinement

namespace Vsa.Sim.StuckSimClose

open Vsa.While
open Vsa.Machine (Config Halts Diverges)
open Vsa.Refine (Layout Loaded InterpSim)
open Vsa.Sim

local notation "SpecSt" => Vsa.While.St

end Vsa.Sim.StuckSimClose
