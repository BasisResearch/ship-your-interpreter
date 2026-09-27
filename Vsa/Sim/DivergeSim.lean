import Vsa.Sim.ErrorSimFull

open Vsa.Machine
open Vsa.While

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

variable (Corr : Config → SpecSt → Nat → Addr → List Stmt → Prop)

end Vsa.Sim
