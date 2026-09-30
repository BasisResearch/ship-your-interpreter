import Vsa.While.ErrorSem
import Vsa.While.Trichotomy
import Vsa.Sim.ErrorSimFull
import Vsa.Triple

open Vsa.Machine
open Vsa.While

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

variable (Corr : Config → SpecSt → Nat → Addr → List Stmt → Prop)

end Vsa.Sim
