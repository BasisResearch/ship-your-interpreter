import Vsa.Sim.rows.InitSomeReturn
import Vsa.Sim.EntryGroundKit
import Vsa.Sim.ExecRecCommon
import Vsa.While.StoreBodiesBoundPreservation

/-! # Present-initializer return adapter

Compose an arbitrary-status recursive initializer exit with the concrete
`j 0x8000426c`, selecting the child's coherent extended allocation maps for
the ensuing for-loop boundary.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (Config Steps)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim.ScaffoldRows

local notation "SpecSt" => Vsa.While.St

end Vsa.Sim.ScaffoldRows

