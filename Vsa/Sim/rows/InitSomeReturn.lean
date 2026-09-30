import Vsa.Sim.rows.Field_hInitSome
import Vsa.Sim.ExecWhileIndexed

/-!
# Present-initializer return seam

The child `exec_stmt` returns to `0x80004258`.  This file discharges the real
`j 0x8000426c` instruction which routes any initializer result to the
for-loop head.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim.ScaffoldRows

local notation "SpecSt" => Vsa.While.St

end Vsa.Sim.ScaffoldRows

