import Vsa.Sim.rows.ExecCaseGeom

/-! Import the pinned exec-leaf widener and its entry-derived proofs from
`ExecCaseGeom`. The memory-pin predicates are defined in `ExecBrkCont`. -/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim



end Vsa.Sim

#print axioms Vsa.Sim.execLeafWidenP_of_entry
#print axioms Vsa.Sim.execExitD_of_pinnedExecExit
