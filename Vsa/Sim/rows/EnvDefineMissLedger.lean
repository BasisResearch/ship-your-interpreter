import Vsa.Sim.rows.EnvDefineContractUpdate
import Vsa.Sim.rows.EnvNewContractSupply
import Vsa.Sim.AllocRuns
import Vsa.Sim.AllocReserveTransport
import Vsa.Sim.Code.FixedImage_Strlen
import Vsa.Sim.Code.FixedImage_Memcpy

/-!
# `EnvDefineMissLedger` — the external facts of the `env_define` miss lanes

A miss (`x` bound nowhere in the frame at `env`) copies the name and appends
it, growing the frame's arrays through `realloc` when full or on the empty
frame.  The callee contracts the landed specs state (`strlen_spec_framed`,
`MallocContract.spec`, `memcpy_spec_framed_{byte,word}`, `ReallocOps`) carry
neither the console output nor byte presence, which `EnvDefineReturnState`
demands; the four runs below restate each contract with exactly those clauses
(the supplier of each is the landed spec plus the observation that the callee
executes no HTIF store and only inserts bytes).  `EnvDefineMissLedger` collects
the runs with the allocator-footprint discipline and the request bounds, each
field naming its supplier.
-/

