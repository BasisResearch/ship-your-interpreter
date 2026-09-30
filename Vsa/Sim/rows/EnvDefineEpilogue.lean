import Vsa.Sim.rows.EnvDefineEpilogueCore
import Vsa.Sim.EnvDefMarshal

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (Config)
open Vsa.Logic (Triple)

namespace Vsa.Sim

set_option maxHeartbeats 1000000
attribute [local simp] mkLine decodeM

end Vsa.Sim
