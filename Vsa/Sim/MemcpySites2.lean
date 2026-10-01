import Vsa.Sim.MemcpySites

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code (MemcpyLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

abbrev ldData8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : BitVec (8 * 8) :=
  ((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0

end Vsa.Sim
