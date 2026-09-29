import Vsa.Sim.DecodeNF
import Vsa.Sim.EnvDefSpec2
import Vsa.Sim.SnprintfSpec5
import Vsa.Sim.StrcmpSpecCond
import Vsa.Sim.ValueEqualSpec2

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

abbrev llArg (a0 a1 a2 a3 a4 a5 a6 a7 : BitVec 8) : BitVec 64 :=
  sign_extend (m := 64)
    ((((((((a7.append a6).append a5).append a4).append a3).append a2).append a1).append a0)
      : BitVec (8 * 8))

end Vsa.Sim
