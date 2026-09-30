import Vsa.Sim.DecodeTable.Batch06Part19
import Vsa.Sim.DecodeTable.Batch06Part08
import Vsa.Sim.DecodeTable.Batch03Part24
import Vsa.Sim.DecodeTable.Batch02Part17
import Vsa.Sim.DecodeTable.Batch01Part31
import Vsa.Sim.DecodeTable.Batch02Part05
import Vsa.Sim.DecodeTable.Batch02Part12
import Vsa.Sim.DecodeTable.Batch02Part21
import Vsa.Sim.DecodeTable.Batch02Part28
import Vsa.Sim.DecodeTable.Batch02Part31
import Vsa.Sim.DecodeTable.Batch03Part17
import Vsa.Sim.DecodeTable.Batch04Part07
import Vsa.Sim.DecodeTable.Batch05Part07
import Vsa.Sim.DecodeTable.Batch05Part10
import Vsa.Sim.DecodeTable.Batch05Part31
import Vsa.Sim.DecodeTable.Batch06Part14
import Vsa.Sim.DecodeTable.Batch06Part18
import Vsa.Sim.DecodeTable.Batch07Part08
import Vsa.Sim.DecodeTable.Batch07Part18
import Vsa.Sim.DecodeTable.Batch08Part03
import Vsa.Sim.DecodeTable.Batch08Part09
import Vsa.Sim.DecodeTable.Batch08Part21
import Vsa.Sim.DecodeTable.Batch08Part22
import Vsa.Sim.DecodeTable.Batch08Part24
import Vsa.Sim.DecodeTable.Batch08Part31
import Vsa.Sim.DecodeTable.Batch09Part07
import Vsa.Sim.DecodeTable.Batch09Part24
import Vsa.Sim.DecodeTable.Batch09Part25
import Vsa.Sim.DecodeTable.Batch09Part26
import Vsa.Sim.DecodeTable.Batch10Part30
import Vsa.Sim.DecodeTable.Batch11Part27
import Vsa.Sim.DecodeTable.Batch11Part31
import Vsa.Sim.DecodeTable.Batch12Part07
import Vsa.Sim.DecodeTable.Batch12Part21
import Vsa.Sim.DecodeTable.Batch13Part02
import Vsa.Sim.DecodeTable.Batch13Part04
import Vsa.Sim.DecodeTable.Batch13Part21
import Vsa.Sim.DecodeTable.Batch14Part05
import Vsa.Sim.DecodeTable.Batch14Part31
import Vsa.Sim.DecodeTable.Batch15Part21
import Vsa.Sim.DecodeTable.Batch15Part22
import Vsa.Sim.DecodeTable.Batch16Part17
import Vsa.Sim.DecodeTable.Batch16Part20
import Vsa.Sim.EnvDefSpec2
import Vsa.Sim.SnprintfSpec5
import Vsa.Sim.StrcmpSpecCond
import Vsa.Sim.ValueEqualSpec2

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (__hidden___udivdi3Loaded)

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

abbrev llArg (a0 a1 a2 a3 a4 a5 a6 a7 : BitVec 8) : BitVec 64 :=
  sign_extend (m := 64)
    ((((((((a7.append a6).append a5).append a4).append a3).append a2).append a1).append a0)
      : BitVec (8 * 8))

end Vsa.Sim
