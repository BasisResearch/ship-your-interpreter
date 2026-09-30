import Vsa.Sim.StepObs
import Vsa.Sim.ExecuteAlu
import Vsa.Sim.ExecuteBranch
import Vsa.Sim.ExecuteLoad
import Vsa.Sim.ExecuteStore
import Vsa.Sim.MemStore
import Vsa.Sim.RegAccess
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part16
import Vsa.Sim.DecodeTable.Batch01Part21
import Vsa.Sim.DecodeTable.Batch02Part23
import Vsa.Sim.DecodeTable.Batch02Part26
import Vsa.Sim.DecodeTable.Batch16Part15
import Vsa.Sim.DecodeTable.Batch16Part16
import Vsa.Sim.DecodeTable.Batch16Part19
import Vsa.Sim.Code.Memcpy
import Vsa.Sim.DivSites

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code (MemcpyLoaded memcpy_at_80006c40 memcpy_at_80006c44 memcpy_at_80006c48 memcpy_at_80006c4c memcpy_at_80006c50 memcpy_at_80006c54 memcpy_at_80006c58 memcpy_at_80006c5c)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

abbrev sbData (vdata : BitVec 64) : BitVec (8 * 1) :=
  Sail.BitVec.extractLsb vdata ((1 *i 8) -i 1) 0

end Vsa.Sim
