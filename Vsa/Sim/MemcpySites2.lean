import Vsa.Sim.StepObs
import Vsa.Sim.ExecuteAlu
import Vsa.Sim.ExecuteBranch
import Vsa.Sim.ExecuteLoad
import Vsa.Sim.ExecuteStore
import Vsa.Sim.MemStore
import Vsa.Sim.RegAccess
import Vsa.Sim.DecodeTable.Batch01Part19
import Vsa.Sim.DecodeTable.Batch01Part25
import Vsa.Sim.DecodeTable.Batch01Part26
import Vsa.Sim.DecodeTable.Batch03Part22
import Vsa.Sim.DecodeTable.Batch03Part24
import Vsa.Sim.DecodeTable.Batch05Part23
import Vsa.Sim.DecodeTable.Batch07Part02
import Vsa.Sim.DecodeTable.Batch16Part13
import Vsa.Sim.DecodeTable.Batch16Part18
import Vsa.Sim.Code.Memcpy
import Vsa.Sim.DivSites
import Vsa.Sim.MemcpySites

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code (MemcpyLoaded memcpy_at_80006bfc memcpy_at_80006c00 memcpy_at_80006c04 memcpy_at_80006c08 memcpy_at_80006c0c memcpy_at_80006c10 memcpy_at_80006c14 memcpy_at_80006c18 memcpy_at_80006c38)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

abbrev ldData8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : BitVec (8 * 8) :=
  ((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0

abbrev sdData8 (vdata : BitVec 64) : BitVec (8 * 8) :=
  Sail.BitVec.extractLsb vdata ((8 *i 8) -i 1) 0

end Vsa.Sim
