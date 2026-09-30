import Vsa.Sim.CmpTailSitesGen
import Vsa.Sim.DecodeTable.Batch01Part10
import Vsa.Sim.DecodeTable.Batch06Part25
import Vsa.Sim.DecodeTable.Batch06Part13
import Vsa.Sim.DecodeTable.Batch05Part26
import Vsa.Sim.DecodeTable.Batch05Part24
import Vsa.Sim.DecodeTable.Batch16Part27
import Vsa.Sim.DecodeTable.Batch07Part22
import Vsa.Sim.DecodeTable.Batch04Part02
import Vsa.Sim.DecodeTable.Batch02Part23

/-!
Hand-written `StepObs` sites for the shared inline comparison arm @0x80003628
that `scripts/gen_sites.py` cannot emit (auipc / slli / srli / slt / not(xori) /
sgtz(slt x0) / slti).  The gen-able sites live in `CmpTailSitesGen`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

