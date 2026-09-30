import Vsa.Sim.SnprintfSitesRet5
import Vsa.Sim.DecodeTable.Batch02Part01
import Vsa.Sim.DecodeTable.Batch01Part25
import Vsa.Sim.DecodeTable.Batch07Part13
import Vsa.Sim.DecodeTable.Batch07Part25
import Vsa.Sim.DecodeTable.Batch07Part30
import Vsa.Sim.DecodeTable.Batch09Part01
import Vsa.Sim.DecodeTable.Batch13Part22
import Vsa.Sim.DecodeTable.Batch13Part25
import Vsa.Sim.DecodeTable.Batch15Part31
import Vsa.Sim.EvalCallNative
import Vsa.Sim.EvalNotSim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem jalr_native_target (a6 : BitVec 64) (halign : a6.toNat % 4 = 0) :
    BitVec.update (a6 + sign_extend (m := 64) (0x000#12)) 0 0#1 = a6 :=
  ret_tgt a6 halign

end Vsa.Sim
