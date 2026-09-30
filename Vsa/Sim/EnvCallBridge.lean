import Vsa.Sim.StoreSeg
import Vsa.Sim.BridgeSeg
import Vsa.Sim.EnvDefBridges3

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic (Triple Ent)
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While (initSt Store Frame Value NativeFn Addr St)

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

set_option maxHeartbeats 800000

end Vsa.Sim
