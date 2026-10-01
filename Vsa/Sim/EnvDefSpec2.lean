import Vsa.Sim.DecodeNF
import Vsa.Sim.StrcmpSpecW3

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc
open Vsa.While (Frame Store)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

def reallocEntry : Nat := 0x8000527c

end Vsa.Sim
