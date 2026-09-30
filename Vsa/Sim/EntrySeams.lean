import Vsa.Sim.EntryHalts
import Vsa.Sim.EntryHaltsSpans
import Vsa.Sim.LayoutInstance

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps Halted Halts output)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc
open Vsa.Refine (Layout Loaded)
open Vsa.While (initSt Program Status ExecSeq Addr)
open Vsa.Sim.Code (Interp_runLoaded)

set_option maxHeartbeats 800000
set_option maxRecDepth 1000000

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

end Vsa.Sim
