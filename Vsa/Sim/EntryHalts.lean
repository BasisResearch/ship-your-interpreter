import Vsa.Sim.TermEntry
import Vsa.Sim.TermSimAssembly
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

set_option maxHeartbeats 400000
set_option maxRecDepth 1000000

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

def interpLoopHeadPC : Nat := 0x8000448c

def interpNormalExitPC : Nat := 0x80004514

end Vsa.Sim
