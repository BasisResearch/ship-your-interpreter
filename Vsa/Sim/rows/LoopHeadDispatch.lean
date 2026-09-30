import Vsa.Sim.ExecEntry
import Vsa.Sim.InductionScaffold
import Vsa.Sim.BridgeSeg

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc
open Vsa.While (Status Stmt Addr)
open Vsa.Sim.Code (Exec_stmtLoaded)

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

end Vsa.Sim
