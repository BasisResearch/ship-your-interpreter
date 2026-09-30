import Vsa.Sim.DivFamily
import Vsa.Sim.EntryHalts

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps StepsN)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc
open Vsa.Refine (Layout Loaded)
open Vsa.While (initSt Program Status ExecSeq ExecS SApprox Stmt Addr)

namespace Vsa.Sim.DivCorrClose

local notation "SpecSt" => Vsa.While.St

variable (Reflect : Config → Addr → List Stmt → Prop)

end Vsa.Sim.DivCorrClose
