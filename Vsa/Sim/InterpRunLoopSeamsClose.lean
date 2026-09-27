import Vsa.Sim.DivLoopProgressClose

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps StepsN)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc
open Vsa.Refine (Layout Loaded)
open Vsa.While (initSt Program Status ExecSeq ExecS Stmt Addr)

namespace Vsa.Sim.InterpRunLoopSeamsClose

local notation "SpecSt" => Vsa.While.St

variable (Reflect : Config → Addr → List Stmt → Prop)

end Vsa.Sim.InterpRunLoopSeamsClose
