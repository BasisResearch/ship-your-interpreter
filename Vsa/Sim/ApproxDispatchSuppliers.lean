import Vsa.Sim.ApproxSeamFold

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps StepsN)
open Vsa.Logic (TripleN)
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc
open Vsa.Refine (Layout)
open Vsa.While (St Stmt Expr BinOp UnOp Value ClosureData Store Status Addr EvalE EvalArgs ForCond ExecInit ExecStep ExecS)

namespace Vsa.Sim.ApproxDispatchSuppliers

local notation "SpecSt" => Vsa.While.St

end Vsa.Sim.ApproxDispatchSuppliers
