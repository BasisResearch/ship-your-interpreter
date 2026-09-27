import Vsa.Sim.InterpRunLoopSeamsClose
import Vsa.Sim.StepCount
import Vsa.Sim.rows.LoopHeadDispatch
import Vsa.Sim.IterSeamAssembly

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps StepsN)
open Vsa.Logic (TripleN)
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc
open Vsa.Refine (Layout)
open Vsa.While (St Stmt Expr BinOp UnOp Value ClosureData Store Status Addr EvalE EvalArgs ForCond ExecInit ExecStep ExecS)

namespace Vsa.Sim.ApproxSeamFold

local notation "SpecSt" => Vsa.While.St

variable
  (EEntry : Config → SpecSt → Nat → Addr → Expr → Prop)
  (AEntry : Config → SpecSt → Nat → Addr → List Expr → Prop)
  (CEntry : Config → SpecSt → Nat → Value → List Value → Prop)
  (SEntry : Config → SpecSt → Nat → Addr → Stmt → Prop)
  (FEntry : Config → SpecSt → Nat → Addr → Option Expr → Option Expr → Stmt → Prop)

variable
  (SqEntry : Config → SpecSt → Nat → Addr → List Stmt → Prop)

end Vsa.Sim.ApproxSeamFold
