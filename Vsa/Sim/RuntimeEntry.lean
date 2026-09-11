import Vsa.Sim.RuntimeOwnershipData
import Vsa.Sim.InterpEntry

open LeanRV64DExecutable Vsa
open Vsa.Machine (Config)
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

namespace Vsa.Sim
open RuntimeOwnership

/-- Recursive evaluator entry with the owned runtime and exact AST read support. -/
structure EvalRuntimeEntry
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (phiF phiC : Vsa.While.Addr → Nat) (alloc : Allocations)
    (exts : List Extent) (shared : Nat → Prop) (st : Vsa.While.St)
    (d env : Nat) (e : Vsa.While.Expr) (sp ret dst aEnv aExpr : BitVec 64)
    (m0 : Mem) (c : Config) : Prop where
  entry : EvalEntry g N A SL phiF phiC st d env e sp ret dst aEnv aExpr m0 c
  runtime : StoreRuntimeData N A SL phiF phiC alloc exts shared st.store c.σ.mem
  ast : ExprReprWithin c.σ.mem shared aExpr.toNat e

end Vsa.Sim
