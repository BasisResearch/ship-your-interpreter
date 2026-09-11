import Vsa.Sim.RuntimeEntry
import Vsa.Sim.ExecEntry

open LeanRV64DExecutable Vsa
open Vsa.Machine (Config)
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

namespace Vsa.Sim
open RuntimeOwnership

/-- Statement entry retaining the owned runtime and exact AST read support. -/
structure ExecRuntimeEntry
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (phiF phiC : Vsa.While.Addr → Nat) (alloc : Allocations)
    (exts : List Extent) (shared : Nat → Prop) (st : Vsa.While.St)
    (d env : Nat) (s : Vsa.While.Stmt)
    (sp ret aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) (c : Config) : Prop where
  entry : ExecEntry g N A SL phiF phiC st d env s sp ret aInterp aStmt aEnv aRet m0 c
  runtime : StoreRuntimeData N A SL phiF phiC alloc exts shared st.store c.σ.mem
  ast : StmtReprWithin c.σ.mem shared aStmt.toNat s

end Vsa.Sim
