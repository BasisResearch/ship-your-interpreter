import Vsa.Sim.RuntimeResult
import Vsa.Sim.ExecRuntimeEntry
import Vsa.Sim.EvalReturn
import Vsa.Sim.ExecBlock

open LeanRV64DExecutable Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While Vsa.Machine Vsa.Logic

namespace Vsa.Sim
open RuntimeOwnership

/-- Owned evaluator return at one selected map pair and allocation state. -/
abbrev EvalRuntimeReturn
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (phiF phiC : Addr → Nat)
    (nf nc : Nat) (shared : Nat → Prop) (st : Vsa.While.St) (v : Value)
    (sp ret dst : BitVec 64) (m0 : Mem) (c : Config) : Prop :=
  EvalReturn g N A SL phiF phiC nf nc st v sp ret dst m0
    (RuntimeResult N A SL shared st.store [(dst.toNat, v)] m0) c

/-- Recursive evaluator contract consuming ownership at the actual entry. -/
structure EvalRuntimeIH (st : Vsa.While.St) (d env : Nat) (e : Expr)
    (st' : Vsa.While.St) (v : Value) : Prop where
  run : ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (phiF phiC : Addr → Nat)
    (alloc : Allocations) (exts : List Extent) (shared : Nat → Prop)
    (sp ret dst aEnv aExpr : BitVec 64) (m0 : Mem),
    Triple (EvalRuntimeEntry g N A SL phiF phiC alloc exts shared st d env e
      sp ret dst aEnv aExpr m0)
      (EvalRuntimeReturn g N A SL phiF phiC st.store.frames.size st.store.closures.size
        shared st' v sp ret dst m0)

/-- Only a return status exposes a represented statement result. -/
def statusResults (a : Nat) : Status → List (Nat × Value)
  | .ret v => [(a, v)]
  | _ => []

/-- Statement results and the runtime use one selected representation pair. -/
structure ExecRuntimeReturn
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (phiF phiC : Addr → Nat)
    (nf nc : Nat) (shared : Nat → Prop) (st : Vsa.While.St) (status : Status)
    (sp ret aRet : BitVec 64) (m0 : Mem) (c : Config) : Prop where
  exit : ExecExitD g N A SL phiF phiC nf nc st status sp ret aRet m0 c
  selected : ∃ resultF resultC,
    ReturnRepr N A phiF phiC resultF resultC nf nc st.store (statusResults aRet.toNat status)
      (RuntimeResult N A SL shared st.store (statusResults aRet.toNat status) m0)
      (fun k => SL.lo ≤ k ∧ k < SL.hi) c.σ.mem

/-- Recursive statement contract retaining ownership for subsequent calls. -/
structure ExecRuntimeIH (st : Vsa.While.St) (d env : Nat) (s : Stmt)
    (st' : Vsa.While.St) (status : Status) : Prop where
  run : ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (phiF phiC : Addr → Nat)
    (alloc : Allocations) (exts : List Extent) (shared : Nat → Prop)
    (sp ret aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem),
    Triple (ExecRuntimeEntry g N A SL phiF phiC alloc exts shared st d env s
      sp ret aInterp aStmt aEnv aRet m0)
      (ExecRuntimeReturn g N A SL phiF phiC st.store.frames.size st.store.closures.size
        shared st' status sp ret aRet m0)

end Vsa.Sim
