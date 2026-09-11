import Vsa.Sim.AllocatorResult
import Vsa.Sim.AllocatorEntry
import Vsa.Sim.RuntimeIH

open LeanRV64DExecutable Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While Vsa.Machine Vsa.Logic

namespace Vsa.Sim
open RuntimeOwnership

/-- The evaluator returns allocator ownership and the actual global pointer together. -/
structure EvalAllocatorReturn
    (g : (R : Register) → Option (RegisterType R)) (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (phiF phiC : Addr → Nat)
    (nf nc : Nat) (shared : Nat → Prop) (credits : Nat)
    (st : Vsa.While.St) (v : Value) (sp ret dst : BitVec 64)
    (m0 : Mem) (c : Config) : Prop where
  returned : EvalReturn g N A SL phiF phiC nf nc st v sp ret dst m0
    (AllocatorResult M N shared credits st.store [(dst.toNat, v)] m0) c
  gp : c.σ.regs.get? Register.x3 = some gpv

/-- A supplier establishes sufficient entry credit under a request ceiling.
The run-global allocator ledger supplies its operation contracts. Each recursive
case must derive sufficient resource parameters and preserve the caller's reserve. -/
structure EvalAllocatorIH (st : Vsa.While.St) (d env : Nat) (e : Expr)
    (st' : Vsa.While.St) (v : Value) (cost maxRequest : Nat) : Prop where
  run : ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (gpv : BitVec 64)
    (headroom maxReq : Nat) (M : MallocContract A SL gpv headroom maxReq)
    (_L : AllocLedger A SL gpv headroom maxReq M), maxRequest ≤ maxReq →
    ∀ (phiF phiC : Addr → Nat) (alloc : Allocations) (exts : List Extent)
    (shared : Nat → Prop) (reserve : Nat)
    (sp ret dst aEnv aExpr : BitVec 64) (m0 : Mem),
    Triple (EvalAllocatorEntry g N M phiF phiC alloc exts shared (cost + reserve)
      st d env e sp ret dst aEnv aExpr m0)
      (EvalAllocatorReturn g N M phiF phiC st.store.frames.size st.store.closures.size
        shared reserve st' v sp ret dst m0)

/-- Statement status, allocator ownership, and global pointer at the same return. -/
structure ExecAllocatorReturn
    (g : (R : Register) → Option (RegisterType R)) (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (phiF phiC : Addr → Nat)
    (nf nc : Nat) (shared : Nat → Prop) (credits : Nat)
    (st : Vsa.While.St) (status : Status) (sp ret aRet : BitVec 64)
    (m0 : Mem) (c : Config) : Prop where
  exit : ExecExitD g N A SL phiF phiC nf nc st status sp ret aRet m0 c
  selected : ∃ resultF resultC,
    ReturnRepr N A phiF phiC resultF resultC nf nc st.store (statusResults aRet.toNat status)
      (AllocatorResult M N shared credits st.store (statusResults aRet.toNat status) m0)
      (fun k => SL.lo ≤ k ∧ k < SL.hi) c.σ.mem
  gp : c.σ.regs.get? Register.x3 = some gpv

/-- Statement suppliers require sufficient entry credit and retain the caller's reserve. -/
structure ExecAllocatorIH (st : Vsa.While.St) (d env : Nat) (s : Stmt)
    (st' : Vsa.While.St) (status : Status) (cost maxRequest : Nat) : Prop where
  run : ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (gpv : BitVec 64)
    (headroom maxReq : Nat) (M : MallocContract A SL gpv headroom maxReq)
    (_L : AllocLedger A SL gpv headroom maxReq M), maxRequest ≤ maxReq →
    ∀ (phiF phiC : Addr → Nat) (alloc : Allocations) (exts : List Extent)
    (shared : Nat → Prop) (reserve : Nat)
    (sp ret aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem),
    Triple (ExecAllocatorEntry g N M phiF phiC alloc exts shared (cost + reserve)
      st d env s sp ret aInterp aStmt aEnv aRet m0)
      (ExecAllocatorReturn g N M phiF phiC st.store.frames.size st.store.closures.size
        shared reserve st' status sp ret aRet m0)

end Vsa.Sim
