import Vsa.Sim.RuntimeAllocatorState
import Vsa.Sim.ExecRuntimeEntry

open LeanRV64DExecutable Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While Vsa.Machine

namespace Vsa.Sim
open RuntimeOwnership

/-- Evaluator entry retaining allocator state and the actual global pointer. -/
structure EvalAllocatorEntry
    (g : (R : Register) → Option (RegisterType R)) (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (phiF phiC : Addr → Nat)
    (alloc : Allocations) (exts : List Extent) (shared : Nat → Prop) (credits : Nat)
    (st : Vsa.While.St) (d env : Nat) (e : Expr)
    (sp ret dst aEnv aExpr : BitVec 64) (m0 : Mem) (c : Config) : Prop where
  entry : EvalEntry g N A SL phiF phiC st d env e sp ret dst aEnv aExpr m0 c
  allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared credits st.store c.σ.mem
  ast : ExprReprWithin c.σ.mem shared aExpr.toNat e
  gp : c.σ.regs.get? Register.x3 = some gpv

/-- Statement entry retaining the same allocator state used by its children. -/
structure ExecAllocatorEntry
    (g : (R : Register) → Option (RegisterType R)) (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (phiF phiC : Addr → Nat)
    (alloc : Allocations) (exts : List Extent) (shared : Nat → Prop) (credits : Nat)
    (st : Vsa.While.St) (d env : Nat) (s : Stmt)
    (sp ret aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) (c : Config) : Prop where
  entry : ExecEntry g N A SL phiF phiC st d env s sp ret aInterp aStmt aEnv aRet m0 c
  allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared credits st.store c.σ.mem
  ast : StmtReprWithin c.σ.mem shared aStmt.toNat s
  gp : c.σ.regs.get? Register.x3 = some gpv

variable {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
  {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
  {M : MallocContract A SL gpv headroom maxReq} {phiF phiC : Addr → Nat}
  {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop} {credits : Nat}
  {st : Vsa.While.St} {d env : Nat} {e : Expr} {s : Stmt}
  {sp ret dst aEnv aExpr aInterp aStmt aRet : BitVec 64} {m0 : Mem} {c : Config}

theorem EvalAllocatorEntry.runtime
    (h : EvalAllocatorEntry g N M phiF phiC alloc exts shared credits st d env e
      sp ret dst aEnv aExpr m0 c) (L : AllocLedger A SL gpv headroom maxReq M) :
    EvalRuntimeEntry g N A SL phiF phiC alloc exts shared st d env e
      sp ret dst aEnv aExpr m0 c :=
  ⟨h.entry, h.allocator.runtime L, h.ast⟩

theorem ExecAllocatorEntry.runtime
    (h : ExecAllocatorEntry g N M phiF phiC alloc exts shared credits st d env s
      sp ret aInterp aStmt aEnv aRet m0 c) (L : AllocLedger A SL gpv headroom maxReq M) :
    ExecRuntimeEntry g N A SL phiF phiC alloc exts shared st d env s
      sp ret aInterp aStmt aEnv aRet m0 c :=
  ⟨h.entry, h.allocator.runtime L, h.ast⟩

#print axioms EvalAllocatorEntry.runtime
#print axioms ExecAllocatorEntry.runtime

end Vsa.Sim
