import Vsa.Sim.RuntimeIH
import Vsa.Sim.EvalChildRuntime

open LeanRV64DExecutable Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While Vsa.Machine

namespace Vsa.Sim.EvalChildArm
open RuntimeOwnership

/-- The actual recursive child return and its enclosing statement frame. -/
structure RuntimeChildReturn (D : EvalChildArm) (s : Stmt) (e : Expr)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (phiF phiC : Addr → Nat)
    (shared : Nat → Prop) (st st' : Vsa.While.St) (d env : Nat) (v : Value)
    (sp ret aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (gC : (R : Register) → Option (RegisterType R)) (aC : BitVec 64) (mC : Mem)
    (after : Config) : Prop where
  parent : D.Carrier s e g N A SL phiF phiC st d env
    sp ret aInterp aStmt aEnv aRet m0 gC aC mC
  child : EvalRuntimeReturn gC N A SL phiF phiC st.store.frames.size st.store.closures.size
    shared st' v (sp - 176#64) D.retPC (D.sret (sp - 176#64)) mC after
  shared_before : AgreeP shared m0 mC

/-- Dispatch and invoke the owned child IH while retaining the same endpoint. -/
theorem call_runtime
    {D : EvalChildArm} {s : Stmt} {e : Expr}
    (C : D.Cert) (E : D.EntryCert) (S : D.Sem s e) (edge : StmtExprChild s D.childOff e)
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop}
    {st st' : Vsa.While.St} {d env : Nat} {v : Value}
    {sp ret aInterp aStmt aEnv aRet : BitVec 64} {m0 : Mem} {before : Config}
    (entry : ExecRuntimeEntry g N A SL phiF phiC alloc exts shared st d env s
      sp ret aInterp aStmt aEnv aRet m0 before)
    (ih : EvalRuntimeIH st d env e st' v) :
    ∃ after gC aC mC, Steps before after ∧
      RuntimeChildReturn D s e g N A SL phiF phiC shared st st' d env v
        sp ret aInterp aStmt aEnv aRet m0 gC aC mC after := by
  obtain ⟨called, gC, aC, mC, steps, dispatch⟩ := dispatch_runtime C E S edge entry
  obtain ⟨after, run, result⟩ := ih.run gC N A SL phiF phiC alloc exts shared
    (sp - 176#64) D.retPC (D.sret (sp - 176#64)) aInterp aC mC called dispatch.child
  refine ⟨after, gC, aC, mC, steps.trans run, dispatch.parent, result, ?_⟩
  intro k hk
  have off := entry.runtime.shared_off_stack hk
  have hsp := entry.entry.stackBudget.2.1
  exact (dispatch.parent.mem_frame k (by omega)).symm

#print axioms call_runtime

end Vsa.Sim.EvalChildArm
