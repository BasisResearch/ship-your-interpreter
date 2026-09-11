import Vsa.Sim.ExecRuntimeEntry
import Vsa.Sim.RuntimeOwnershipDataTransport
import Vsa.Sim.EvalChildArm
import Vsa.MemReprReadChildren

open LeanRV64DExecutable Vsa
open Vsa.Machine (Config Steps)
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

namespace Vsa.Sim.EvalChildArm
open RuntimeOwnership

/-- The parent carrier and owned child entry at one dispatch endpoint. -/
structure RuntimeDispatch (D : EvalChildArm) (s : Vsa.While.Stmt) (e : Vsa.While.Expr)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (phiF phiC : Vsa.While.Addr → Nat)
    (alloc : Allocations) (exts : List Extent) (shared : Nat → Prop)
    (st : Vsa.While.St) (d env : Nat)
    (sp ret aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (gC : (R : Register) → Option (RegisterType R))
    (aC : BitVec 64) (mC : Mem) (c : Config) : Prop where
  parent : D.Carrier s e g N A SL phiF phiC st d env
    sp ret aInterp aStmt aEnv aRet m0 gC aC mC
  child : EvalRuntimeEntry gC N A SL phiF phiC alloc exts shared st d env e
    (sp - 176#64) D.retPC (D.sret (sp - 176#64)) aInterp aC mC c

variable {D : EvalChildArm} {s : Vsa.While.Stmt} {e : Vsa.While.Expr}
  {g : (R : Register) → Option (RegisterType R)}
  {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Vsa.While.Addr → Nat}
  {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop}
  {st : Vsa.While.St} {d env : Nat}
  {sp ret aInterp aStmt aEnv aRet : BitVec 64} {m0 : Mem} {before after : Config}

/-- Recover owned data from the existing dispatch's exact memory frame. -/
theorem DispatchPost.runtime
    (h : D.DispatchPost s e g N A SL phiF phiC st d env
      sp ret aInterp aStmt aEnv aRet m0 after)
    (entry : ExecRuntimeEntry g N A SL phiF phiC alloc exts shared st d env s
      sp ret aInterp aStmt aEnv aRet m0 before)
    (edge : StmtExprChild s D.childOff e) :
    ∃ gC aC mC, RuntimeDispatch D s e g N A SL phiF phiC alloc exts shared
      st d env sp ret aInterp aStmt aEnv aRet m0 gC aC mC after := by
  obtain ⟨gC, aC, mC, parent, child⟩ := h
  have hsp := entry.entry.stackBudget.2.1
  have hm : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → before.σ.mem[k]? = mC[k]? := by
    intro k hk
    rw [entry.entry.mem]
    exact (parent.mem_frame k (by omega)).symm
  have hs : ∀ k, shared k → before.σ.mem[k]? = mC[k]? :=
    fun k hk => hm k (entry.runtime.shared_off_stack hk)
  have runtime := entry.runtime.after_stack hm
  have ast := (entry.ast.transport hs).exprChild edge parent.child_read
  exact ⟨gC, aC, mC, parent, child, child.mem.symm ▸ runtime, child.mem.symm ▸ ast⟩

/-- Execute statement dispatch while retaining ownership for the child call. -/
theorem dispatch_runtime (C : D.Cert) (E : D.EntryCert) (S : D.Sem s e)
    (edge : StmtExprChild s D.childOff e)
    (entry : ExecRuntimeEntry g N A SL phiF phiC alloc exts shared st d env s
      sp ret aInterp aStmt aEnv aRet m0 before) :
    ∃ after gC aC mC, Steps before after ∧
      RuntimeDispatch D s e g N A SL phiF phiC alloc exts shared
        st d env sp ret aInterp aStmt aEnv aRet m0 gC aC mC after := by
  obtain ⟨after, steps, post⟩ := D.dispatch C E S g N A SL phiF phiC st d env
    sp ret aInterp aStmt aEnv aRet m0 before entry.entry
  obtain ⟨gC, aC, mC, owned⟩ := post.runtime entry edge
  exact ⟨after, gC, aC, mC, steps, owned⟩

#print axioms DispatchPost.runtime
#print axioms dispatch_runtime

end Vsa.Sim.EvalChildArm
