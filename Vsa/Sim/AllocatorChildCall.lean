import Vsa.Sim.AllocatorAt
import Vsa.Sim.EvalChildRuntime

open LeanRV64DExecutable Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While Vsa.Machine

namespace Vsa.Sim.EvalChildArm
open RuntimeOwnership

/-- Dispatch retains the allocator state at the same child entry as the reflected run. -/
structure AllocatorDispatch (D : EvalChildArm) (s : Stmt) (e : Expr)
    (g : (R : Register) → Option (RegisterType R)) (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (phiF phiC : Addr → Nat)
    (alloc : Allocations) (exts : List Extent) (shared : Nat → Prop) (credits : Nat)
    (st : Vsa.While.St) (d env : Nat)
    (sp ret aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (gC : (R : Register) → Option (RegisterType R)) (aC : BitVec 64) (mC : Mem)
    (after : Config) : Prop where
  parent : D.Carrier s e g N A SL phiF phiC st d env
    sp ret aInterp aStmt aEnv aRet m0 gC aC mC
  child : EvalAllocatorEntry gC N M phiF phiC alloc exts shared credits st d env e
    (sp - 176#64) D.retPC (D.sret (sp - 176#64)) aInterp aC mC after
  shared_before : AgreeP shared m0 mC

variable {D : EvalChildArm} {s : Stmt} {e : Expr}
  {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
  {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
  {M : MallocContract A SL gpv headroom maxReq} {phiF phiC : Addr → Nat}
  {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop} {credits : Nat}
  {st : Vsa.While.St} {d env : Nat}
  {sp ret aInterp aStmt aEnv aRet : BitVec 64} {m0 : Mem} {before : Config}

/-- Transport allocator-private memory through the existing dispatch frame. -/
theorem dispatch_allocator (C : D.Cert) (E : D.EntryCert) (S : D.Sem s e)
    (edge : StmtExprChild s D.childOff e)
    (entry : ExecAllocatorEntry g N M phiF phiC alloc exts shared credits st d env s
      sp ret aInterp aStmt aEnv aRet m0 before)
    (L : AllocLedger A SL gpv headroom maxReq M) :
    ∃ after gC aC mC, Steps before after ∧
      AllocatorDispatch D s e g N M phiF phiC alloc exts shared credits
        st d env sp ret aInterp aStmt aEnv aRet m0 gC aC mC after := by
  obtain ⟨after, gC, aC, mC, steps, reached⟩ :=
    dispatch_runtime C E S edge (entry.runtime L)
  have hsp := entry.entry.stackBudget.2.1
  have hm : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → before.σ.mem[k]? = mC[k]? := by
    intro k hk
    rw [entry.entry.mem]
    exact (reached.parent.mem_frame k (by omega)).symm
  have hframe : gC .x3 = g .x3 := by
    have hf := reached.parent.frame .x3 (by decide)
    simpa only [reduceCtorEq, false_or] using hf
  exact ⟨after, gC, aC, mC, steps,
    { parent := reached.parent
      child :=
        { entry := reached.child.entry
          allocator := reached.child.entry.mem.symm ▸ entry.allocator.after_stack L hm
          ast := reached.child.ast
          gp := (reached.child.entry.frame .x3 (by decide)).trans
            (hframe.trans ((entry.entry.frame .x3 (by decide)).symm.trans entry.gp)) }
      shared_before := fun k hk => by
        rw [← entry.entry.mem]
        exact hm k ((entry.allocator.runtime L).shared_off_stack hk) }⟩

/-- Parent frame and resource-indexed child result from one composed execution. -/
structure AllocatorChildReturn (D : EvalChildArm) (s : Stmt) (e : Expr)
    (g : (R : Register) → Option (RegisterType R)) (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (phiF phiC : Addr → Nat)
    (shared : Nat → Prop) (reserve : Nat) (st st' : Vsa.While.St) (d env : Nat) (v : Value)
    (sp ret aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (gC : (R : Register) → Option (RegisterType R)) (aC : BitVec 64) (mC : Mem)
    (after : Config) : Prop where
  parent : D.Carrier s e g N A SL phiF phiC st d env
    sp ret aInterp aStmt aEnv aRet m0 gC aC mC
  child : EvalAllocatorReturn gC N M phiF phiC st.store.frames.size st.store.closures.size
    shared reserve st' v (sp - 176#64) D.retPC (D.sret (sp - 176#64)) mC after
  shared_before : AgreeP shared m0 mC

/-- Execute the owned expression child at the current native addresses. -/
theorem call_allocator_at (C : D.Cert) (E : D.EntryCert) (S : D.Sem s e)
    (edge : StmtExprChild s D.childOff e)
    {cost maxRequest reserve : Nat} {st' : Vsa.While.St} {v : Value}
    (entry : ExecAllocatorEntry g N M phiF phiC alloc exts shared (cost + reserve)
      st d env s sp ret aInterp aStmt aEnv aRet m0 before)
    (L : AllocLedger A SL gpv headroom maxReq M) (hrequest : maxRequest ≤ maxReq)
    (ih : EvalAllocatorAt N st d env e st' v cost maxRequest) :
    ∃ after gC aC mC, Steps before after ∧
      AllocatorChildReturn D s e g N M phiF phiC shared reserve st st' d env v
        sp ret aInterp aStmt aEnv aRet m0 gC aC mC after := by
  obtain ⟨called, gC, aC, mC, steps, reached⟩ := dispatch_allocator C E S edge entry L
  obtain ⟨after, run, result⟩ := ih.run gC A SL gpv headroom maxReq M L hrequest
    phiF phiC alloc exts shared reserve
    (sp - 176#64) D.retPC (D.sret (sp - 176#64)) aInterp aC mC called reached.child
  exact ⟨after, gC, aC, mC, steps.trans run,
    reached.parent, result, reached.shared_before⟩

theorem call_allocator (C : D.Cert) (E : D.EntryCert) (S : D.Sem s e)
    (edge : StmtExprChild s D.childOff e)
    {cost maxRequest reserve : Nat} {st' : Vsa.While.St} {v : Value}
    (entry : ExecAllocatorEntry g N M phiF phiC alloc exts shared (cost + reserve)
      st d env s sp ret aInterp aStmt aEnv aRet m0 before)
    (L : AllocLedger A SL gpv headroom maxReq M) (hrequest : maxRequest ≤ maxReq)
    (ih : EvalAllocatorIH st d env e st' v cost maxRequest) :
    ∃ after gC aC mC, Steps before after ∧
      AllocatorChildReturn D s e g N M phiF phiC shared reserve st st' d env v
        sp ret aInterp aStmt aEnv aRet m0 gC aC mC after :=
  call_allocator_at C E S edge entry L hrequest (ih.at N)

#print axioms dispatch_allocator
#print axioms call_allocator_at
#print axioms call_allocator

end Vsa.Sim.EvalChildArm
