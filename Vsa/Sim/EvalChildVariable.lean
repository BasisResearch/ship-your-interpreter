import Vsa.Sim.EvalChildRuntime
import Vsa.Sim.EnvGetReflected.EvalRuntimeEntry

open LeanRV64DExecutable Vsa
open Vsa.Machine (Config Steps)
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

namespace Vsa.Sim.EvalChildArm
open RuntimeOwnership EnvGetReflected

/-- A variable child returns with its owned runtime and the enclosing frame. -/
structure RuntimeVariableReturn (D : EvalChildArm) (s : Vsa.While.Stmt) (query : String)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (phiF phiC : Vsa.While.Addr → Nat)
    (alloc : Allocations) (shared : Nat → Prop) (st : Vsa.While.St) (d env : Nat)
    (v : Vsa.While.Value) (sp ret aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (gC : (R : Register) → Option (RegisterType R))
    (aC : BitVec 64) (mC : Mem) (after : Config) : Prop where
  parent : D.Carrier s (.var query) g N A SL phiF phiC st d env
    sp ret aInterp aStmt aEnv aRet m0 gC aC mC
  child : VarEvalResult gC N A SL phiF phiC alloc shared st v
    (sp - 176#64) D.retPC (D.sret (sp - 176#64)) mC after

/-- Execute the statement prefix and actual owned variable call at one endpoint. -/
theorem variable_runtime
    {D : EvalChildArm} {s : Vsa.While.Stmt} {query : String}
    (C : D.Cert) (E : D.EntryCert) (S : D.Sem s (.var query))
    (edge : StmtExprChild s D.childOff (.var query))
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Vsa.While.Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop}
    {st : Vsa.While.St} {d env : Nat} {v : Vsa.While.Value}
    {sp ret aInterp aStmt aEnv aRet : BitVec 64} {m0 : Mem} {before : Config}
    (entry : ExecRuntimeEntry g N A SL phiF phiC alloc exts shared st d env s
      sp ret aInterp aStmt aEnv aRet m0 before)
    (hget : st.store.get? env query = some v) :
    ∃ after gC aC mC, Steps before after ∧
      RuntimeVariableReturn D s query g N A SL phiF phiC alloc shared st d env v
        sp ret aInterp aStmt aEnv aRet m0 gC aC mC after := by
  obtain ⟨called, gC, aC, mC, steps, dispatch⟩ := dispatch_runtime C E S edge entry
  obtain ⟨after, run, child⟩ := eval_var_owned dispatch.child hget
  exact ⟨after, gC, aC, mC, steps.trans run, dispatch.parent, child⟩

#print axioms variable_runtime

/-- The variable call preserves the parent's shared reads at its actual return. -/
theorem RuntimeVariableReturn.shared_agree
    {D : EvalChildArm} {s : Vsa.While.Stmt} {query : String}
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Vsa.While.Addr → Nat}
    {alloc : Allocations} {shared : Nat → Prop} {st : Vsa.While.St} {d env : Nat}
    {v : Vsa.While.Value} {sp ret aInterp aStmt aEnv aRet : BitVec 64} {m0 mC : Mem}
    {gC : (R : Register) → Option (RegisterType R)} {aC : BitVec 64} {after : Config}
    (h : RuntimeVariableReturn D s query g N A SL phiF phiC alloc shared st d env v
      sp ret aInterp aStmt aEnv aRet m0 gC aC mC after) (C : D.Cert) :
    ∀ k, shared k → after.σ.mem[k]? = m0[k]? := by
  have hframe : SL.lo + 176 ≤ sp.toNat := by
    have := h.parent.stack_budget.1
    have := Vsa.While.Stmt.stackNeed_ge s
    simp only [Vsa.While.execFrame] at *
    omega
  have hsp176 : 176 ≤ sp.toNat := by omega
  have hsp := h.parent.stack_budget.2.1
  have hesp := esp_toNat sp hsp176
  have hdst := D.sret_toNat C sp hsp176
  have hroom := C.sret_room
  obtain ⟨exts, runtime⟩ := h.child.runtime
  intro k hk
  have off := runtime.shared_off_stack hk
  exact (h.child.memory.agree k (by omega) (by omega)).trans
    (h.parent.mem_frame k (by omega))

#print axioms RuntimeVariableReturn.shared_agree

end Vsa.Sim.EvalChildArm
