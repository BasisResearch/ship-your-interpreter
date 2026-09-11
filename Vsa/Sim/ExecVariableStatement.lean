import Vsa.Sim.EvalChildVariable
import Vsa.Sim.rows.Field_hSExprClosed

namespace Vsa.Sim
open LeanRV64DExecutable Vsa
open Vsa.Machine (Config Steps)
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc
open RuntimeOwnership

/-- A nonallocating statement retains the runtime at its original maps. -/
structure ExecRuntimeLeafReturn
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (phiF phiC : Vsa.While.Addr → Nat)
    (alloc : Allocations) (shared : Nat → Prop) (st : Vsa.While.St)
    (sp ret aRet : BitVec 64) (m0 : Mem) (after : Config) : Prop where
  exit : ExecExitD g N A SL phiF phiC st.store.frames.size st.store.closures.size
    st .normal sp ret aRet m0 after
  runtime : ∃ exts, StoreRuntimeData N A SL phiF phiC alloc exts shared st.store after.σ.mem
  shared_agree : ∀ k, shared k → after.σ.mem[k]? = m0[k]?

/-- A variable expression statement executes lookup and returns normal.
Its child proof consumes the owned statement entry directly. -/
theorem exec_variable_statement_owned
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Vsa.While.Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop}
    {st : Vsa.While.St} {d env : Nat} {query : String} {v : Vsa.While.Value}
    {sp ret aInterp aStmt aEnv aRet : BitVec 64} {m0 : Mem} {before : Config}
    (entry : ExecRuntimeEntry g N A SL phiF phiC alloc exts shared st d env
      (.expr (.var query)) sp ret aInterp aStmt aEnv aRet m0 before)
    (hget : st.store.get? env query = some v) :
    ∃ after, Steps before after ∧
      ExecRuntimeLeafReturn g N A SL phiF phiC alloc shared st sp ret aRet m0 after := by
  obtain ⟨returned, gC, aC, mC, run, result⟩ :=
    EvalChildArm.variable_runtime stmtExprArm_cert stmtExprArm_entryCert
      (stmtExprArm_sem (.var query)) (.expr (.var query)) entry hget
  obtain ⟨resultF, resultC, pre⟩ :=
    stmtExprArm.normalExitPre_of_exit stmtExprArm_cert result.parent returned
      result.child.returned.exit
  obtain ⟨after, tail, exit⟩ :=
    normalExitTail_memory stmtExprArm.retPC (0x1fff14#21) stmtExprArm_liSite
      stmtExprArm_jSite (by decide) returned pre
  refine ⟨after, run.trans tail, exit.exit, ?_, ?_⟩
  · rw [exit.memory]
    exact result.child.runtime
  · rw [exit.memory]
    exact result.shared_agree stmtExprArm_cert

/-- Project ordinary statement correctness from the same owned return. -/
theorem exec_variable_statement
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Vsa.While.Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop}
    {st : Vsa.While.St} {d env : Nat} {query : String} {v : Vsa.While.Value}
    {sp ret aInterp aStmt aEnv aRet : BitVec 64} {m0 : Mem} {before : Config}
    (entry : ExecRuntimeEntry g N A SL phiF phiC alloc exts shared st d env
      (.expr (.var query)) sp ret aInterp aStmt aEnv aRet m0 before)
    (hget : st.store.get? env query = some v) :
    ∃ after, Steps before after ∧
      ExecExitD g N A SL phiF phiC st.store.frames.size st.store.closures.size
        st .normal sp ret aRet m0 after := by
  obtain ⟨after, steps, result⟩ := exec_variable_statement_owned entry hget
  exact ⟨after, steps, result.exit⟩

#print axioms exec_variable_statement_owned
#print axioms exec_variable_statement

end Vsa.Sim
