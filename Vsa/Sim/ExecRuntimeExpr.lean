import Vsa.Sim.RuntimeChildCall
import Vsa.Sim.RuntimeReturnAdapters
import Vsa.Sim.EvalRuntimeVariable
import Vsa.Sim.rows.Field_hSExprClosed

open LeanRV64DExecutable Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While Vsa.Machine

namespace Vsa.Sim

/-- Expression statements retain the child IH's actual runtime and selected maps. -/
theorem execRuntimeIH_expr {st st' : Vsa.While.St} {d env : Nat} {e : Expr} {v : Value}
    (ih : EvalRuntimeIH st d env e st' v) : ExecRuntimeIH st d env (.expr e) st' .normal where
  run := by
    intro g N A SL phiF phiC alloc exts shared sp ret aInterp aStmt aEnv aRet m0 before entry
    obtain ⟨returned, gC, aC, mC, steps, result⟩ :=
      EvalChildArm.call_runtime stmtExprArm_cert stmtExprArm_entryCert
        (stmtExprArm_sem e) (.expr e) entry ih
    obtain ⟨tailF, tailC, pre⟩ := stmtExprArm.normalExitPre_of_exit
      stmtExprArm_cert result.parent returned result.child.exit
    obtain ⟨after, tail, exit⟩ := normalExitTail_memory stmtExprArm.retPC (0x1fff14#21)
      stmtExprArm_liSite stmtExprArm_jSite (by decide) returned pre
    obtain ⟨resultF, resultC, repr⟩ := result.child.repr.selected
    have hrepr : ReturnRepr N A phiF phiC resultF resultC
        st.store.frames.size st.store.closures.size st'.store []
        (RuntimeResult N A SL shared st'.store [] m0)
        (fun k => SL.lo ≤ k ∧ k < SL.hi) after.σ.mem := by
      rw [exit.memory]
      exact
        { frames := repr.frames
          closures := repr.closures
          values := fun _ _ h => False.elim (List.not_mem_nil h)
          owned := repr.owned.rebase (fun _ h => False.elim (List.not_mem_nil h))
            result.shared_before
          survives := repr.survives }
    exact ⟨after, steps.trans tail, exit.exit.withRuntimeRepr hrepr⟩

/-- The variable supplier is consumed through the generic owned child contract. -/
theorem execRuntimeIH_var_statement
    {st : Vsa.While.St} {d env : Nat} {query : String} {v : Value}
    (hget : st.store.get? env query = some v) :
    ExecRuntimeIH st d env (.expr (.var query)) st .normal :=
  execRuntimeIH_expr (evalRuntimeIH_var hget)

#print axioms execRuntimeIH_expr
#print axioms execRuntimeIH_var_statement

end Vsa.Sim
