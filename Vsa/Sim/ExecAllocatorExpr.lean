import Vsa.Sim.ExecAllocatorAt
import Vsa.Sim.AllocatorChildCall
import Vsa.Sim.AllocatorReturnAdapters
import Vsa.Sim.EvalAllocatorVariable
import Vsa.Sim.rows.Field_hSExprClosed

open LeanRV64DExecutable Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While Vsa.Machine

namespace Vsa.Sim

/-- Return normally with the fixed-address expression child's allocator reserve. -/
theorem execAllocatorAt_expr {N : NativeAddrs} {st st' : Vsa.While.St} {d env : Nat} {e : Expr} {v : Value}
    {cost maxRequest : Nat} (ih : EvalAllocatorAt N st d env e st' v cost maxRequest) :
    ExecAllocatorAt N st d env (.expr e) st' .normal cost maxRequest where
  run := by
    intro g A SL gpv headroom maxReq M L hrequest
      phiF phiC alloc exts shared reserve sp ret aInterp aStmt aEnv aRet m0 before entry
    obtain ⟨returned, gC, aC, mC, steps, result⟩ :=
      EvalChildArm.call_allocator_at stmtExprArm_cert stmtExprArm_entryCert
        (stmtExprArm_sem e) (.expr e) entry L hrequest ih
    obtain ⟨tailF, tailC, pre⟩ := stmtExprArm.normalExitPre_of_exit
      stmtExprArm_cert result.parent returned result.child.returned.exit
    obtain ⟨after, tail, exit⟩ := normalExitTail_memory stmtExprArm.retPC (0x1fff14#21)
      stmtExprArm_liSite stmtExprArm_jSite (by decide) returned pre
    obtain ⟨resultF, resultC, repr⟩ := result.child.returned.repr.selected
    have hrepr : ReturnRepr N A phiF phiC resultF resultC
        st.store.frames.size st.store.closures.size st'.store []
        (AllocatorResult M N shared reserve st'.store [] m0)
        (fun k => SL.lo ≤ k ∧ k < SL.hi) after.σ.mem := by
      rw [exit.memory]
      exact
        { frames := repr.frames
          closures := repr.closures
          values := fun _ _ h => False.elim (List.not_mem_nil h)
          owned := repr.owned.rebase (fun _ h => False.elim (List.not_mem_nil h))
            result.shared_before
          survives := repr.survives }
    have gp := (exit.exit.1.frame .x3 (by decide)).trans
      ((entry.entry.frame .x3 (by decide)).symm.trans entry.gp)
    exact ⟨after, steps.trans tail, exit.exit.withAllocatorRepr hrepr L gp⟩

/-- Expression statements inherit the child's allocation cost and request bound. -/
theorem execAllocatorIH_expr {st st' : Vsa.While.St} {d env : Nat} {e : Expr} {v : Value}
    {cost maxRequest : Nat} (ih : EvalAllocatorIH st d env e st' v cost maxRequest) :
    ExecAllocatorIH st d env (.expr e) st' .normal cost maxRequest where
  run := fun g N => (execAllocatorAt_expr (ih.at N)).run g

/-- Variable expression statements preserve the caller's full allocation credit. -/
theorem execAllocatorIH_var_statement
    {st : Vsa.While.St} {d env : Nat} {query : String} {v : Value}
    (hget : st.store.get? env query = some v) :
    ExecAllocatorIH st d env (.expr (.var query)) st .normal 0 0 :=
  execAllocatorIH_expr (evalAllocatorIH_var hget)

#print axioms execAllocatorAt_expr
#print axioms execAllocatorIH_expr
#print axioms execAllocatorIH_var_statement

end Vsa.Sim
