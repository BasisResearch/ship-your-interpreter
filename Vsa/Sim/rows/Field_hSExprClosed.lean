import Vsa.Sim.rows.ExecRecRows

/-!
# `Field_hSExprClosed` — the expression-statement residual, closed

`hSExpr` is the first statement field closed entirely by the parametric
`EvalChildArm` layer: the arm dispatch is the generic instance at
`stmtExprArm`, and the resume is the generic normal-exit head at the arm's
`li a0,0` (`0x80004184`) followed by the parametric tail.
-/

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

/-- The `li a0,0` site of the `expr` arm. -/
theorem stmtExprArm_liSite : LiZeroSite stmtExprArm.retPC :=
  fun σ i u vmi hG hpc hmi hmem hi =>
    site_80004184_es σ i u _ vmi hG hpc hmi hmem (by decide) hi

/-- The `j 0x8000409c` site of the `expr` arm. -/
theorem stmtExprArm_jSite : JumpSite (BitVec.addInt stmtExprArm.retPC 4) (0x1fff14#21) :=
  fun σ i u vmi hG hpc hmi hmem htgt hi =>
    site_80004188_es σ i u _ vmi hG hpc hmi hmem (by decide) htgt hi

/-- Concrete supplier for the expression-statement residual. -/
theorem ScaffoldRows.field_hSExpr :
    ∀ st st' d env e v, Rows.ExprResid st st' d env e v := by
  intro st st' d env e v g N A SL φf φc sp r aInterp aStmt aEnv aRet m0
  exact
    { dispatch := execStmtExprDispatch_generic g N A SL φf φc st d env e
        sp r aInterp aStmt aEnv aRet m0
      resume := fun gC aC mC hCarrier cfg hExit =>
        let ⟨φf', φc', hPre⟩ :=
          stmtExprArm.normalExitPre_of_exit stmtExprArm_cert hCarrier cfg hExit
        normalExitTail stmtExprArm.retPC (0x1fff14#21) stmtExprArm_liSite
          stmtExprArm_jSite (by decide) cfg hPre }

#print axioms ScaffoldRows.field_hSExpr

end Vsa.Sim
