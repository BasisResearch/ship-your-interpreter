import Vsa.Sim.WhileCondDispatchClosed
import Vsa.Sim.WhileCondFalseResume
import Vsa.Sim.rows.ExecDispatchRows

namespace Vsa.Sim.ScaffoldRows

open LeanRV64DExecutable Sail
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Rows

/-- Concrete supplier for the false-condition while residual. -/
theorem field_hSWhileFalse :
    ∀ st st' d env c b v hC,
      WhileFalseCaseResid st st' d env c b v hC := by
  intro st st' d env c b v hC hFalsy _
    g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 _ _
  exact
    { condDispatch := execWhileCondDispatch_closed g N A SL φf φc
        st d env c b sp r aInterp aStmt aEnv aRet m0
      condResume := fun _ _ _ hCarrier =>
        execWhileCondResume_false hFalsy hCarrier }

#print axioms field_hSWhileFalse

end Vsa.Sim.ScaffoldRows
