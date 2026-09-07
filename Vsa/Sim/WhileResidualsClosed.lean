import Vsa.Sim.WhileCondDispatchClosed
import Vsa.Sim.WhileBodyDispatchClosed
import Vsa.Sim.WhileBodyResumeClosed
import Vsa.Sim.rows.ExecDispatchRows

namespace Vsa.Sim

open LeanRV64DExecutable Sail
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Rows

/-- All three finite boundaries of a source while iteration. -/
theorem execWhileStepGeom_closed
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st stCond stMid stFin : Vsa.While.St) (d : Nat) (env : Addr)
    (cnd : Expr) (body : Stmt) (v : Value) (bodyStatus finalStatus : Status)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (hCond : EvalE st d env cnd stCond v)
    (hBody : ExecS stCond d env body stMid bodyStatus)
    (hTruthy : v.truthy = true)
    (hRoute : WhileBodyRoute bodyStatus finalStatus) :
    ExecWhileStepGeomI g N A SL φf φc st stCond stMid stFin d env cnd body v
      bodyStatus finalStatus sp r aInterp aStmt aEnv aRet m0 := by
  exact
    { truthy := hTruthy
      condDispatch := execWhileCondDispatch_closed g N A SL φf φc st d env cnd body
        sp r aInterp aStmt aEnv aRet m0
      bodyDispatch := fun _ _ _ hCarrier =>
        execWhileBodyDispatch_closed hCond hTruthy hCarrier
      bodyResume := fun _ _ _ _ _ hpf hpc hCarrier =>
        execWhileBodyResume_closed (evalE_store_mono hCond) hBody hRoute hpf hpc hCarrier }

namespace ScaffoldRows

/-- Concrete supplier for the breaking-while residual. -/
theorem field_hSWhileBreak :
    ∀ st stC stB d env c b v hC hB,
      WhileBreakCaseResid st stC stB d env c b v hC hB := by
  intro st stC stB d env c b v hC hB hTruthy _ _
    g N A SL φf φc sp r aInterp aStmt aEnv aRet m0
  exact ⟨execWhileStepGeom_closed g N A SL φf φc st stC stB stB d env c b v
    .brk .normal sp r aInterp aStmt aEnv aRet m0 hC hB hTruthy .breaking⟩

/-- Concrete supplier for the returning-while residual. -/
theorem field_hSWhileRet :
    ∀ st stC stB d env c b v rv hC hB,
      WhileRetCaseResid st stC stB d env c b v rv hC hB := by
  intro st stC stB d env c b v rv hC hB hTruthy _ _
    g N A SL φf φc sp r aInterp aStmt aEnv aRet m0
  exact ⟨execWhileStepGeom_closed g N A SL φf φc st stC stB stB d env c b v
    (.ret rv) (.ret rv) sp r aInterp aStmt aEnv aRet m0 hC hB hTruthy (.returning rv)⟩

/-- Concrete supplier for the continuing-while residual. -/
theorem field_hSWhileLoop :
    ∀ st stC stB stR d env c b v bodyStatus finalStatus hC hB hRest,
      WhileLoopCaseResid st stC stB stR d env c b v bodyStatus finalStatus hC hB hRest := by
  intro st stC stB stR d env c b v bodyStatus finalStatus hC hB hRest
    hTruthy hContinue _ _ _ _ g N A SL φf φc sp r aInterp aStmt aEnv aRet m0
  exact ⟨execWhileStepGeom_closed g N A SL φf φc st stC stB stR d env c b v
    bodyStatus finalStatus sp r aInterp aStmt aEnv aRet m0 hC hB hTruthy
      (.continuing hContinue)⟩

#print axioms field_hSWhileBreak
#print axioms field_hSWhileRet
#print axioms field_hSWhileLoop

end ScaffoldRows
end Vsa.Sim
