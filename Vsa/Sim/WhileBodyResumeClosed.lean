import Vsa.Sim.WhileBodyLoopResume
import Vsa.Sim.WhileBodyBreakResume
import Vsa.Sim.WhileBodyRetResume

namespace Vsa.Sim

open LeanRV64DExecutable Sail
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Logic (Triple)

/-- The status routes permitted by the source while constructors. -/
inductive WhileBodyRoute : Status → Status → Prop where
  | continuing {bodyStatus finalStatus} :
      (bodyStatus = .normal ∨ bodyStatus = .cont) →
      WhileBodyRoute bodyStatus finalStatus
  | breaking : WhileBodyRoute .brk .normal
  | returning (value : Value) : WhileBodyRoute (.ret value) (.ret value)

/-- The complete body-resume boundary for every source while route. -/
theorem execWhileBodyResume_closed
    {g gBody : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {φf φc φfBody φcBody : Addr → Nat}
    {st stCond stMid stFin : Vsa.While.St} {d : Nat} {env : Addr}
    {cnd : Expr} {body : Stmt} {bodyStatus finalStatus : Status}
    {sp r aInterp aStmt aEnv aRet aBody : BitVec 64} {m0 mBody : Mem}
    (hSize : StoreLe st.store stCond.store)
    (hBody : ExecS stCond d env body stMid bodyStatus)
    (hRoute : WhileBodyRoute bodyStatus finalStatus)
    (hpf : PhiExtends φf φfBody st.store.frames.size)
    (hpc : PhiExtends φc φcBody st.store.closures.size)
    (h : ExecWhileBodyCarrier g N A SL φfBody φcBody stCond d env cnd body
      sp r aInterp aStmt aEnv aRet m0 gBody aBody mBody) :
    Triple
      (ExecExitD gBody N A SL φfBody φcBody stCond.store.frames.size
        stCond.store.closures.size stMid bodyStatus
        (sp - 176#64) 0x80004088#64 aRet mBody)
      (ExecWhileStepPostI g N A SL φf φc st stMid stFin d env cnd body
        bodyStatus finalStatus sp r aInterp aStmt aEnv aRet m0) := by
  cases hRoute with
  | continuing hContinue =>
    exact execWhileBodyResume_continue hSize hBody hContinue hpf hpc h
  | breaking =>
    intro cfg hChild
    obtain ⟨cfg', hs, hExit⟩ := execWhileBodyResume_break hSize hBody hpf hpc h cfg hChild
    exact ⟨cfg', hs, Or.inr ⟨by simp, hExit⟩⟩
  | returning value =>
    intro cfg hChild
    obtain ⟨cfg', hs, hExit⟩ := execWhileBodyResume_ret hSize hBody hpf hpc h cfg hChild
    exact ⟨cfg', hs, Or.inr ⟨by simp, hExit⟩⟩

#print axioms execWhileBodyResume_closed

end Vsa.Sim
