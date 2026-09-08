import Vsa.Sim.rows.ExecRecRows
import Vsa.Sim.rows.EvalChildArmVarInit
import Vsa.Sim.EvalReturn

/-!
# `ExecVarInitRow` — the initialised declaration's recursor row

`exec_varInit_row` fills the `hSVarInit` minor premise of the term recursor
from the residual `VarInitResid`: the parametric child dispatch
(`stmtVarInitArm`, `rows/EvalChildArmVarInit.lean`) and the resume from the
child's widened exit (`rows/Field_hSVarInitClosed.lean`, through the shared
declaration tail `envDefineTail_run`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

end Vsa.Sim

/-! ## The `mExecS`-motive case row (the recursor-premise adapter)

`exec_varInit_row` marshals `execVarDeclSimD` into the exact minor-premise slot of
`execSeq_sim_of_cases`/`term_sim_of_cases` (`hSVarInit`).  As for the recursive
`expr`/`ret` rows (`rows/ExecRecRows.lean`), the premise is `ExecIH …` by definitional
unfolding (`mExecS = ExecIH`), and the sub-derivation IH the recursor hands the case
(`mEvalE st d env e st' v a`) is the coherent `EvalReturnIH TrivialOwned …`, whose
`.run` lands the child's `EvalReturn` (widened exit + ONE selected map pair) at the
reached entry; the resume consumes that pair (`rows/Field_hSVarInitClosed.lean`).
The per-case `ExecVarInitGeom` bundle (∀-closed over the ghosts) carries the geometry +
glue (the `env_define` oracle) + widener. -/
namespace Vsa.Sim.Rows

open Vsa.Sim
open Vsa.Sim.TermSimAssembly

local notation "SpecSt" => Vsa.While.St

/-- The two finite boundaries of the initialised declaration around the actual
child evaluation: the parametric arm dispatch (`stmtVarInitArm`) and the
resume from the child's widened exit (`ld a1,8(s0)`, the copy to `esp+16`, the
`env_define` call, and the normal epilogue at `0x80004118`). -/
structure VarInitCaseGeom
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr) (v : Value)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) : Prop where
  dispatch : Triple
    (Vsa.Sim.ExecEntry g N A SL φf φc st d env (.varDecl x (some e))
      sp r aInterp aStmt aEnv aRet m0)
    (stmtVarInitArm.DispatchPost (.varDecl x (some e)) e g N A SL φf φc st d env
      sp r aInterp aStmt aEnv aRet m0)
  resume : ∀ (gC : (R : Register) → Option (RegisterType R)) (aC : BitVec 64) (mC : Mem),
    stmtVarInitArm.Carrier (.varDecl x (some e)) e g N A SL φf φc st d env
      sp r aInterp aStmt aEnv aRet m0 gC aC mC →
    EvalE st d env e st' v →
    Triple
      (EvalReturn gC N A SL φf φc st.store.frames.size st.store.closures.size st' v
        (sp - 176#64) stmtVarInitArm.retPC (stmtVarInitArm.sret (sp - 176#64)) mC
        (fun _ _ _ => True))
      (ExecExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        ⟨st'.store.define env x v, st'.out⟩ .normal sp r aRet m0)

/-- The varInit-case residual: `VarInitCaseGeom` ∀-closed over the ghosts. -/
def VarInitResid (st st' : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr)
    (v : Value) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem),
    VarInitCaseGeom g N A SL φf φc st st' d env x e v sp r aInterp aStmt aEnv aRet m0

/-- The resume seam alone (it carries the `env_define` callee contract).  The
dispatch half is generic (`execStmtVarInitDispatch_generic`). -/
def VarInitResumeResid (st st' : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr)
    (v : Value) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (gC : (R : Register) → Option (RegisterType R)) (aC : BitVec 64) (mC : Mem),
    stmtVarInitArm.Carrier (.varDecl x (some e)) e g N A SL φf φc st d env
      sp r aInterp aStmt aEnv aRet m0 gC aC mC →
    EvalE st d env e st' v →
    Triple
      (EvalReturn gC N A SL φf φc st.store.frames.size st.store.closures.size st' v
        (sp - 176#64) stmtVarInitArm.retPC (stmtVarInitArm.sret (sp - 176#64)) mC
        (fun _ _ _ => True))
      (ExecExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        ⟨st'.store.define env x v, st'.out⟩ .normal sp r aRet m0)

/-- The dispatch half is generic; only the resume seam is residual. -/
theorem varInitResid_of_resume {st st' : SpecSt} {d : Nat} {env : Addr} {x : String}
    {e : Expr} {v : Value}
    (h : VarInitResumeResid st st' d env x e v) : VarInitResid st st' d env x e v :=
  fun g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 =>
    { dispatch := execStmtVarInitDispatch_generic g N A SL φf φc st d env x e
        sp r aInterp aStmt aEnv aRet m0
      resume := h g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 }

/-- Route `hSVarInit`: dispatch to the child, apply its IH at the reached
entry, and resume at its widened exit. -/
theorem exec_varInit_row
    (hR : ∀ st st' d env x e v, VarInitResid st st' d env x e v) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr) (st' : SpecSt)
      (v : Value) (a : EvalE st d env e st' v),
      mEvalE st d env e st' v a →
      mExecS st d env (Stmt.varDecl x (some e))
        { store := st'.store.define env x v, out := st'.out }
        Status.normal (ExecS.varInit st d env x e st' v a) := by
  intro st d env x e st' v a hIH
  show Vsa.Sim.ExecIH st d env (.varDecl x (some e))
    ⟨st'.store.define env x v, st'.out⟩ .normal
  intro g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 cfg hEntry
  let G := hR st st' d env x e v g N A SL φf φc sp r aInterp aStmt aEnv aRet m0
  obtain ⟨cfgC, hsC, gC, aC, mC, hCarrier, hChildEntry⟩ := G.dispatch cfg hEntry
  obtain ⟨cfgX, hsX, hChildExit⟩ :=
    hIH.run gC N A SL φf φc (sp - 176#64) stmtVarInitArm.retPC
      (stmtVarInitArm.sret (sp - 176#64)) aInterp aC mC cfgC hChildEntry
  obtain ⟨cfgD, hsD, hExit⟩ := G.resume gC aC mC hCarrier a cfgX hChildExit
  exact ⟨cfgD, hsC.trans (hsX.trans hsD), hExit⟩

/-- **Slot-verify.** `exec_varInit_row` fills the EXACT `hSVarInit` minor-premise slot
of `TermCaseBundle.TermCases.hSVarInit`: the type below is the verbatim premise type;
the term type-checks iff the row's conclusion matches it. -/
theorem exec_varInit_row_fills_hSVarInit
    (hR : ∀ st st' d env x e v, VarInitResid st st' d env x e v) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr) (st' : SpecSt)
      (v : Value) (a : EvalE st d env e st' v),
      mEvalE st d env e st' v a →
      mExecS st d env (Stmt.varDecl x (some e))
        { store := st'.store.define env x v, out := st'.out }
        Status.normal (ExecS.varInit st d env x e st' v a) :=
  exec_varInit_row hR

end Vsa.Sim.Rows

#print axioms Vsa.Sim.Rows.exec_varInit_row
#print axioms Vsa.Sim.Rows.exec_varInit_row_fills_hSVarInit
