import Vsa.Sim.ExecVarDecl
import Vsa.Sim.rows.ExecRecRows

/-!
# `ExecVarInitRow` — the `hSVarInit` recursor case row (`ExecS.varInit`)

The `varDecl x (some e)` case of `term_sim_of_cases`/`execSeq_sim_of_cases`
(`TermCaseBundle.hSVarInit`, verbatim):

```
∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr) (st' : SpecSt)
  (v : Value) (a : EvalE st d env e st' v),
  mEvalE st d env e st' v a →
  mExecS st d env (Stmt.varDecl x (some e))
    { store := st'.store.define env x v, out := st'.out } Status.normal
    (ExecS.varInit st d env x e st' v a)
```

which is `ExecIH st d env (.varDecl x (some e)) ⟨st'.store.define env x v, st'.out⟩
.normal` by definitional unfolding (`TermSimAssembly.mExecS = ExecBlock.ExecIH`), and
the sub-derivation IH `mEvalE st d env e st' v a` is `EvalRecCommon.EvalIH st d env e
st' v` by the SAME unfolding (`mEvalE = EvalIH`), so it passes straight to the sim's
`hIH` by `rfl` — no adapter.

`execVarDeclSim` (`ExecVarDecl.lean`) already proves the packaged
`Triple (ExecEntry (.varDecl x (some e)) ∧ sailOutput=out0) (ExecExit …
⟨st'.store.define env x v, st'.out⟩ .normal …)` — conditional on the jump-table
slot pin + the body glue `hGlue` (which consumes the `EvalIH` for the initializer
AND the **`env_define` callee**, producing the `Store.define` post-state).  So this
file is the `varInit` twin of `rows/ExecRecRows.lean`'s `execVarNullSimD` /
`exec_varNull_row`, but RECURSIVE (it consumes the sub-`EvalIH`), and its exit store
is `st'.store.define env x v` at a NON-identity φ (the `define` grows the frame's
binding list, and the sub-eval may have extended the maps) — so the parametric
recursive widener `ExecRecWiden` (NOT the identity-φ leaf widener) applies.

## The `env_define` oracle (leaf_bridge_oracle pattern — `rows/EvalVarRow.lean`)

`execVarDeclSim`'s `hGlue` is the sole honest residual: the whole varInit body
(`beqz`-not-taken init load ≫ `jal eval_expr` (the `EvalIH`) ≫ value reload/stage ≫
**`jal env_define`** ≫ `li a0,0`) reaching `0x80004118` in a `SubExecReturn` for the
DEFINED post-state.  The `env_define` callee is consumed INSIDE `hGlue` as a named
`Triple` oracle — the module doc of `ExecVarDecl.lean` records that there is no
top-level `env_define` Triple to reuse, so like `EvalVarRow`'s `env_get_found` field
it is threaded as the case's genuinely-open `O`-class residual.  With
`Vsa/Sim/EnvDefMarshal.env_define_append_spec` now landed (the append path assembled
with `bridgeStore` supplied), the `env_define` callee this `hGlue` consumes IS
dischargeable — what remains between `env_define_append_spec` and this `hGlue` is the
varInit-arm call linkage (the arg-setup prefix at `0x80004100→jal env_define`, and
the `env_define` post → `SubExecReturn` repackaging), a `callSeg`-style splice.  Until
that bridge lands the row threads `hGlue` as the named residual (exactly `EvalVarRow`'s
conditional-leaf_bridge discipline).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
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

/-! ## `ExecVarInitGeom` — the `hSVarInit` recursor-supplied residual bundle

Everything `execVarDeclSim` needs beyond the sub-`EvalIH` (which the recursor hands
the case for free, `rfl`-passed): the `execBlockA` jump-table slot pin + its
stack-disjointness, the body glue `hGlue` (consuming the sub-eval AND the
`env_define` callee, the `O`-class oracle), and the recursive widener at the DEFINED
post-store.  This is the `ExecExprGeom`/`ExecVarNullGeom` twin for the recursive,
`define`-post `varInit` case: one bundle, ∀-closed over the ghosts in the row. -/
def ExecVarInitGeom
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (x : String) (e : Expr) (v : Value)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) : Prop :=
  StmtSlotPinned 1 execArmVarDecl m0 ∧
  (stmtJumpTableBase + 4 * 1 + 4 ≤ SL.lo ∨ sp.toNat ≤ stmtJumpTableBase + 4 * 1) ∧
  -- the body glue: eval_expr (EvalIH) ≫ env_define callee (the O-class oracle),
  -- ∀-closed over the entry `sailOutput` array `out0`.
  (∀ out0 : Array String,
    EvalIH st d env e st' v →
    Triple
      (fun c => ∃ ment v8 v9 v18 v19,
        ExecArmEntryK g N A SL φf φc st execArmVarDecl sp r aInterp aStmt aEnv aRet
          v8 v9 v18 v19 out0 m0 ment c)
      (fun c => ∃ subsret v1 v8 v9 v18 v19 mcall,
        SubExecReturn g N A SL φf φc st.store.frames.size st.store.closures.size
          ⟨st'.store.define env x v, st'.out⟩ v
          sp r aRet subsret (0x80004118#64) v1 v8 v9 v18 v19 m0 mcall c)) ∧
  -- the NON-identity-φ recursive widener (the sub-eval extended the maps AND `define`
  -- grew the frame binding list): the parametric `ExecRecWiden`.
  ExecRecWiden g N A SL φf φc st.store.frames.size st.store.closures.size
    ⟨st'.store.define env x v, st'.out⟩ .normal sp r aRet m0

/-- **`execVarDeclSimD`** — `ExecS.varInit` re-landed at `ExecExitD` (the `ExecIH`
shape).  Composes `execVarDeclSim`'s packaged `ExecExit` with the recursive widener
`execExitD_of_execExit_rec`, threading the `ExecVarInitGeom` bundle, and supplying the
entry `out0 := c.σ.sailOutput` by `rfl`.  Consumes the sub-`EvalIH` directly (passed
through by the row). -/
theorem execVarDeclSimD
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (x : String) (e : Expr) (v : Value)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (hSpec : ExecS st d env (.varDecl x (some e))
      ⟨st'.store.define env x v, st'.out⟩ .normal)
    (hIH : EvalIH st d env e st' v)
    (hG : ExecVarInitGeom g N A SL φf φc st st' d env x e v
      sp r aInterp aStmt aEnv aRet m0) :
    Triple
      (ExecEntry g N A SL φf φc st d env (.varDecl x (some e))
        sp r aInterp aStmt aEnv aRet m0)
      (ExecExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        ⟨st'.store.define env x v, st'.out⟩ .normal sp r aRet m0) := by
  intro c hEntry
  obtain ⟨hslot, htableStk, hGlue, hW⟩ := hG
  obtain ⟨c', hs, hExit⟩ :=
    execVarDeclSim g N A SL φf φc st st' d env x e v sp r aInterp aStmt aEnv aRet m0
      c.σ.sailOutput hSpec hIH hslot htableStk (hGlue c.σ.sailOutput) c ⟨hEntry, rfl⟩
  exact ⟨c', hs, execExitD_of_execExit_rec hExit hW⟩

end Vsa.Sim

/-! ## The `mExecS`-motive case row (the recursor-premise adapter)

`exec_varInit_row` marshals `execVarDeclSimD` into the exact minor-premise slot of
`execSeq_sim_of_cases`/`term_sim_of_cases` (`hSVarInit`).  As for the recursive
`expr`/`ret` rows (`rows/ExecRecRows.lean`), the premise is `ExecIH …` by definitional
unfolding (`mExecS = ExecIH`), and the sub-derivation IH the recursor hands the case
(`mEvalE st d env e st' v a`) is `EvalRecCommon.EvalIH st d env e st' v` by the SAME
unfolding (`mEvalE = EvalIH`), so it passes straight to `hIH` by `rfl` — no adapter.
The per-case `ExecVarInitGeom` bundle (∀-closed over the ghosts) carries the geometry +
glue (the `env_define` oracle) + widener. -/
namespace Vsa.Sim.Rows

open Vsa.Sim
open Vsa.Sim.TermSimAssembly

local notation "SpecSt" => Vsa.While.St

/-- The varInit-case residual: the `ExecVarInitGeom` bundle (carrying the body glue
with the `env_define` callee oracle), ∀-closed over the ghosts. -/
def VarInitResid (st st' : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr)
    (v : Value) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem),
    Vsa.Sim.ExecVarInitGeom g N A SL φf φc st st' d env x e v
      sp r aInterp aStmt aEnv aRet m0

/-- Route `hSVarInit` → `execVarDeclSimD`.  The sub-`EvalIH` (`mEvalE … a`) passes to
`hIH` by `rfl` (`mEvalE = EvalIH`).  Conditional on `VarInitResid` (which threads the
`env_define` callee oracle inside `hGlue`) — the `varInit` twin of `exec_expr_row`. -/
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
  intro g N A SL φf φc sp r aInterp aStmt aEnv aRet m0
  exact Vsa.Sim.execVarDeclSimD g N A SL φf φc st st' d env x e v
    sp r aInterp aStmt aEnv aRet m0 (ExecS.varInit st d env x e st' v a) hIH
    (hR st st' d env x e v g N A SL φf φc sp r aInterp aStmt aEnv aRet m0)

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

#print axioms Vsa.Sim.execVarDeclSimD
#print axioms Vsa.Sim.Rows.exec_varInit_row
#print axioms Vsa.Sim.Rows.exec_varInit_row_fills_hSVarInit
