import Vsa.Sim.ExecIf
import Vsa.Sim.ExecDispatch

/-!
# Layer 4 — M4 `ifStmt` re-dispatch cases: `ExecS.ifTrue` and `ExecS.ifFalse`

These are the FIRST consumers of the re-dispatch induction hypothesis
(`ExecDispatchIH`, `ExecDispatch.lean`). `if` executes its `then`/`else` branch by
**re-dispatch**: it sets `s0 := stmt->then` (`ifTrue`) or `s0 := stmt->else`
(`ifFalse`) and `j 0x80004014` — the dispatch point *after* the `exec_stmt`
prologue — running the branch statement in the SAME `exec_stmt` frame (no `jal`, no
second prologue). The branch's own arm + epilogue + `ret` run in-frame; the
epilogue restores the OUTER (`if`) call's saved registers and returns to ITS caller
(sound because the frame is shared). So the branch's ordinary `ExecIH`
(`ExecEntry` @ `0x80003fe0`, from the FULL entry including the prologue) does NOT
apply — the branch re-enters at `0x80004014`, POST-prologue. The `ExecDispatchIH`
is exactly the body-from-dispatch shape: `Triple (ExecDispatchReady … s' …)
(ExecExitD … status …)`, consumed directly here.

## The `ifStmt` arm (kind 3, `0x800041e8`) — the re-dispatch paths

```
800041e8:  ld   a2,8(s0)       -- a2 := stmt->cond
800041ec:  mv   a3,s3          -- a3 := env
800041f0:  mv   a1,s1          -- a1 := interp*
800041f4:  addi a0,sp,56       -- cond eval sret buffer
800041f8:  jal  eval_expr      -- link 0x800041fc; the cond sub-derivation (EvalIH)
800041fc:  ld   a2,56(sp)      -- reload the 24-byte cond result …
80004200:  ld   a3,64(sp)
80004204:  ld   a5,72(sp)
80004208:  addi a0,sp,16       -- value_truthy arg buffer
8000420c:  sd   a2,16(sp)      -- copy result into it
80004210:  sd   a3,24(sp)
80004214:  sd   a5,32(sp)
80004218:  jal  value_truthy   -- link 0x8000421c; a0 := (v.truthy ? 1 : 0)
8000421c:  li   a6,8           -- (dispatch-bound reload)
80004220:  auipc a4,0x16       -- table base …
80004224:  addi a4,a4,-616     -- a4 := 0x80019fb8
80004228:  beqz a0,0x800042cc  -- v.truthy == 0 (FALSY) → 0x800042cc (else-check)
                               -- NOT taken (TRUTHY) = ifTrue:
8000422c:  ld   s0,16(s0)      -- s0 := stmt->then  (offset 16)
80004230:  j    0x80004014     -- re-dispatch: run `then` in-frame
    -- taken (FALSY) → 0x800042cc:
800042cc:  ld   s0,24(s0)      -- s0 := stmt->else  (offset 24)
800042d0:  bnez s0,0x80004014  -- else present → re-dispatch (= ifFalse); absent = ifNone
```

## Structure

`execIfTrueSim` = `execBlockA (kind 3, arm 0x800041e8)` ≫ **`hGlue`** (cond eval +
`value_truthy` truthy + `ld s0,16(s0)` + `j 0x80004014`, reaching
`ExecDispatchReady` for the `then` branch `t` in state `st'`) ≫ **consume the
branch `ExecDispatchIH st' d env t st'' status`** → `ExecExitD … st'' status`,
whose `ExecExit` component is the goal (rebasing the exit maps `φfE/φcE` to the
entry maps `φf/φc` via `PhiExtends.trans`). NO second prologue, NO `execBlockD` —
the branch's own arm runs its epilogue + `ret`. `execIfFalseSim` is symmetric with
`ld s0,24(s0)` + `bnez` taken, and the `else` branch `e`.

The cond-eval + `value_truthy` machine path (`0x800041e8 → 0x80004014` with
`s0 := then/else`) plus the extended-map cond-eval facts are delivered as the named
glue residual `hGlue` (the statement-frame analog of `execIfNoneSim`'s `hGlue`, only
landing at `ExecDispatchReady` instead of the `.normal` epilogue). The truthy/falsy
hypothesis is the genuine `ifTrue`/`ifFalse`-spec premise, folded into `hGlue`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
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

/-! ## `ExecIfTrueSimGoal` — the `ExecS.ifTrue` simulation Triple (packaged) -/
def ExecIfTrueSimGoal
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st'' : Vsa.While.St) (d : Nat) (env : Addr) (c : Expr) (t : Stmt)
    (e : Option Stmt) (status : Status)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) (out0 : Array String) : Prop :=
  Triple
    (fun cfg => ExecEntry g N A SL φf φc st d env (.ifStmt c t e) sp r aInterp aStmt aEnv aRet m0 cfg
      ∧ cfg.σ.sailOutput = out0)
    (ExecExit g N A SL φf φc st'' status sp r aRet m0)

/-! ## `execIfTrueSim` — `ExecS.ifTrue`: `execBlockA ≫ (cond-eval + truthy + re-dispatch) ≫ ExecDispatchIH`

The head (`execBlockA`, prologue+dispatch to the `ifStmt` arm `0x800041e8`) is
threaded UNCONDITIONALLY. The arm-body glue `hGlue` consumes the condition
`EvalIH`, evaluates `value_truthy` (result nonzero, `v.truthy = true`), takes the
NOT-taken (truthy) branch, sets `s0 := stmt->then`, and `j 0x80004014`, reaching
`ExecDispatchReady` for the `then` branch `t` in the cond's output state `st'`.
Consuming the branch `ExecDispatchIH st' d env t st'' status` yields `ExecExitD …`
directly; its `ExecExit` component (rebased to the entry maps) is the goal. -/
theorem execIfTrueSim
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (d : Nat) (env : Addr) (c : Expr) (t : Stmt)
    (e : Option Stmt) (status : Status) (v : Value)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) (out0 : Array String)
    (_hSpec : ExecS st d env (.ifStmt c t e) st'' status)
    (hIH : EvalIH st d env c st' v)
    (_htruthy : v.truthy = true)
    -- the branch induction hypothesis (supplied by the mutual recursor):
    (hBranchIH : ExecDispatchIH st' d env t st'' status)
    -- execBlockA residuals (as for brk/cont/expr/ifNone):
    (hslot : StmtSlotPinned 3 execArmIf m0)
    (htableStk : stmtJumpTableBase + 4 * 3 + 4 ≤ SL.lo ∨ sp.toNat ≤ stmtJumpTableBase + 4 * 3)
    -- the frame-alloc φ-accounting residual: given the branch-run maps `φfE/φcE`
    -- (which `hGlue` proves extend the entry maps `φf/φc` over the cond-output store
    -- `st'`), the branch's exit `ExecExit` (store/retval stated at `φfE/φcE`) re-bases
    -- to the entry maps `φf/φc` at the FINAL store size `st''`. This is the
    -- `block`-case `hphi` analog — allocFrame/closure accounting the sub-run's growing
    -- store forces (`φf → φfE → φf''` at differing sizes); RESIDUAL.
    (hmaps : ∀ (φfE φcE : Addr → Nat) (cD : Config),
      PhiExtends φf φfE st'.store.frames.size →
      PhiExtends φc φcE st'.store.closures.size →
      ExecExit g N A SL φfE φcE st'' status sp r aRet m0 cD →
      ExecExit g N A SL φf φc st'' status sp r aRet m0 cD)
    -- the arm-body glue: from the arm-entry state at `0x800041e8`, the cond setup +
    -- `jal eval_expr` + the sub-call (the `EvalIH`) + the reload/copy + `value_truthy`
    -- (result nonzero, `v.truthy = true`) + the TRUTHY branch (`beqz a0` NOT taken) +
    -- `ld s0,16(s0)` (`s0 := stmt->then` = `aThen`) + `j 0x80004014` reach the
    -- re-dispatch entry `ExecDispatchReady` for the `then` branch `t` in state `st'`.
    -- The re-dispatch target `aThen`, the extended maps for `st'.store`, the spill
    -- witnesses, and the post-cond memory `ment` are chosen inside. `φfE/φcE` extend
    -- the entry maps (`PhiExtends`); the IH is ∀-closed over maps so it consumes them.
    -- RESIDUAL.
    (hGlue : EvalIH st d env c st' v →
      Triple
        (fun cfg => ∃ ment v8 v9 v18 v19,
          ExecArmEntryK g N A SL φf φc st execArmIf sp r aInterp aStmt aEnv aRet
            v8 v9 v18 v19 out0 m0 ment cfg)
        (fun cfg => ∃ (φfE φcE : Addr → Nat) (aThen : BitVec 64)
            (ment : Mem) (v8 v9 v18 v19 : BitVec 64),
          PhiExtends φf φfE st'.store.frames.size ∧
          PhiExtends φc φcE st'.store.closures.size ∧
          ExecDispatchReady g N A SL φfE φcE st' t sp r aInterp aThen aEnv aRet
            v8 v9 v18 v19 out0 m0 ment cfg)) :
    ExecIfTrueSimGoal g N A SL φf φc st st'' d env c t e status
      sp r aInterp aStmt aEnv aRet m0 out0 := by
  intro cfg hpre
  obtain ⟨he, hout0⟩ := hpre
  -- kind read `read32 m0 aStmt = 3` from the `.ifStmt` StmtRepr (either arm)
  have hkind : read32 m0 aStmt.toNat = some 3 := by
    have := he.stmt; rw [he.mem] at this; cases this with
    | ifElse h0 _ _ _ _ _ _ _ => exact h0
    | ifNoElse h0 _ _ _ _ _ => exact h0
  -- ===== head: execBlockA (prologue + dispatch → arm entry 0x800041e8) =====
  have hBlockA : ExecBlockAGoal g N A SL φf φc st d env (.ifStmt c t e)
      sp r aInterp aStmt aEnv aRet execArmIf m0 out0 :=
    execBlockA g N A SL φf φc st d env (.ifStmt c t e) 3 execArmIf
      sp r aInterp aStmt aEnv aRet m0 out0
      (by omega) (by omega) hkind hslot (by decide) ⟨htableStk⟩
  obtain ⟨cA, hstepsA, hArmExists⟩ := hBlockA cfg ⟨he, hout0⟩
  -- ===== glue: cond eval + value_truthy (truthy) + ld s0,16(s0) + j → ExecDispatchReady =====
  obtain ⟨cG, hstepsG, hGlueOut⟩ := hGlue hIH cA hArmExists
  obtain ⟨φfE, φcE, aThen, ment, v8, v9, v18, v19, hpfE, hpcE, hReady⟩ := hGlueOut
  -- ===== consume the branch ExecDispatchIH → ExecExitD (then-branch runs in-frame) =====
  obtain ⟨cD, hstepsD, hExitD⟩ :=
    hBranchIH g N A SL φfE φcE sp r aInterp aThen aEnv aRet v8 v9 v18 v19 out0 m0 ment cG hReady
  -- The branch's `ExecExitD` yields the goal `ExecExit` VERBATIM (same `m0` frame
  -- baseline, same `sp r aRet`, same `st''`/`status`) except its `store`/`retval`
  -- clauses are stated at the branch-run maps `φfE/φcE`, re-based to `φf/φc` by `hmaps`.
  exact ⟨cD, hstepsA.trans (hstepsG.trans hstepsD), hmaps φfE φcE cD hpfE hpcE hExitD.1⟩

/-! ## `ExecIfFalseSimGoal` — the `ExecS.ifFalse` simulation Triple (packaged) -/
def ExecIfFalseSimGoal
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st'' : Vsa.While.St) (d : Nat) (env : Addr) (c : Expr) (t e : Stmt)
    (status : Status)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) (out0 : Array String) : Prop :=
  Triple
    (fun cfg => ExecEntry g N A SL φf φc st d env (.ifStmt c t (some e)) sp r aInterp aStmt aEnv aRet m0 cfg
      ∧ cfg.σ.sailOutput = out0)
    (ExecExit g N A SL φf φc st'' status sp r aRet m0)

/-! ## `execIfFalseSim` — `ExecS.ifFalse`: symmetric to `execIfTrueSim`

The condition evaluates FALSY (`v.truthy = false`), the `beqz a0` is TAKEN to
`0x800042cc`, `ld s0,24(s0)` sets `s0 := stmt->else` (`= aElse`, nonzero since the
`else` is present), and `bnez s0` is TAKEN, `j`-ing to the re-dispatch entry
`0x80004014` for the `else` branch `e` in state `st'`. Consuming the branch
`ExecDispatchIH st' d env e st'' status` yields `ExecExitD …`; its `ExecExit`
component (rebased to the entry maps) is the goal. -/
theorem execIfFalseSim
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (d : Nat) (env : Addr) (c : Expr) (t e : Stmt)
    (status : Status) (v : Value)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) (out0 : Array String)
    (_hSpec : ExecS st d env (.ifStmt c t (some e)) st'' status)
    (hIH : EvalIH st d env c st' v)
    (_hfalsy : v.truthy = false)
    -- the branch induction hypothesis (supplied by the mutual recursor):
    (hBranchIH : ExecDispatchIH st' d env e st'' status)
    -- execBlockA residuals:
    (hslot : StmtSlotPinned 3 execArmIf m0)
    (htableStk : stmtJumpTableBase + 4 * 3 + 4 ≤ SL.lo ∨ sp.toNat ≤ stmtJumpTableBase + 4 * 3)
    -- the frame-alloc φ-accounting residual (as `execIfTrueSim`'s `hmaps`):
    (hmaps : ∀ (φfE φcE : Addr → Nat) (cD : Config),
      PhiExtends φf φfE st'.store.frames.size →
      PhiExtends φc φcE st'.store.closures.size →
      ExecExit g N A SL φfE φcE st'' status sp r aRet m0 cD →
      ExecExit g N A SL φf φc st'' status sp r aRet m0 cD)
    -- the arm-body glue, symmetric to `execIfTrueSim`: cond eval + `value_truthy`
    -- (result zero, `v.truthy = false`) + the FALSY branch (`beqz a0` taken to
    -- `0x800042cc`) + `ld s0,24(s0)` (`s0 := stmt->else` = `aElse`) + `bnez s0`
    -- TAKEN (else present) reach the re-dispatch entry `ExecDispatchReady` for the
    -- `else` branch `e` in state `st'`. RESIDUAL.
    (hGlue : EvalIH st d env c st' v →
      Triple
        (fun cfg => ∃ ment v8 v9 v18 v19,
          ExecArmEntryK g N A SL φf φc st execArmIf sp r aInterp aStmt aEnv aRet
            v8 v9 v18 v19 out0 m0 ment cfg)
        (fun cfg => ∃ (φfE φcE : Addr → Nat) (aElse : BitVec 64)
            (ment : Mem) (v8 v9 v18 v19 : BitVec 64),
          PhiExtends φf φfE st'.store.frames.size ∧
          PhiExtends φc φcE st'.store.closures.size ∧
          ExecDispatchReady g N A SL φfE φcE st' e sp r aInterp aElse aEnv aRet
            v8 v9 v18 v19 out0 m0 ment cfg)) :
    ExecIfFalseSimGoal g N A SL φf φc st st'' d env c t e status
      sp r aInterp aStmt aEnv aRet m0 out0 := by
  intro cfg hpre
  obtain ⟨he, hout0⟩ := hpre
  have hkind : read32 m0 aStmt.toNat = some 3 := by
    have := he.stmt; rw [he.mem] at this; cases this with
    | ifElse h0 _ _ _ _ _ _ _ => exact h0
  -- ===== head: execBlockA (prologue + dispatch → arm entry 0x800041e8) =====
  have hBlockA : ExecBlockAGoal g N A SL φf φc st d env (.ifStmt c t (some e))
      sp r aInterp aStmt aEnv aRet execArmIf m0 out0 :=
    execBlockA g N A SL φf φc st d env (.ifStmt c t (some e)) 3 execArmIf
      sp r aInterp aStmt aEnv aRet m0 out0
      (by omega) (by omega) hkind hslot (by decide) ⟨htableStk⟩
  obtain ⟨cA, hstepsA, hArmExists⟩ := hBlockA cfg ⟨he, hout0⟩
  -- ===== glue: cond eval + value_truthy (falsy) + ld s0,24(s0) + bnez → ExecDispatchReady =====
  obtain ⟨cG, hstepsG, hGlueOut⟩ := hGlue hIH cA hArmExists
  obtain ⟨φfE, φcE, aElse, ment, v8, v9, v18, v19, hpfE, hpcE, hReady⟩ := hGlueOut
  -- ===== consume the branch ExecDispatchIH → ExecExitD (else-branch runs in-frame) =====
  obtain ⟨cD, hstepsD, hExitD⟩ :=
    hBranchIH g N A SL φfE φcE sp r aInterp aElse aEnv aRet v8 v9 v18 v19 out0 m0 ment cG hReady
  exact ⟨cD, hstepsA.trans (hstepsG.trans hstepsD), hmaps φfE φcE cD hpfE hpcE hExitD.1⟩

end Vsa.Sim
