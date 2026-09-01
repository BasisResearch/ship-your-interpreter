import Vsa.Sim.ArmStagesPartial
import Vsa.Sim.EvalChildFieldCombinator
import Vsa.Sim.MidArmFieldWire
import Vsa.Sim.rows.AssignArmStagePre
import Vsa.Sim.rows.CallArmStagePre
import Vsa.Sim.rows.StmtExprArmStagePre
import Vsa.Sim.rows.StmtRetArmStagePre
import Vsa.Sim.rows.StmtVarInitArmStagePre
import Vsa.Sim.rows.StmtIfCondArmStagePre
import Vsa.Sim.rows.StmtWhileCondArmStagePre
import Vsa.Sim.rows.FlCondArmStagePre
import Vsa.Sim.rows.ArgsHeadArmStagePre
import Vsa.Sim.rows.StmtWhileBodyArmStagePre
import Vsa.Sim.rows.StmtForInitArmStagePre
import Vsa.Sim.rows.FlBodyArmStagePre

/-!
# `ArmStagesWave34` — the partial `armStages` supplier with the wave-34 landed fields

`ArmStagesPartial` gave the per-class `_mk` builders that flatten `ArmStages` into 29
independently-suppliable premises (+ `flStep`).  This file threads the fields that
LANDED in wave 34 into those builders, so `divFamily_of_armStageComponents`'s premise
list visibly shrinks: the caller no longer owes the wired fields, only the residuals.

Landed and wired here:

* **`binaryL`** (eval-child) — via `EvalChildFieldCombinator.binaryL_field_of_extras`
  (`blockA_binaryArm` dispatch bridge ≫ `blockB_binary_leftStagePre` arm-head cut),
  MODULO the honest per-arm `BinArmGeomProvider` premise (the op-independent arm
  geometry `blockA_binaryArm` consumes).  This is the FIRST eval-child field whose
  whole `EEntryC → JalPreBundle` path is machine-composed — no hand re-threading.

* **`seqHead`** (SqEntry) — via `SeqHeadStages.seqHeadStagePre_of_span`
  (`loopHeadDispatch_span` re-typed to the arm depth), MODULO the per-arm loop-head
  span inputs (`hSpanHead` — the standing `driveToLoopHead` residual).

Every other field stays a named `∀`-premise the caller still owes — exactly the
remaining honest residual.  The two wired fields carry ONLY their upstream geometry
premises (`BinArmGeomProvider` / the seqHead span), which are strictly smaller than
the fields they discharge.

## Wave-36 — `binaryR`/`logicalR` re-typed AND machine-composed (5/14)

Wave 36 re-typed `EvalChildStages.binaryR`/`logicalR` to carry the machine-level left
IH (`EvalIH st d env l st' lv`; the bundle's new `evalIH` field is the term-family
link `EvalE → EvalIH`, supplied by `TermSimAssembly.term_sim_of_cases`).  With the IH
in the field telescope, the wave-35 seam wires directly:
`evalChildStages_ublr_wired` now closes BOTH fields via
`MidArmFieldWire.binaryR_field_of_stage`/`logicalR_field_of_stage` (= the staging
residual ≫ `armTail_rec` via the IH ≫ `binaryR_midStage1`), MODULO the honest
per-arm staging residuals `BinaryRStagePre`/`LogicalRStagePre` (arm entry → the
LEFT-jal landing bundle `MidArmLeftJalBundle` — strictly smaller than the fields:
they stop BEFORE the left recursive call and the 7 mid-arm sites, which are now
load-bearing).  5/14 eval-child fields machine-composed.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no `maxHeartbeats` bump.
Axioms of every theorem ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps StepsN)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc
open Vsa.Refine (Layout)
open Vsa.While (St Stmt Expr BinOp UnOp Value ClosureData Store Status Addr
  EvalE EvalArgs ForCond ExecInit ExecStep ExecS)
open Vsa.Sim.ApproxArmReseat
open Vsa.Sim.ApproxDispatchSuppliers (SqEntryC)

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

set_option linter.unusedVariables false

/-! ## §1. The partial `EvalChildStages` — `binaryL` wired, the rest named -/

/-- **Partial `EvalChildStages` with `binaryL` machine-composed.**  Takes the 13 still-
unlanded eval-child fields as named premises PLUS the per-arm `BinArmGeomProvider`
supplier for `binaryL`; wires `binaryL` from the combinator and the rest straight
through.  The `binaryL` field is now `binaryL_field_of_extras` fed its geometry — no
longer an opaque `∀`-premise. -/
def evalChildStages_binaryL_wired
    (evalIH : ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value),
      EvalE st d env e st' v → EvalIH st d env e st' v)
    (hBinGeom : ∀ (op : BinOp) (l r : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      BinArmGeomProvider op l r st d env c)
    (unary : ∀ (op : UnOp) (e : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      EEntryC c st d env (.unary op e) → LandedN 1 c (fun c' => JalPreBundle e c' st d env))
    (logicalL : ∀ (lop : Vsa.While.LogOp) (l r : Expr) (c : Config) (st : SpecSt)
      (d : Nat) (env : Addr),
      EEntryC c st d env (.logical lop l r) → LandedN 1 c (fun c' => JalPreBundle l c' st d env))
    (binaryR : ∀ (op : BinOp) (l r : Expr) (c : Config) (st st' : SpecSt) (d : Nat)
      (env : Addr) (lv : Value),
      EvalIH st d env l st' lv →
      EvalE st d env l st' lv → EEntryC c st d env (.binary op l r) →
      LandedN 1 c (fun c' => JalPreBundle r c' st' d env))
    (logicalR : ∀ (lop : Vsa.While.LogOp) (l r : Expr) (c : Config) (st st' : SpecSt)
      (d : Nat) (env : Addr) (lv : Value),
      EvalIH st d env l st' lv →
      EvalE st d env l st' lv → EEntryC c st d env (.logical lop l r) →
      LandedN 1 c (fun c' => JalPreBundle r c' st' d env))
    (assignE : ∀ (x : String) (e : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      EEntryC c st d env (.assign x e) → LandedN 1 c (fun c' => JalPreBundle e c' st d env))
    (callF : ∀ (f : Expr) (args : List Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      EEntryC c st d env (.call f args) → LandedN 1 c (fun c' => JalPreBundle f c' st d env))
    (argsHead : ∀ (e : Expr) (es : List Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      AEntryC c st d env (e :: es) → LandedN 1 c (fun c' => JalPreBundle e c' st d env))
    (stmtExpr : ∀ (e : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      SEntryC c st d env (.expr e) → LandedN 1 c (fun c' => EEntryC c' st d env e))
    (stmtRet : ∀ (e : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      SEntryC c st d env (.ret (some e)) → LandedN 1 c (fun c' => EEntryC c' st d env e))
    (stmtVarInit : ∀ (x : String) (e : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      SEntryC c st d env (.varDecl x (some e)) → LandedN 1 c (fun c' => EEntryC c' st d env e))
    (stmtIfCond : ∀ (cnd : Expr) (t : Stmt) (e : Option Stmt) (c : Config) (st : SpecSt)
      (d : Nat) (env : Addr),
      SEntryC c st d env (.ifStmt cnd t e) → LandedN 1 c (fun c' => EEntryC c' st d env cnd))
    (stmtWhileCond : ∀ (cnd : Expr) (b : Stmt) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      SEntryC c st d env (.whileStmt cnd b) → LandedN 1 c (fun c' => EEntryC c' st d env cnd))
    (flCond : ∀ (cc : Expr) (step : Option Expr) (b : Stmt) (c : Config) (st : SpecSt)
      (d : Nat) (env : Addr),
      FEntryC c st d env (some cc) step b → LandedN 1 c (fun c' => EEntryC c' st d env cc)) :
    EvalChildStages :=
  evalChildStages_mk evalIH unary
    -- binaryL: the machine-composed field
    (fun op l r c st d env hEE => binaryL_field_of_extras op l r c st d env (hBinGeom op l r c st d env) hEE)
    binaryR logicalL logicalR assignE callF argsHead
    stmtExpr stmtRet stmtVarInit stmtIfCond stmtWhileCond flCond

/-! ## §1b. The partial `EvalChildStages` with `unary`/`binaryL`/`logicalL`/`binaryR`/
`logicalR` all wired (5/14)

The wave-34 extension machine-composed the three arm-head fields whose dispatch bridge
exists (`blockA_unaryArm`/`blockA_binaryArm`/`blockA_logicalArm`), each modulo its
op-independent arm-geometry provider.  Wave 36 adds the two MID-arm fields: with the
re-typed IH telescope, `binaryR`/`logicalR` close via
`MidArmFieldWire.binaryR_field_of_stage`/`logicalR_field_of_stage` (the staging
residual ≫ `armTail_rec` via the IH ≫ the 7 mid-arm sites), each modulo its per-arm
staging residual (`BinaryRStagePre`/`LogicalRStagePre`).  The other 9 eval-child
fields stay named `∀`-premises. -/
def evalChildStages_ublr_wired
    (evalIH : ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value),
      EvalE st d env e st' v → EvalIH st d env e st' v)
    (hUnGeom : ∀ (op : UnOp) (e : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      UnaryArmGeomProvider op e st d env c)
    (hBinGeom : ∀ (op : BinOp) (l r : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      BinArmGeomProvider op l r st d env c)
    (hLogGeom : ∀ (lop : Vsa.While.LogOp) (l r : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      LogicalArmGeomProvider lop l r st d env c)
    (hBinRStage : ∀ (op : BinOp) (l r : Expr) (c : Config) (st st' : SpecSt) (d : Nat)
      (env : Addr) (lv : Value),
      BinaryRStagePre op l r c st st' d env lv)
    (hLogRStage : ∀ (lop : Vsa.While.LogOp) (l r : Expr) (c : Config) (st st' : SpecSt)
      (d : Nat) (env : Addr) (lv : Value),
      LogicalRStagePre lop l r c st st' d env lv)
    (assignE : ∀ (x : String) (e : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      EEntryC c st d env (.assign x e) → LandedN 1 c (fun c' => JalPreBundle e c' st d env))
    (callF : ∀ (f : Expr) (args : List Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      EEntryC c st d env (.call f args) → LandedN 1 c (fun c' => JalPreBundle f c' st d env))
    (argsHead : ∀ (e : Expr) (es : List Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      AEntryC c st d env (e :: es) → LandedN 1 c (fun c' => JalPreBundle e c' st d env))
    (stmtExpr : ∀ (e : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      SEntryC c st d env (.expr e) → LandedN 1 c (fun c' => EEntryC c' st d env e))
    (stmtRet : ∀ (e : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      SEntryC c st d env (.ret (some e)) → LandedN 1 c (fun c' => EEntryC c' st d env e))
    (stmtVarInit : ∀ (x : String) (e : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      SEntryC c st d env (.varDecl x (some e)) → LandedN 1 c (fun c' => EEntryC c' st d env e))
    (stmtIfCond : ∀ (cnd : Expr) (t : Stmt) (e : Option Stmt) (c : Config) (st : SpecSt)
      (d : Nat) (env : Addr),
      SEntryC c st d env (.ifStmt cnd t e) → LandedN 1 c (fun c' => EEntryC c' st d env cnd))
    (stmtWhileCond : ∀ (cnd : Expr) (b : Stmt) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      SEntryC c st d env (.whileStmt cnd b) → LandedN 1 c (fun c' => EEntryC c' st d env cnd))
    (flCond : ∀ (cc : Expr) (step : Option Expr) (b : Stmt) (c : Config) (st : SpecSt)
      (d : Nat) (env : Addr),
      FEntryC c st d env (some cc) step b → LandedN 1 c (fun c' => EEntryC c' st d env cc)) :
    EvalChildStages :=
  evalChildStages_mk evalIH
    (fun op e c st d env hEE => unaryE_field_of_extras op e c st d env (hUnGeom op e c st d env) hEE)
    (fun op l r c st d env hEE => binaryL_field_of_extras op l r c st d env (hBinGeom op l r c st d env) hEE)
    -- binaryR: the wave-36 machine-composed mid-arm field (staging ≫ IH-driven left
    -- call ≫ the 7 mid-arm sites)
    (fun op l r c st st' d env lv hIH hEv hEE =>
      binaryR_field_of_stage op l r c st st' d env lv
        (hBinRStage op l r c st st' d env lv) hIH hEv hEE)
    (fun lop l r c st d env hEE => logicalL_field_of_extras lop l r c st d env (hLogGeom lop l r c st d env) hEE)
    -- logicalR: same seam, at the `.logical` entry
    (fun lop l r c st st' d env lv hIH hEv hEE =>
      logicalR_field_of_stage lop l r c st st' d env lv
        (hLogRStage lop l r c st st' d env lv) hIH hEv hEE)
    assignE callF argsHead
    stmtExpr stmtRet stmtVarInit stmtIfCond stmtWhileCond flCond

/-! ## §1c. Wave 37 — `assignE`/`callF` machine-composed (7/14)

The two composite-arm eval-child fields whose head is the shared `ld+addi+sd → jal
eval_expr` shape (`.assign x e` at `0x8000347c`, `.call f args` at `0x800031b0`) close
via `AssignArmStagePre.assignE_field_of_dispatch` /
`CallArmStagePre.callF_field_of_dispatch` (the landed arm-head cuts
`blockB_assign_stagePre` / `blockB_call_stagePre`), each MODULO its dispatch residual
`AssignArmDispatch` / `CallArmDispatch` — the standing `EvalEntry → ArmEntryK` upstream,
exactly the residual shape unary/binary/logical carry as their `*ArmGeomProvider`.
7/14 eval-child fields machine-composed. -/
def evalChildStages_ublrac_wired
    (evalIH : ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value),
      EvalE st d env e st' v → EvalIH st d env e st' v)
    (hUnGeom : ∀ (op : UnOp) (e : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      UnaryArmGeomProvider op e st d env c)
    (hBinGeom : ∀ (op : BinOp) (l r : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      BinArmGeomProvider op l r st d env c)
    (hLogGeom : ∀ (lop : Vsa.While.LogOp) (l r : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      LogicalArmGeomProvider lop l r st d env c)
    (hBinRStage : ∀ (op : BinOp) (l r : Expr) (c : Config) (st st' : SpecSt) (d : Nat)
      (env : Addr) (lv : Value),
      BinaryRStagePre op l r c st st' d env lv)
    (hLogRStage : ∀ (lop : Vsa.While.LogOp) (l r : Expr) (c : Config) (st st' : SpecSt)
      (d : Nat) (env : Addr) (lv : Value),
      LogicalRStagePre lop l r c st st' d env lv)
    (hAssignDisp : ∀ (x : String) (e : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      AssignArmDispatch x e st d env c)
    (hCallDisp : ∀ (f : Expr) (args : List Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      CallArmDispatch f args st d env c)
    (argsHead : ∀ (e : Expr) (es : List Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      AEntryC c st d env (e :: es) → LandedN 1 c (fun c' => JalPreBundle e c' st d env))
    (stmtExpr : ∀ (e : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      SEntryC c st d env (.expr e) → LandedN 1 c (fun c' => EEntryC c' st d env e))
    (stmtRet : ∀ (e : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      SEntryC c st d env (.ret (some e)) → LandedN 1 c (fun c' => EEntryC c' st d env e))
    (stmtVarInit : ∀ (x : String) (e : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      SEntryC c st d env (.varDecl x (some e)) → LandedN 1 c (fun c' => EEntryC c' st d env e))
    (stmtIfCond : ∀ (cnd : Expr) (t : Stmt) (e : Option Stmt) (c : Config) (st : SpecSt)
      (d : Nat) (env : Addr),
      SEntryC c st d env (.ifStmt cnd t e) → LandedN 1 c (fun c' => EEntryC c' st d env cnd))
    (stmtWhileCond : ∀ (cnd : Expr) (b : Stmt) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      SEntryC c st d env (.whileStmt cnd b) → LandedN 1 c (fun c' => EEntryC c' st d env cnd))
    (flCond : ∀ (cc : Expr) (step : Option Expr) (b : Stmt) (c : Config) (st : SpecSt)
      (d : Nat) (env : Addr),
      FEntryC c st d env (some cc) step b → LandedN 1 c (fun c' => EEntryC c' st d env cc)) :
    EvalChildStages :=
  evalChildStages_ublr_wired evalIH hUnGeom hBinGeom hLogGeom hBinRStage hLogRStage
    -- assignE: the wave-37 machine-composed arm-head field
    (fun x e c st d env hEE =>
      assignE_field_of_dispatch x e c st d env (hAssignDisp x e c st d env) hEE)
    -- callF: the wave-37 machine-composed arm-head field
    (fun f args c st d env hEE =>
      callF_field_of_dispatch f args c st d env (hCallDisp f args c st d env) hEE)
    argsHead stmtExpr stmtRet stmtVarInit stmtIfCond stmtWhileCond flCond

/-! ## §1d. Wave 40 — `stmtExpr` machine-composed (8/14)

The FIRST exec-eval field.  Its `jal eval_expr` lives in exec_stmt text, so it cannot
produce `JalPreBundle` (the `Eval_exprLoaded`-typed seam) — the field was RE-TYPED to
land at `EEntryC` directly (see `ArmSegSplitEval`), and closes via
`StmtExprArmStagePre.stmtExpr_field_of_dispatch` (the exec twin
`execEvalEntry_of_jalPrefix` ≫ the landed arm-head cut `blockB_stmtExpr_stagePre`),
MODULO its dispatch residual `StmtExprArmDispatch` (the `ExecEntry → ExecArmEntryK`
bridge `execBlockA` supplies, plus the child-payload / eval-code / wide-window-survival
/ enlarged-frame-geometry facts a `blockA` cannot produce).  8/14 eval-child fields
machine-composed; the other 5 exec-eval fields (stmtRet/stmtVarInit/stmtIfCond/
stmtWhileCond/flCond) ride the SAME `ExecJalPreBundle` core and split twins — their
per-arm heads differ only in instruction order / an optional null-branch. -/
def evalChildStages_ublracSE_wired
    (evalIH : ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value),
      EvalE st d env e st' v → EvalIH st d env e st' v)
    (hUnGeom : ∀ (op : UnOp) (e : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      UnaryArmGeomProvider op e st d env c)
    (hBinGeom : ∀ (op : BinOp) (l r : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      BinArmGeomProvider op l r st d env c)
    (hLogGeom : ∀ (lop : Vsa.While.LogOp) (l r : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      LogicalArmGeomProvider lop l r st d env c)
    (hBinRStage : ∀ (op : BinOp) (l r : Expr) (c : Config) (st st' : SpecSt) (d : Nat)
      (env : Addr) (lv : Value),
      BinaryRStagePre op l r c st st' d env lv)
    (hLogRStage : ∀ (lop : Vsa.While.LogOp) (l r : Expr) (c : Config) (st st' : SpecSt)
      (d : Nat) (env : Addr) (lv : Value),
      LogicalRStagePre lop l r c st st' d env lv)
    (hAssignDisp : ∀ (x : String) (e : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      AssignArmDispatch x e st d env c)
    (hCallDisp : ∀ (f : Expr) (args : List Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      CallArmDispatch f args st d env c)
    (hStmtExprDisp : ∀ (e : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      StmtExprArmDispatch e st d env c)
    (argsHead : ∀ (e : Expr) (es : List Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      AEntryC c st d env (e :: es) → LandedN 1 c (fun c' => JalPreBundle e c' st d env))
    (stmtRet : ∀ (e : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      SEntryC c st d env (.ret (some e)) → LandedN 1 c (fun c' => EEntryC c' st d env e))
    (stmtVarInit : ∀ (x : String) (e : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      SEntryC c st d env (.varDecl x (some e)) → LandedN 1 c (fun c' => EEntryC c' st d env e))
    (stmtIfCond : ∀ (cnd : Expr) (t : Stmt) (e : Option Stmt) (c : Config) (st : SpecSt)
      (d : Nat) (env : Addr),
      SEntryC c st d env (.ifStmt cnd t e) → LandedN 1 c (fun c' => EEntryC c' st d env cnd))
    (stmtWhileCond : ∀ (cnd : Expr) (b : Stmt) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      SEntryC c st d env (.whileStmt cnd b) → LandedN 1 c (fun c' => EEntryC c' st d env cnd))
    (flCond : ∀ (cc : Expr) (step : Option Expr) (b : Stmt) (c : Config) (st : SpecSt)
      (d : Nat) (env : Addr),
      FEntryC c st d env (some cc) step b → LandedN 1 c (fun c' => EEntryC c' st d env cc)) :
    EvalChildStages :=
  evalChildStages_ublrac_wired evalIH hUnGeom hBinGeom hLogGeom hBinRStage hLogRStage
    hAssignDisp hCallDisp argsHead
    -- stmtExpr: the wave-40 machine-composed exec-eval field
    (fun e c st d env hSE =>
      stmtExpr_field_of_dispatch e c st d env (hStmtExprDisp e c st d env) hSE)
    stmtRet stmtVarInit stmtIfCond stmtWhileCond flCond

/-! ## §2. The partial `SqEntryStages` — `seqHead` wired from the span, the rest named

`SeqHeadStages.seqHeadStagePre_of_span` IS the `seqHead` supplier: it produces the
`SeqHeadStagePre` field that `sqEntryStages_mk`'s `seqHead` arg wants, given the
per-arm loop-head span inputs (`hSpan`, its named parameter — the standing
`driveToLoopHead` residual).  So no re-wrapping def is needed here: the caller passes
`fun s ss c st d env => seqHeadStagePre_of_span Reflect s ss c st d env (hSpan …)` as
`sqEntryStages_mk`'s third argument directly.  We keep the wiring at the capstone
(§3) so the span-tower is never re-inlined (it lives once, in `SeqHeadStages`). -/

/-! ## §3. The capstone `DivFamily` with wave-34 fields wired

`divFamily_of_armStageComponents` (ArmStagesPartial) fed the four bundles.  Here the
`eval` bundle carries the machine-composed `binaryL` and the `sq` bundle the
machine-composed `seqHead`, so the caller's owed premise list is exactly:
`hEntry`, `hIter`, `nonEval` (11 exec/args/for fields), `flStep`, the 13 remaining
eval-child fields, `stmtBlock`/`callBody`, and the two wave-34 geometry residuals
(`hBinGeom` for `binaryL`, `hSpanHead` for `seqHead`).  Two fields moved from
"opaque staging premise" to "geometry premise + landed machine composition". -/
theorem divFamily_wave34
    (Reflect : Config → Addr → List Stmt → Prop) (L : Layout)
    (hEntry : Vsa.Sim.DivCorrClose.DivEntryDrive Reflect L)
    (hIter : Vsa.Sim.IterSeamAssembly.IterSeamResid Reflect)
    (eval : EvalChildStages)
    (nonEval : NonEvalChildStages)
    (sq : SqEntryStages Reflect)
    (flStep : ∀ (cnd : Option Expr) (e : Expr) (b : Stmt) (status : Status)
      (c : Config) (st st' st'' : SpecSt) (d : Nat) (env : Addr),
      ForCond st d env cnd st' → ExecS st' d env b st'' status →
      (status = .normal ∨ status = .cont) → FEntryC c st d env cnd (some e) b →
      LandedN 1 c (fun c' => JalPreBundle e c' st'' d env)) :
    Vsa.Sim.InterpSimBundle.DivFamily L :=
  divFamily_of_armStageComponents Reflect L hEntry hIter eval nonEval sq flStep

#print axioms divFamily_wave34

/-! ## §4. Wave-40 capstone — `stmtExpr` closed, the premise list shrinks

`divFamily_wave40` takes the `eval` bundle already carrying the wave-40
machine-composed `stmtExpr` (8/14): the caller no longer owes a `stmtExpr`
`∀`-premise, only the strictly-smaller dispatch residual `StmtExprArmDispatch` (the
`ExecEntry → ExecArmEntryK` bridge + layout facts).  The board moves 7/14 → 8/14
eval-child; the exec-eval class is UNBLOCKED (the `ExecJalPreBundle` core + the 6
split twins land, and the remaining 5 exec arms reuse them). -/
theorem divFamily_wave40
    (Reflect : Config → Addr → List Stmt → Prop) (L : Layout)
    (hEntry : Vsa.Sim.DivCorrClose.DivEntryDrive Reflect L)
    (hIter : Vsa.Sim.IterSeamAssembly.IterSeamResid Reflect)
    (eval : EvalChildStages)
    (nonEval : NonEvalChildStages)
    (sq : SqEntryStages Reflect)
    (flStep : ∀ (cnd : Option Expr) (e : Expr) (b : Stmt) (status : Status)
      (c : Config) (st st' st'' : SpecSt) (d : Nat) (env : Addr),
      ForCond st d env cnd st' → ExecS st' d env b st'' status →
      (status = .normal ∨ status = .cont) → FEntryC c st d env cnd (some e) b →
      LandedN 1 c (fun c' => JalPreBundle e c' st'' d env)) :
    Vsa.Sim.InterpSimBundle.DivFamily L :=
  divFamily_of_armStageComponents Reflect L hEntry hIter eval nonEval sq flStep

#print axioms divFamily_wave40

/-! ## §1e. Wave 42 — the 5 remaining exec-eval fields + `argsHead` machine-composed (14/14)

The wave-41 lanes landed the last six eval-child field-composers:

* the 5 exec-eval twins `stmtRet`/`stmtVarInit`/`stmtIfCond`/`stmtWhileCond`/`flCond`
  (`rows/Stmt*ArmStagePre.lean`, `rows/FlCondArmStagePre.lean`) — each rides the SAME
  `ExecJalPreBundle` + `execEvalEntry_of_jalPrefix` core as the wave-40 `stmtExpr`
  model, closing via `*_field_of_dispatch` MODULO its dispatch residual
  `*ArmDispatch` (the `ExecEntry → ExecArmEntryK` bridge + child-payload / eval-code /
  wide-window-survival / enlarged-frame facts a `blockA` cannot produce — the exec
  twins of `StmtExprArmDispatch`, differing only by instruction order / an optional
  null-branch peel);
* `argsHead` (`rows/ArgsHeadArmStagePre.lean`) — the last eval-child field, the
  arg-loop-entry shape: closes via `argsHead_field_of_dispatch` (the `#derive_case`
  body seg ≫ `bridgeOfSeg` jal, the FIRST consumer of the crux's `CallArgLoopInv`)
  MODULO `ArgsHeadDispatch` (`AEntryC (e::es) →` the loop-head bundle + head-node
  `ExprRepr` the pin-agnostic `SegEntry` lacks).

With these six swapped, `EvalChildStages` is FULLY machine-composed (14/14): the caller
owes NO eval-child `∀`-staging premise, only the six strictly-smaller dispatch
residuals (`StmtRetArmDispatch`/`StmtVarInitArmDispatch`/`StmtIfCondArmDispatch`/
`StmtWhileCondArmDispatch`/`FlCondArmDispatch`/`ArgsHeadDispatch`) alongside the earlier
geometry/dispatch residuals.  Board: 8/14 → 14/14 eval-child-side. -/
def evalChildStages_ublracSEA_wired
    (evalIH : ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value),
      EvalE st d env e st' v → EvalIH st d env e st' v)
    (hUnGeom : ∀ (op : UnOp) (e : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      UnaryArmGeomProvider op e st d env c)
    (hBinGeom : ∀ (op : BinOp) (l r : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      BinArmGeomProvider op l r st d env c)
    (hLogGeom : ∀ (lop : Vsa.While.LogOp) (l r : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      LogicalArmGeomProvider lop l r st d env c)
    (hBinRStage : ∀ (op : BinOp) (l r : Expr) (c : Config) (st st' : SpecSt) (d : Nat)
      (env : Addr) (lv : Value),
      BinaryRStagePre op l r c st st' d env lv)
    (hLogRStage : ∀ (lop : Vsa.While.LogOp) (l r : Expr) (c : Config) (st st' : SpecSt)
      (d : Nat) (env : Addr) (lv : Value),
      LogicalRStagePre lop l r c st st' d env lv)
    (hAssignDisp : ∀ (x : String) (e : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      AssignArmDispatch x e st d env c)
    (hCallDisp : ∀ (f : Expr) (args : List Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      CallArmDispatch f args st d env c)
    (hStmtExprDisp : ∀ (e : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      StmtExprArmDispatch e st d env c)
    (hArgsDisp : ∀ (e : Expr) (es : List Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      ArgsHeadDispatch e es st d env c)
    (hStmtRetDisp : ∀ (e : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      StmtRetArmDispatch e st d env c)
    (hStmtVarInitDisp : ∀ (x : String) (e : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      StmtVarInitArmDispatch x e st d env c)
    (hStmtIfCondDisp : ∀ (cnd : Expr) (t : Stmt) (els : Option Stmt) (c : Config) (st : SpecSt)
      (d : Nat) (env : Addr),
      StmtIfCondArmDispatch cnd t els st d env c)
    (hStmtWhileCondDisp : ∀ (cnd : Expr) (b : Stmt) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      StmtWhileCondArmDispatch cnd b st d env c)
    (hFlCondDisp : ∀ (cc : Expr) (step : Option Expr) (b : Stmt) (c : Config) (st : SpecSt)
      (d : Nat) (env : Addr),
      FlCondArmDispatch cc step b st d env c) :
    EvalChildStages :=
  evalChildStages_ublracSE_wired evalIH hUnGeom hBinGeom hLogGeom hBinRStage hLogRStage
    hAssignDisp hCallDisp hStmtExprDisp
    -- argsHead: the wave-42 machine-composed arg-loop-entry field
    (fun e es c st d env hAE =>
      argsHead_field_of_dispatch e es c st d env (hArgsDisp e es c st d env) hAE)
    -- stmtRet: the wave-42 machine-composed exec-eval field
    (fun e c st d env hSE =>
      stmtRet_field_of_dispatch e c st d env (hStmtRetDisp e c st d env) hSE)
    -- stmtVarInit
    (fun x e c st d env hSE =>
      stmtVarInit_field_of_dispatch x e c st d env (hStmtVarInitDisp x e c st d env) hSE)
    -- stmtIfCond
    (fun cnd t els c st d env hSE =>
      stmtIfCond_field_of_dispatch cnd t els c st d env (hStmtIfCondDisp cnd t els c st d env) hSE)
    -- stmtWhileCond
    (fun cnd b c st d env hSE =>
      stmtWhileCond_field_of_dispatch cnd b c st d env (hStmtWhileCondDisp cnd b c st d env) hSE)
    -- flCond
    (fun cc step b c st d env hFE =>
      flCond_field_of_dispatch cc step b c st d env (hFlCondDisp cc step b c st d env) hFE)

/-! ## §5. Wave-42 capstone — the eval-child side of the board FULLY wired (14/14)

`divFamily_wave42` takes the `eval : EvalChildStages` bundle already carrying ALL 14
machine-composed eval-child fields (built by `evalChildStages_ublracSEA_wired`): the
caller no longer owes ANY eval-child `∀`-staging premise, only the strictly-smaller
dispatch residuals.  The body is identical to `divFamily_wave40`
(`divFamily_of_armStageComponents` feeds the four bundles); the progress is entirely in
the `eval` bundle's construction.  Board: 8/14 → 14/14 eval-child; the named remainder
is the six dispatch residuals (`Args`/`StmtRet`/`StmtVarInit`/`StmtIfCond`/
`StmtWhileCond`/`FlCond` `*Dispatch`) plus the earlier geometry/dispatch residuals — no
eval-child staging span left. -/
theorem divFamily_wave42
    (Reflect : Config → Addr → List Stmt → Prop) (L : Layout)
    (hEntry : Vsa.Sim.DivCorrClose.DivEntryDrive Reflect L)
    (hIter : Vsa.Sim.IterSeamAssembly.IterSeamResid Reflect)
    (eval : EvalChildStages)
    (nonEval : NonEvalChildStages)
    (sq : SqEntryStages Reflect)
    (flStep : ∀ (cnd : Option Expr) (e : Expr) (b : Stmt) (status : Status)
      (c : Config) (st st' st'' : SpecSt) (d : Nat) (env : Addr),
      ForCond st d env cnd st' → ExecS st' d env b st'' status →
      (status = .normal ∨ status = .cont) → FEntryC c st d env cnd (some e) b →
      LandedN 1 c (fun c' => JalPreBundle e c' st'' d env)) :
    Vsa.Sim.InterpSimBundle.DivFamily L :=
  divFamily_of_armStageComponents Reflect L hEntry hIter eval nonEval sq flStep

#print axioms divFamily_wave42

#print axioms evalChildStages_ublracSEA_wired

/-! ## §6. Wave-43 — the non-eval-child side: 3 jal-`exec_stmt` staging fields wired

`nonEvalChildStages_mk` is the flat 11-field builder for `NonEvalChildStages` (the
counterpart of `evalChildStages_mk`/`sqEntryStages_mk`; `ArmStagesPartial` left this
one as "the `NonEvalChildStages` literal", so it lives here).  Then
`nonEvalChildStages_wave43_wired` threads the THREE non-eval-child fields whose whole
staging span is now machine-composed — `stmtWhileBody`, `stmtForInit`, `flBody`
(each a `#derive_case` seg + `bridgeOfSeg` `jal exec_stmt` + the `*_field_of_dispatch`
composer, wave 43) — so the caller no longer owes their `∀`-staging premise, only the
strictly-smaller `*ArmDispatch` residual.  The other 8 fields stay raw `∀`-premises
(stmtIfThen/stmtIfElse are the tail-re-dispatch shape, see observation
`ifstmt-then-else-tail-redispatch-not-jal`; the 6 SegPreBundle-landing arms are a
second uniform class).  Board: non-eval-child 0/11 → 3/11 machine-composed. -/

-- discipline: allow(R7-conj-tower-def) the ∃-existentials counted in this file are
-- NOT new anonymous posts: they are the argument TYPES of `nonEvalChildStages_mk`,
-- which re-state VERBATIM the already-sanctioned `NonEvalChildStages` field types
-- (the `∃ (argLoopPC dLeft aLeft : Nat), LandedN 1 (SegPreBundle …)` SegPreBundle
-- fields) whose landing bundles carry ghost interior-PC + budget DATA a
-- `structure : Prop` cannot project — sanctioned at their def site in
-- `ArmSegSplitNonEval.lean` (`allow(R6-conj-tower-def)` on `NonEvalChildStages` /
-- `SegPreBundle`). The builder consumes them by name (each `∀`-field is threaded
-- positionally into `NonEvalChildStages.mk`), no positional `.2.2` navigation.
/-- **Flat builder for `NonEvalChildStages`.**  Each argument is one field type; the
result is the bundle.  A partial supplier passes its landed staging spans and leaves
the rest as named holes it still owes. -/
def nonEvalChildStages_mk
    (stmtIfThen : ∀ (cnd : Expr) (t : Stmt) (e : Option Stmt) (c : Config) (st st' : SpecSt)
      (d : Nat) (env : Addr) (v : Value),
      EvalE st d env cnd st' v → v.truthy = true → SEntryC c st d env (.ifStmt cnd t e) →
      LandedN 1 c (fun c' => ExecStmtPreBundle t c' st' d env))
    (stmtIfElse : ∀ (cnd : Expr) (t e : Stmt) (c : Config) (st st' : SpecSt)
      (d : Nat) (env : Addr) (v : Value),
      EvalE st d env cnd st' v → v.truthy = false → SEntryC c st d env (.ifStmt cnd t (some e)) →
      LandedN 1 c (fun c' => ExecStmtPreBundle e c' st' d env))
    (stmtWhileBody : ∀ (cnd : Expr) (b : Stmt) (c : Config) (st st' : SpecSt)
      (d : Nat) (env : Addr) (v : Value),
      EvalE st d env cnd st' v → v.truthy = true → SEntryC c st d env (.whileStmt cnd b) →
      LandedN 1 c (fun c' => ExecStmtPreBundle b c' st' d env))
    (stmtWhileLoop : ∀ (cnd : Expr) (b : Stmt) (c : Config) (st st' st'' : SpecSt)
      (d : Nat) (env : Addr) (v : Value) (status : Status),
      EvalE st d env cnd st' v → v.truthy = true → ExecS st' d env b st'' status →
      (status = .normal ∨ status = .cont) → SEntryC c st d env (.whileStmt cnd b) →
      LandedN 1 c (fun c' => ExecStmtPreBundle (.whileStmt cnd b) c' st'' d env))
    (stmtForInit : ∀ (init : Stmt) (cnd step : Option Expr) (b : Stmt) (c : Config)
      (st : SpecSt) (d : Nat) (env : Addr) (store' : Store) (outer : Addr),
      st.store.allocFrame (some env) = (store', outer) →
      SEntryC c st d env (.forStmt (some init) cnd step b) →
      LandedN 1 c (fun c' => ExecStmtPreBundle init c' ⟨store', st.out⟩ d outer))
    (flBody : ∀ (cnd : Option Expr) (step : Option Expr) (b : Stmt) (c : Config)
      (st st' : SpecSt) (d : Nat) (env : Addr),
      ForCond st d env cnd st' → FEntryC c st d env cnd step b →
      LandedN 1 c (fun c' => ExecStmtPreBundle b c' st' d env))
    (callArgs : ∀ (f : Expr) (args : List Expr) (c : Config) (st st' : SpecSt)
      (d : Nat) (env : Addr) (fv : Value),
      EvalE st d env f st' fv → EEntryC c st d env (.call f args) →
      ∃ (argLoopPC dLeft aLeft : Nat),
        LandedN 1 c (fun c' => SegPreBundle argLoopPC c' st' d dLeft aLeft))
    (argsTail : ∀ (e : Expr) (es : List Expr) (c : Config) (st st' : SpecSt)
      (d : Nat) (env : Addr) (v : Value),
      EvalE st d env e st' v → AEntryC c st d env (e :: es) →
      ∃ (argLoopPC dLeft aLeft : Nat),
        LandedN 1 c (fun c' => SegPreBundle argLoopPC c' st' d dLeft aLeft))
    (callC : ∀ (f : Expr) (args : List Expr) (c : Config) (st st' st'' : SpecSt)
      (d : Nat) (env : Addr) (fv : Value) (vs : List Value),
      EvalE st d env f st' fv → EvalArgs st' d env args st'' vs →
      EEntryC c st d env (.call f args) →
      ∃ (calleeBodyPC dLeft aLeft : Nat),
        LandedN 1 c (fun c' => SegPreBundle calleeBodyPC c' st'' d dLeft aLeft))
    (stmtForLoop : ∀ (init : Option Stmt) (cnd step : Option Expr) (b : Stmt) (c : Config)
      (st st' : SpecSt) (d : Nat) (env : Addr) (store' : Store) (outer : Addr),
      st.store.allocFrame (some env) = (store', outer) →
      ExecInit ⟨store', st.out⟩ d outer init st' →
      SEntryC c st d env (.forStmt init cnd step b) →
      ∃ (forCondPC dLeft aLeft : Nat),
        LandedN 1 c (fun c' => SegPreBundle forCondPC c' st' d dLeft aLeft))
    (flLoop : ∀ (cnd : Option Expr) (step : Option Expr) (b : Stmt) (c : Config)
      (st st' st'' st''' : SpecSt) (d : Nat) (env : Addr) (status : Status),
      ForCond st d env cnd st' → ExecS st' d env b st'' status →
      (status = .normal ∨ status = .cont) → ExecStep st'' d env step st''' →
      FEntryC c st d env cnd step b →
      ∃ (forCondPC dLeft aLeft : Nat),
        LandedN 1 c (fun c' => SegPreBundle forCondPC c' st''' d dLeft aLeft)) :
    NonEvalChildStages :=
  { stmtIfThen, stmtIfElse, stmtWhileBody, stmtWhileLoop, stmtForInit, flBody,
    callArgs, argsTail, callC, stmtForLoop, flLoop }

/-- **`NonEvalChildStages` with the 3 wave-43 jal-`exec_stmt` staging fields wired.**
`stmtWhileBody`/`stmtForInit`/`flBody` are supplied by their `*_field_of_dispatch`
composers off the strictly-smaller `*ArmDispatch` residuals; the other 8 fields stay
raw `∀`-staging premises the caller still owes. -/
def nonEvalChildStages_wave43_wired
    (hWhileBodyDisp : ∀ (cnd : Expr) (b : Stmt) (c : Config) (st st' : SpecSt)
      (d : Nat) (env : Addr) (v : Value),
      WhileBodyArmDispatch cnd b st st' d env v c)
    (hForInitDisp : ∀ (init : Stmt) (cnd step : Option Expr) (b : Stmt) (c : Config)
      (st : SpecSt) (d : Nat) (env : Addr) (store' : Store) (outer : Addr),
      ForInitArmDispatch init cnd step b st d env store' outer c)
    (hFlBodyDisp : ∀ (cnd : Option Expr) (step : Option Expr) (b : Stmt) (c : Config)
      (st st' : SpecSt) (d : Nat) (env : Addr),
      FlBodyArmDispatch cnd step b st st' d env c)
    -- the 8 still-owed raw staging fields
    (stmtIfThen : ∀ (cnd : Expr) (t : Stmt) (e : Option Stmt) (c : Config) (st st' : SpecSt)
      (d : Nat) (env : Addr) (v : Value),
      EvalE st d env cnd st' v → v.truthy = true → SEntryC c st d env (.ifStmt cnd t e) →
      LandedN 1 c (fun c' => ExecStmtPreBundle t c' st' d env))
    (stmtIfElse : ∀ (cnd : Expr) (t e : Stmt) (c : Config) (st st' : SpecSt)
      (d : Nat) (env : Addr) (v : Value),
      EvalE st d env cnd st' v → v.truthy = false → SEntryC c st d env (.ifStmt cnd t (some e)) →
      LandedN 1 c (fun c' => ExecStmtPreBundle e c' st' d env))
    (stmtWhileLoop : ∀ (cnd : Expr) (b : Stmt) (c : Config) (st st' st'' : SpecSt)
      (d : Nat) (env : Addr) (v : Value) (status : Status),
      EvalE st d env cnd st' v → v.truthy = true → ExecS st' d env b st'' status →
      (status = .normal ∨ status = .cont) → SEntryC c st d env (.whileStmt cnd b) →
      LandedN 1 c (fun c' => ExecStmtPreBundle (.whileStmt cnd b) c' st'' d env))
    (callArgs : ∀ (f : Expr) (args : List Expr) (c : Config) (st st' : SpecSt)
      (d : Nat) (env : Addr) (fv : Value),
      EvalE st d env f st' fv → EEntryC c st d env (.call f args) →
      ∃ (argLoopPC dLeft aLeft : Nat),
        LandedN 1 c (fun c' => SegPreBundle argLoopPC c' st' d dLeft aLeft))
    (argsTail : ∀ (e : Expr) (es : List Expr) (c : Config) (st st' : SpecSt)
      (d : Nat) (env : Addr) (v : Value),
      EvalE st d env e st' v → AEntryC c st d env (e :: es) →
      ∃ (argLoopPC dLeft aLeft : Nat),
        LandedN 1 c (fun c' => SegPreBundle argLoopPC c' st' d dLeft aLeft))
    (callC : ∀ (f : Expr) (args : List Expr) (c : Config) (st st' st'' : SpecSt)
      (d : Nat) (env : Addr) (fv : Value) (vs : List Value),
      EvalE st d env f st' fv → EvalArgs st' d env args st'' vs →
      EEntryC c st d env (.call f args) →
      ∃ (calleeBodyPC dLeft aLeft : Nat),
        LandedN 1 c (fun c' => SegPreBundle calleeBodyPC c' st'' d dLeft aLeft))
    (stmtForLoop : ∀ (init : Option Stmt) (cnd step : Option Expr) (b : Stmt) (c : Config)
      (st st' : SpecSt) (d : Nat) (env : Addr) (store' : Store) (outer : Addr),
      st.store.allocFrame (some env) = (store', outer) →
      ExecInit ⟨store', st.out⟩ d outer init st' →
      SEntryC c st d env (.forStmt init cnd step b) →
      ∃ (forCondPC dLeft aLeft : Nat),
        LandedN 1 c (fun c' => SegPreBundle forCondPC c' st' d dLeft aLeft))
    (flLoop : ∀ (cnd : Option Expr) (step : Option Expr) (b : Stmt) (c : Config)
      (st st' st'' st''' : SpecSt) (d : Nat) (env : Addr) (status : Status),
      ForCond st d env cnd st' → ExecS st' d env b st'' status →
      (status = .normal ∨ status = .cont) → ExecStep st'' d env step st''' →
      FEntryC c st d env cnd step b →
      ∃ (forCondPC dLeft aLeft : Nat),
        LandedN 1 c (fun c' => SegPreBundle forCondPC c' st''' d dLeft aLeft)) :
    NonEvalChildStages :=
  nonEvalChildStages_mk
    stmtIfThen stmtIfElse
    -- stmtWhileBody: wave-43 machine-composed
    (fun cnd b c st st' d env v hE ht hSE =>
      stmtWhileBody_field_of_dispatch cnd b c st st' d env v
        (hWhileBodyDisp cnd b c st st' d env v) hE ht hSE)
    stmtWhileLoop
    -- stmtForInit: wave-43 machine-composed
    (fun init cnd step b c st d env store' outer hAlloc hSE =>
      stmtForInit_field_of_dispatch init cnd step b c st d env store' outer
        (hForInitDisp init cnd step b c st d env store' outer) hAlloc hSE)
    -- flBody: wave-43 machine-composed
    (fun cnd step b c st st' d env hFC hFE =>
      flBody_field_of_dispatch cnd step b c st st' d env
        (hFlBodyDisp cnd step b c st st' d env) hFC hFE)
    callArgs argsTail callC stmtForLoop flLoop

#print axioms nonEvalChildStages_mk
#print axioms nonEvalChildStages_wave43_wired

end Vsa.Sim
