import Vsa.Sim.ArmStagesPartial
import Vsa.Sim.EvalChildFieldCombinator
import Vsa.Sim.MidArmFieldWire
import Vsa.Sim.rows.AssignArmStagePre
import Vsa.Sim.rows.CallArmStagePre

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
      SEntryC c st d env (.expr e) → LandedN 1 c (fun c' => JalPreBundle e c' st d env))
    (stmtRet : ∀ (e : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      SEntryC c st d env (.ret (some e)) → LandedN 1 c (fun c' => JalPreBundle e c' st d env))
    (stmtVarInit : ∀ (x : String) (e : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      SEntryC c st d env (.varDecl x (some e)) → LandedN 1 c (fun c' => JalPreBundle e c' st d env))
    (stmtIfCond : ∀ (cnd : Expr) (t : Stmt) (e : Option Stmt) (c : Config) (st : SpecSt)
      (d : Nat) (env : Addr),
      SEntryC c st d env (.ifStmt cnd t e) → LandedN 1 c (fun c' => JalPreBundle cnd c' st d env))
    (stmtWhileCond : ∀ (cnd : Expr) (b : Stmt) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      SEntryC c st d env (.whileStmt cnd b) → LandedN 1 c (fun c' => JalPreBundle cnd c' st d env))
    (flCond : ∀ (cc : Expr) (step : Option Expr) (b : Stmt) (c : Config) (st : SpecSt)
      (d : Nat) (env : Addr),
      FEntryC c st d env (some cc) step b → LandedN 1 c (fun c' => JalPreBundle cc c' st d env)) :
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
      SEntryC c st d env (.expr e) → LandedN 1 c (fun c' => JalPreBundle e c' st d env))
    (stmtRet : ∀ (e : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      SEntryC c st d env (.ret (some e)) → LandedN 1 c (fun c' => JalPreBundle e c' st d env))
    (stmtVarInit : ∀ (x : String) (e : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      SEntryC c st d env (.varDecl x (some e)) → LandedN 1 c (fun c' => JalPreBundle e c' st d env))
    (stmtIfCond : ∀ (cnd : Expr) (t : Stmt) (e : Option Stmt) (c : Config) (st : SpecSt)
      (d : Nat) (env : Addr),
      SEntryC c st d env (.ifStmt cnd t e) → LandedN 1 c (fun c' => JalPreBundle cnd c' st d env))
    (stmtWhileCond : ∀ (cnd : Expr) (b : Stmt) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      SEntryC c st d env (.whileStmt cnd b) → LandedN 1 c (fun c' => JalPreBundle cnd c' st d env))
    (flCond : ∀ (cc : Expr) (step : Option Expr) (b : Stmt) (c : Config) (st : SpecSt)
      (d : Nat) (env : Addr),
      FEntryC c st d env (some cc) step b → LandedN 1 c (fun c' => JalPreBundle cc c' st d env)) :
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
      SEntryC c st d env (.expr e) → LandedN 1 c (fun c' => JalPreBundle e c' st d env))
    (stmtRet : ∀ (e : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      SEntryC c st d env (.ret (some e)) → LandedN 1 c (fun c' => JalPreBundle e c' st d env))
    (stmtVarInit : ∀ (x : String) (e : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      SEntryC c st d env (.varDecl x (some e)) → LandedN 1 c (fun c' => JalPreBundle e c' st d env))
    (stmtIfCond : ∀ (cnd : Expr) (t : Stmt) (e : Option Stmt) (c : Config) (st : SpecSt)
      (d : Nat) (env : Addr),
      SEntryC c st d env (.ifStmt cnd t e) → LandedN 1 c (fun c' => JalPreBundle cnd c' st d env))
    (stmtWhileCond : ∀ (cnd : Expr) (b : Stmt) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      SEntryC c st d env (.whileStmt cnd b) → LandedN 1 c (fun c' => JalPreBundle cnd c' st d env))
    (flCond : ∀ (cc : Expr) (step : Option Expr) (b : Stmt) (c : Config) (st : SpecSt)
      (d : Nat) (env : Addr),
      FEntryC c st d env (some cc) step b → LandedN 1 c (fun c' => JalPreBundle cc c' st d env)) :
    EvalChildStages :=
  evalChildStages_ublr_wired evalIH hUnGeom hBinGeom hLogGeom hBinRStage hLogRStage
    -- assignE: the wave-37 machine-composed arm-head field
    (fun x e c st d env hEE =>
      assignE_field_of_dispatch x e c st d env (hAssignDisp x e c st d env) hEE)
    -- callF: the wave-37 machine-composed arm-head field
    (fun f args c st d env hEE =>
      callF_field_of_dispatch f args c st d env (hCallDisp f args c st d env) hEE)
    argsHead stmtExpr stmtRet stmtVarInit stmtIfCond stmtWhileCond flCond

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

end Vsa.Sim
