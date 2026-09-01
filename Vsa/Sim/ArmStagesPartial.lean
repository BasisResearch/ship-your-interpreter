import Vsa.Sim.ApproxArmResidGapAssembly
import Vsa.Sim.SeqHeadStages

/-!
# `ArmStagesPartial` — per-field builders for the `ArmStages` divergence bundle (Task #81)

`ApproxArmResidGapAssembly.divFamily_of_armStages` consumes ONE monolithic
`ArmStages Reflect` (= `EvalChildStages` × `NonEvalChildStages` × `SqEntryStages` ×
the lone `flStep`).  A partial-coverage supplier that has landed only SOME staging
spans cannot build the whole structure literal in one shot — it needs to drop each
landed field in as it lands, and mark the rest as its remaining residual.  This file
supplies the per-class *builders* that turn a flat list of field-typed lemmas into the
corresponding bundle, so:

* `evalChildStages_mk` — the flat builder for `EvalChildStages` (14 group fields plus
  the wave-36 `evalIH` term-family link;
  `flStep` is the separate lone bundle field, built alongside).  Each argument is
  EXACTLY one `EvalChildStages` field type, so a landed `*_stagePre` supplier
  (composed with `blockA_k` into the `EEntryC`-source shape) plugs straight in and the
  un-landed ones stay named `∀`-premises the caller still owes.
* `nonEvalChildStages_mk` / `sqEntryStages_mk` — the analogous 11-arg / 3-arg builders.
* `armStages_mk` — the top assembler: the four bundles + `flStep` into `ArmStages`.

Because each builder is the structure's own anonymous constructor, it adds ZERO logic
— its VALUE is the flattened call shape: `divFamily_of_armStages` now closes on 29
independently-suppliable premises (+ `flStep`) instead of one all-or-nothing literal,
so partial delivery threads through immediately.

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

/-! ## §1. `EvalChildStages` — the 14-field builder -/

/-- **Flat builder for `EvalChildStages`.**  Each argument is one field type; the
result is the bundle.  A partial supplier passes its landed staging spans (as the
matching `∀ ... → LandedN 1 ... JalPreBundle ...` lemmas) and leaves the rest as
named holes it still owes. -/
def evalChildStages_mk
    (evalIH : ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value),
      EvalE st d env e st' v → EvalIH st d env e st' v)
    (unary : ∀ (op : UnOp) (e : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      EEntryC c st d env (.unary op e) → LandedN 1 c (fun c' => JalPreBundle e c' st d env))
    (binaryL : ∀ (op : BinOp) (l r : Expr) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      EEntryC c st d env (.binary op l r) → LandedN 1 c (fun c' => JalPreBundle l c' st d env))
    (binaryR : ∀ (op : BinOp) (l r : Expr) (c : Config) (st st' : SpecSt) (d : Nat)
      (env : Addr) (lv : Value),
      EvalIH st d env l st' lv →
      EvalE st d env l st' lv → EEntryC c st d env (.binary op l r) →
      LandedN 1 c (fun c' => JalPreBundle r c' st' d env))
    (logicalL : ∀ (lop : Vsa.While.LogOp) (l r : Expr) (c : Config) (st : SpecSt)
      (d : Nat) (env : Addr),
      EEntryC c st d env (.logical lop l r) → LandedN 1 c (fun c' => JalPreBundle l c' st d env))
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
    -- the 6 exec-eval fields land at `EEntryC` directly (wave 40 re-type)
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
  { evalIH, unary, binaryL, binaryR, logicalL, logicalR, assignE, callF, argsHead,
    stmtExpr, stmtRet, stmtVarInit, stmtIfCond, stmtWhileCond, flCond }

/-! ## §2. `SqEntryStages` — the 3-field builder -/

/-- **Flat builder for `SqEntryStages Reflect`.**  The three `SqEntryC`-boundary
staging residuals (`stmtBlock`/`callBody`/`seqHead`).  `seqHead` is now suppliable
straight from `SeqHeadStages.seqHeadStagePre_of_span` (Task #81 item 5). -/
def sqEntryStages_mk (Reflect : Config → Addr → List Stmt → Prop)
    (stmtBlock : ∀ (ss : List Stmt) (c : Config) (st : SpecSt) (d : Nat) (env : Addr)
      (store' : Store) (inner : Addr),
      StmtBlockStagePre Reflect ss c st d env store' inner)
    (callBody : ∀ (c : Config) (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData)
      (vs : List Value) (store' : Store) (frame : Addr),
      CallBodyStagePre Reflect c st d a cd vs store' frame)
    (seqHead : ∀ (s : Stmt) (ss : List Stmt) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
      SeqHeadStagePre Reflect s ss c st d env) :
    SqEntryStages Reflect :=
  { stmtBlock, callBody, seqHead }

/-! ## §3. `ArmStages` — the top assembler -/

/-- **The top `ArmStages` assembler.**  The four bundle components → `ArmStages`.
This is the seam `divFamily_of_armStages` consumes: with the three group builders
(§1, §2, `ArmSegSplitNonEval` for the middle) plus the lone `flStep`, a partial
supplier assembles exactly the coverage it has and names the rest. -/
def armStages_mk (Reflect : Config → Addr → List Stmt → Prop)
    (eval : EvalChildStages)
    (nonEval : NonEvalChildStages)
    (sq : SqEntryStages Reflect)
    (flStep : ∀ (cnd : Option Expr) (e : Expr) (b : Stmt) (status : Status)
      (c : Config) (st st' st'' : SpecSt) (d : Nat) (env : Addr),
      ForCond st d env cnd st' → ExecS st' d env b st'' status →
      (status = .normal ∨ status = .cont) → FEntryC c st d env cnd (some e) b →
      LandedN 1 c (fun c' => JalPreBundle e c' st'' d env)) :
    ArmStages Reflect :=
  { eval, nonEval, sq, flStep }

/-- **The composing capstone via the assembler.**  `divFamily_of_armStages` fed the
four components directly — the shape a partial supplier threads: build each bundle
from its per-field lemmas (`evalChildStages_mk` / `sqEntryStages_mk` / the
`NonEvalChildStages` literal), supply `flStep`, and get `DivFamily L` modulo
`hEntry`/`hIter`. -/
theorem divFamily_of_armStageComponents
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
  divFamily_of_armStages Reflect L hEntry hIter (armStages_mk Reflect eval nonEval sq flStep)

#print axioms divFamily_of_armStageComponents

end Vsa.Sim
