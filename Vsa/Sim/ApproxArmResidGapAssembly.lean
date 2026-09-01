import Vsa.Sim.ArmSegSplitEval
import Vsa.Sim.ArmSegSplitNonEval
import Vsa.Sim.ArmSegSplitSqEntry

/-!
# `ApproxArmResidGapAssembly` — the full 29-field `ApproxArmResidGap` from staging bundles (Task #78)

`ApproxArmReseat.ApproxArmResidGap Reflect` is `ApproxDispatchSuppliers.ApproxArmResid`
at the concrete divergence-fold entries (`EEntryC`/`AEntryC`/`CEntryC`/`SEntryC`/
`FEntryC`).  Its 29 fields are now covered class-by-class by three staging groups plus
one lone field:

* `ArmSegSplitEval.armResidGap_evalChildFields` — 14 EVAL-child-landing fields from
  `EvalChildStages` (post = `EEntryC <child expr>`, no extra spec premise).
* `ArmSegSplitEval.flStep_split` — the 15th eval-child field `flStep` (post = `EEntryC
  <step expr>`, but carrying `ForCond`/`ExecS`/status premises), from its own staging.
* `ArmSegSplitNonEval.armResidGap_nonEvalChildFields` — 11 NON-eval-child fields from
  `NonEvalChildStages` (post = `SEntryC`/`AEntryC`/`CEntryC`/`FEntryC`).
* `ArmSegSplitSqEntry.armResidGap_sqEntryFields` — the 3 `SqEntryC`-boundary fields
  (`callBody`/`stmtBlock`/`seqHead`) from `SqEntryStages`.

This file bundles the four staging inputs (`ArmStages`) and assembles the full
`ApproxArmResidGap` structure by projecting each `*_split` corollary into the matching
named field — the FIRST point at which the whole divergence arm residual becomes ONE
supplier interface (the staging spans), with every marshalling bridge load-bearing.
`divFamily_of_armStages` then threads it through `ApproxArmReseat.
divFamily_of_armResidGap` to `DivFamily L`, so the divergence family closes on:
`hEntry` (shared entry drive) + `hIter` (loop-body assembly + `seqStep`) + `ArmStages`
(the 29 arm-head staging spans).

The staging spans themselves (`*StagePre` / `*Stages` field bodies) remain the honest
upstream residual — each is a per-arm arm-head re-cut of a landed M4 chain, strictly
smaller than the field it discharges.  This file adds ZERO machine content; it is the
pure composition that a future staging supplier plugs straight into.

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
open Vsa.Sim.ApproxDispatchSuppliers (ApproxArmResid)

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

/-! ## §1. `ArmStages` — the four staging bundles + the lone `flStep` staging

The complete upstream supplier interface for `ApproxArmResidGap`: the three per-group
staging bundles, plus the single `flStep` staging residual (which carries its own
`ForCond`/`ExecS`/status premises so is not in any group bundle). -/

-- discipline: allow(R6-conj-tower-def) `ArmStages` is the top-level staging BUNDLE:
-- three named sub-bundles + one lone staging residual, projected by name below.
structure ArmStages (Reflect : Config → Addr → List Stmt → Prop) : Prop where
  eval : EvalChildStages
  nonEval : NonEvalChildStages
  sq : SqEntryStages Reflect
  /-- The lone `flStep` staging (post = `EEntryC <step>`, with the for-loop
  `ForCond`/`ExecS`/status premises); discharged by `flStep_split`. -/
  flStep : ∀ (cnd : Option Expr) (e : Expr) (b : Stmt) (status : Status)
    (c : Config) (st st' st'' : SpecSt) (d : Nat) (env : Addr),
    ForCond st d env cnd st' → ExecS st' d env b st'' status →
    (status = .normal ∨ status = .cont) → FEntryC c st d env cnd (some e) b →
    LandedN 1 c (fun c' => JalPreBundle e c' st'' d env)

/-! ## §2. `armResidGap_of_stages` — assemble the full `ApproxArmResidGap`

Project each `*_split` corollary into the matching named field of `ApproxArmResid` at
the concrete entries (= `ApproxArmResidGap`).  The 14 eval-child fields come from
`armResidGap_evalChildFields`, the 11 non-eval from `armResidGap_nonEvalChildFields`,
the 3 SqEntryC-boundary from `armResidGap_sqEntryFields`, and `flStep` from its own
`flStep_split`. -/

theorem armResidGap_of_stages (Reflect : Config → Addr → List Stmt → Prop)
    (S : ArmStages Reflect) :
    ApproxArmResidGap Reflect := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13⟩ :=
    armResidGap_evalChildFields S.eval
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ :=
    armResidGap_nonEvalChildFields S.nonEval
  obtain ⟨q0, q1, q2⟩ := armResidGap_sqEntryFields Reflect S.sq
  exact {
    -- EApprox
    assignE := fun c st d env x e => e5 x e c st d env
    binaryL := fun c st d env op l r => e1 op l r c st d env
    binaryR := fun c st st' d env op l r lv => e2 op l r c st st' d env lv
    logicalL := fun c st d env lop l r => e3 lop l r c st d env
    logicalR := fun c st st' d env lop l r lv => e4 lop l r c st st' d env lv
    unaryE := fun c st d env op e => e0 op e c st d env
    callF := fun c st d env f args => e6 f args c st d env
    callArgs := fun c st st' d env f args fv => n6 f args c st st' d env fv
    callC := fun c st st' st'' d env f args fv vs => n8 f args c st st' st'' d env fv vs
    -- ArgsApprox
    argsHead := fun c st d env e es => e7 e es c st d env
    argsTail := fun c st st' d env e es v => n7 e es c st st' d env v
    -- CApprox
    callBody := fun c st d a cd vs store' frame => q0 c st d a cd vs store' frame
    -- SApprox
    stmtExpr := fun c st d env e => e8 e c st d env
    stmtRet := fun c st d env e => e9 e c st d env
    stmtVarInit := fun c st d env x e => e10 x e c st d env
    stmtBlock := fun c st d env ss store' inner => q1 c st d env ss store' inner
    stmtIfCond := fun c st d env cnd t e => e11 cnd t e c st d env
    stmtIfThen := fun c st st' d env cnd t e v => n0 cnd t e c st st' d env v
    stmtIfElse := fun c st st' d env cnd t e v => n1 cnd t e c st st' d env v
    stmtWhileCond := fun c st d env cnd b => e12 cnd b c st d env
    stmtWhileBody := fun c st st' d env cnd b v => n2 cnd b c st st' d env v
    stmtWhileLoop := fun c st st' st'' d env cnd b v status =>
      n3 cnd b c st st' st'' d env v status
    stmtForInit := fun c st d env init cnd step b store' outer =>
      n4 init cnd step b c st d env store' outer
    stmtForLoop := fun c st st' d env init cnd step b store' outer =>
      n9 init cnd step b c st st' d env store' outer
    -- FlApprox
    flCond := fun c st d env cc step b => e13 cc step b c st d env
    flBody := fun c st st' d env cnd step b => n5 cnd step b c st st' d env
    flStep := fun c st st' st'' d env cnd e b status hFC hEx hstat hFE =>
      flStep_split cnd e b status c st st' st'' d env
        (S.flStep cnd e b status c st st' st'' d env) hFC hEx hstat hFE
    flLoop := fun c st st' st'' st''' d env cnd step b status =>
      n10 cnd step b c st st' st'' st''' d env status
    -- Approx.head
    seqHead := fun c st d env s ss => q2 c st d env s ss }

#print axioms armResidGap_of_stages

/-! ## §3. `divFamily_of_armStages` — the composing capstone to `DivFamily L`

Threading `armResidGap_of_stages` through `ApproxArmReseat.divFamily_of_armResidGap`.
The whole divergence family reduces to: `hEntry` (the shared entry drive), `hIter`
(the loop-body iteration assembly, which also supplies `seqStep` and the concrete
`SqEntryC`), and `ArmStages` (the 29 arm-head staging spans, the honest upstream
residual).  Every marshalling bridge (`evalEntry_of_jalPrefix`/`execEntry_of_jalPrefix`/
`segEntry_of_jalPrefix` + the `SqEntryC` repack + `loopHeadDispatch_span`) is
load-bearing; nothing but the staging spans remains open. -/

theorem divFamily_of_armStages
    (Reflect : Config → Addr → List Stmt → Prop) (L : Layout)
    (hEntry : Vsa.Sim.DivCorrClose.DivEntryDrive Reflect L)
    (hIter : Vsa.Sim.IterSeamAssembly.IterSeamResid Reflect)
    (S : ArmStages Reflect) :
    Vsa.Sim.InterpSimBundle.DivFamily L :=
  divFamily_of_armResidGap Reflect L hEntry hIter (armResidGap_of_stages Reflect S)

#print axioms divFamily_of_armStages

end Vsa.Sim
