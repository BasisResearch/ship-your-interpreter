import Vsa.Sim.TermSimAssembly
import Vsa.Sim.LoopScaffoldClose
import Vsa.Sim.TermCaseBundle

/-!
# Layer 4 — the loop-scaffold rows (`hInit*`/`hFc*`/`hEs*`, both `.none` and `.some`)

The `ExecInit`/`ForCond`/`ExecStep` loop-scaffold sub-relations are internal,
re-entrant control points of the `for` body.  Their honest per-iteration machine
work is NOT carried by the recursor scaffold motives (`mExecInit`/`mForCond`/
`mExecStep`, `Vsa/Sim/TermSimAssembly.lean`): `execForStartSim`
(`ExecForStart.lean`) consumes the `ExecInit`/`ForCond`/`ExecStep` sub-derivations
as ignored `_`, and the real init/cond/step machine chain flows through `hArm` +
the `ExecForStep` `hstep` oracle.

Motive history (ledgers `scaffold-motive-independent-pq`,
`scaffold-some-motive-unsatisfiable`): the motives were first a `SegEntry →
SegExit` Triple with INDEPENDENT `(p, q)` PCs (the `.none` obstruction), then a
single-PC `p` span (fixing `.none` via `LoopScaffoldClose.segIdentity`, but leaving
the DUAL `.some` obstruction: `ExecInit.some`/`ForCond.some`/`ExecStep.some` mutate
the store, `st' ≠ st`, so a same-PC span with a different-store post is
unsatisfiable).  Both amendments were half-fixes of dead plumbing.  The final
amendment sets all three motives to `True`, so EVERY constructor — `.none` and
`.some` alike — is fillable by `trivial`, with zero consumer re-threading.

This file discharges all six premises (`hInit{None,Some}`/`hFc{None,Some}`/
`hEs{None,Some}`), filling the `TermCaseBundle.TermCases` fields (and the
identically-typed positional premises of `term_sim_of_cases` /
`execSeq_sim_of_cases`) directly, with NO residual.  The old `.some` residual
`def`s (`hInitSome_resid`/`hFcSome_resid`/`hEsSome_resid`) — which were
unsatisfiable-as-stated — are DELETED; their `TermResiduals`/`TermCases` GAP
fields are removed and supplied unconditionally by the `.some` rows below.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`/`admit`.
-/

namespace Vsa.Sim.ScaffoldRows

open LeanRV64DExecutable Sail
open Register
open Vsa.Machine (Config)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim
open Vsa.Sim.Scaffold
open Vsa.Sim.TermSimAssembly

local notation "SpecSt" => Vsa.While.St

/-! ## §1. The six loop-scaffold rows (`.none` and `.some`)

Each row is `mExecInit …/mForCond …/mExecStep …` for one constructor.  With the
motives now `True` every row is `trivial` — the honest init/cond/step work lives in
`execForStartSim`'s `ExecForStep` oracle, not here.  The rows exist so the bundle
assembler drops them in by name with no residual field (mirroring the former
`.none` treatment). -/

/-- `ExecInit.none` row — discharges `TermCases.hInitNone`. -/
theorem hInitNone_row :
    ∀ (st : SpecSt) (d : Nat) (env : Addr),
      mExecInit st d env none st (ExecInit.none st d env) := by
  intro st d env; trivial

/-- `ExecInit.some` row — discharges `TermCases.hInitSome` (was the unsatisfiable
`hInitSome_resid`).  The recursor threads the sub-`ExecS` IH as `_`. -/
theorem hInitSome_row :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (st' : SpecSt) (status : Status)
      (a : ExecS st d env s st' status),
      mExecS st d env s st' status a →
      mExecInit st d env (some s) st' (ExecInit.some st d env s st' status a) := by
  intro st d env s st' status a _hIH; trivial

/-- `ForCond.none` row — discharges `TermCases.hFcNone`. -/
theorem hFcNone_row :
    ∀ (st : SpecSt) (d : Nat) (env : Addr),
      mForCond st d env none st (ForCond.none st d env) := by
  intro st d env; trivial

/-- `ForCond.some` row — discharges `TermCases.hFcSome` (was the unsatisfiable
`hFcSome_resid`).  The recursor threads the sub-`EvalE` IH as `_`. -/
theorem hFcSome_row :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (st' : SpecSt) (v : Value)
      (a : EvalE st d env c st' v) (a_1 : v.truthy = true),
      mEvalE st d env c st' v a →
      mForCond st d env (some c) st' (ForCond.some st d env c st' v a a_1) := by
  intro st d env c st' v a a_1 _hIH; trivial

/-- `ExecStep.none` row — discharges `TermCases.hEsNone`. -/
theorem hEsNone_row :
    ∀ (st : SpecSt) (d : Nat) (env : Addr),
      mExecStep st d env none st (ExecStep.none st d env) := by
  intro st d env; trivial

/-- `ExecStep.some` row — discharges `TermCases.hEsSome` (was the unsatisfiable
`hEsSome_resid`).  The recursor threads the sub-`EvalE` IH as `_`. -/
theorem hEsSome_row :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value)
      (a : EvalE st d env e st' v),
      mEvalE st d env e st' v a →
      mExecStep st d env (some e) st' (ExecStep.some st d env e st' v a) := by
  intro st d env e st' v a _hIH; trivial

#print axioms hInitNone_row
#print axioms hInitSome_row
#print axioms hFcNone_row
#print axioms hFcSome_row
#print axioms hEsNone_row
#print axioms hEsSome_row

/-- Slot check: the six rows have EXACTLY the `TermCases` bundle-field types, so a
bundle assembler drops them in with no adapter.  Type-checking this `example` is
the machine confirmation. -/
example :
    (∀ (st : SpecSt) (d : Nat) (env : Addr),
        mExecInit st d env none st (ExecInit.none st d env)) ∧
    (∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (st' : SpecSt) (status : Status)
        (a : ExecS st d env s st' status),
        mExecS st d env s st' status a →
        mExecInit st d env (some s) st' (ExecInit.some st d env s st' status a)) ∧
    (∀ (st : SpecSt) (d : Nat) (env : Addr),
        mForCond st d env none st (ForCond.none st d env)) ∧
    (∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (st' : SpecSt) (v : Value)
        (a : EvalE st d env c st' v) (a_1 : v.truthy = true),
        mEvalE st d env c st' v a →
        mForCond st d env (some c) st' (ForCond.some st d env c st' v a a_1)) ∧
    (∀ (st : SpecSt) (d : Nat) (env : Addr),
        mExecStep st d env none st (ExecStep.none st d env)) ∧
    (∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value)
        (a : EvalE st d env e st' v),
        mEvalE st d env e st' v a →
        mExecStep st d env (some e) st' (ExecStep.some st d env e st' v a)) :=
  ⟨hInitNone_row, hInitSome_row, hFcNone_row, hFcSome_row, hEsNone_row, hEsSome_row⟩

end Vsa.Sim.ScaffoldRows
