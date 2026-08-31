import Vsa.Sim.TermSimAssembly
import Vsa.Sim.LoopScaffoldClose
import Vsa.Sim.TermCaseBundle

/-!
# Layer 4 — the loop-scaffold no-op rows (`hInitNone`/`hFcNone`/`hEsNone`)

The three `.none` loop-scaffold constructors (`ExecInit.none`, `ForCond.none`,
`ExecStep.none`) do not change the specification state and, in the compiled
`for` body, do not move control: their machine row is an IDENTITY segment at a
single loop-structural PC.

Before the amendment (ledger `scaffold-motive-independent-pq`) the scaffold
motives (`mExecInit`/`mForCond`/`mExecStep`, `Vsa/Sim/TermSimAssembly.lean`)
quantified the entry PC `p` and exit PC `q` INDEPENDENTLY, so these rows were
UNFILLABLE — an identity segment yields exit PC = entry PC, but the motive
demanded an arbitrary `q`. The amendment tied the two PCs to a single `p`, so
each `.none` premise is now EXACTLY `LoopScaffoldClose.segIdentity` at
`st.store.frames.size`/`st.store.closures.size` (the `st' = st` reflexive case).

This file discharges the three now-fillable premises. They fill the
`hInitNone`/`hFcNone`/`hEsNone` fields of `TermCaseBundle.TermCases` (and the
identically-typed positional premises of `term_sim_of_cases` /
`execSeq_sim_of_cases`) directly, with NO residual.

The `.some` companions (`hInitSome`/`hFcSome`/`hEsSome`) still state a real span
(a straight-line init / cond-eval / step-eval machine segment collapsing to the
loop PC `p`); those remain named residuals — see the module tail.

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

/-! ## §1. The three `.none` no-op rows

Each is `mExecInit …/mForCond …/mExecStep …` for the `.none` constructor
(`st' = st`), which β/δ-reduces to the identity-PC `SegEntry → SegExit` Triple
`LoopScaffoldClose.segIdentity` supplies. The proofs `intro` the motive's
∀-closed layout ghosts + budgets + PC `p` + `m0` and apply `segIdentity`. -/

/-- `ExecInit.none` row — discharges `TermCases.hInitNone`. -/
theorem hInitNone_row :
    ∀ (st : SpecSt) (d : Nat) (env : Addr),
      mExecInit st d env none st (ExecInit.none st d env) := by
  intro st d env g N A SL φf φc dLeft aLeft p m0
  exact Vsa.Sim.LoopScaffoldClose.segIdentity g N A SL φf φc st d dLeft aLeft p m0

/-- `ForCond.none` row — discharges `TermCases.hFcNone`. -/
theorem hFcNone_row :
    ∀ (st : SpecSt) (d : Nat) (env : Addr),
      mForCond st d env none st (ForCond.none st d env) := by
  intro st d env g N A SL φf φc dLeft aLeft p m0
  exact Vsa.Sim.LoopScaffoldClose.segIdentity g N A SL φf φc st d dLeft aLeft p m0

/-- `ExecStep.none` row — discharges `TermCases.hEsNone`. -/
theorem hEsNone_row :
    ∀ (st : SpecSt) (d : Nat) (env : Addr),
      mExecStep st d env none st (ExecStep.none st d env) := by
  intro st d env g N A SL φf φc dLeft aLeft p m0
  exact Vsa.Sim.LoopScaffoldClose.segIdentity g N A SL φf φc st d dLeft aLeft p m0

#print axioms hInitNone_row
#print axioms hFcNone_row
#print axioms hEsNone_row

/-- Slot check: the three no-op rows have EXACTLY the `TermCases` bundle-field
types (`hInitNone`/`hFcNone`/`hEsNone`), so a bundle assembler can drop them in
with no adapter. Type-checking this `example` is the machine confirmation. -/
example :
    (∀ (st : SpecSt) (d : Nat) (env : Addr),
        mExecInit st d env none st (ExecInit.none st d env)) ∧
    (∀ (st : SpecSt) (d : Nat) (env : Addr),
        mForCond st d env none st (ForCond.none st d env)) ∧
    (∀ (st : SpecSt) (d : Nat) (env : Addr),
        mExecStep st d env none st (ExecStep.none st d env)) :=
  ⟨hInitNone_row, hFcNone_row, hEsNone_row⟩

/-! ## §2. The `.some` residuals (precise statements, NOT proved here)

Each `.some` loop-scaffold constructor runs a real straight-line machine
segment starting at the loop PC `p`; the amended motive requires that segment to
land back at `p` (identity-PC span) with the spec post-state `st'` re-represented
and the φ-maps extended. These are the genuine open residuals; a machine bridge
(a `#derive_case` seg from the arm's decoded entry to the loop head, or a
`callSeg` splice where the sub-expression calls `eval_expr`) supplies each.

Recorded as `Prop`-valued `def`s (statement-only, exactly the bundle field
type) so a later row can `:= hInitSome_resid`-style fill them:

* `hInitSome_resid` — `ExecInit.some`: the `for` initializer segment
  (`exec_stmt(init)`, whose status the C swallows) from `p` back to `p`, over
  the sub-`ExecS` IH `mExecS … s st' status`.
* `hFcSome_resid` — `ForCond.some`: the truthy `for` condition
  (`eval_expr(c)` + `value_truthy`, taken branch) from `p` back to `p`, over the
  sub-`EvalE` IH `mEvalE … c st' v`.
* `hEsSome_resid` — `ExecStep.some`: the `for` step expression
  (`eval_expr(e)`) from `p` back to `p`, over the sub-`EvalE` IH.

Their bodies are the EXACT bundle-field types; leaving them as `def`s keeps the
open obligation named and typed (law 2) without asserting it. -/

/-- Residual: the `ExecInit.some` row (bundle field `hInitSome`'s type). -/
def hInitSome_resid : Prop :=
  ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (st' : SpecSt) (status : Status)
    (a : ExecS st d env s st' status),
    mExecS st d env s st' status a →
    mExecInit st d env (some s) st' (ExecInit.some st d env s st' status a)

/-- Residual: the `ForCond.some` row (bundle field `hFcSome`'s type). -/
def hFcSome_resid : Prop :=
  ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (st' : SpecSt) (v : Value)
    (a : EvalE st d env c st' v) (a_1 : v.truthy = true),
    mEvalE st d env c st' v a →
    mForCond st d env (some c) st' (ForCond.some st d env c st' v a a_1)

/-- Residual: the `ExecStep.some` row (bundle field `hEsSome`'s type). -/
def hEsSome_resid : Prop :=
  ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value)
    (a : EvalE st d env e st' v),
    mEvalE st d env e st' v a →
    mExecStep st d env (some e) st' (ExecStep.some st d env e st' v a)

end Vsa.Sim.ScaffoldRows
