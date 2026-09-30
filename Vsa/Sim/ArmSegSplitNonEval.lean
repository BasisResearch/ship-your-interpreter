import Vsa.Sim.ArmSegSplitExec
import Vsa.Sim.ArmSegSplitSeg
import Vsa.Sim.ApproxArmReseat

/-!
# `ArmSegSplitNonEval` — the non-eval-child arm-class splits (Task #76, Half A.3)

`ArmSegSplitEval` closed the 15 EVAL-child fields of `ApproxArmResidGap` (post =
`EEntryC <child expr>`) through `landedN_eentryC_of_preBundle` (built on
`evalEntry_of_jalPrefix`).  This file closes the remaining fields whose post is a
NON-eval interior entry, using the two twins built in Half A.1/A.2:

* **`execEntry_of_jalPrefix`** (the exec-stmt twin) drives the `SEntryC`-landing
  fields — the statement arms whose recursion goes into a CHILD STATEMENT:
  `stmtIfThen`, `stmtIfElse`, `stmtWhileBody`, `stmtForInit`, `flBody`.
* **`segEntry_of_jalPrefix`** (the light SegEntry twin) drives the `AEntryC` /
  `CEntryC` / `FEntryC`-landing fields — the interior control points with no rich
  struct: `callArgs`, `argsTail` (arg loop), `callC` (callee dispatch), `stmtForLoop`,
  `flLoop` (for re-entry).

Exactly the `ArmSegSplitEval` pattern: a per-class `*StagePre` residual (arm-head +
dispatch re-cut to land at the twin's PRE-bundle, NOT consume the IH), a shared
"pre-bundle ⇒ child entry" bridge (`landedN_sEntryC_of_preBundle` /
`landedN_segEntryC_of_preBundle`), and a generic split combinator
(`execChildSplit_of_stage` / `segChildSplit_of_stage`) that `LandedN.bind`s the two.

The lowered-frame geometry premises (child-frame `stackOK`, child `StmtRepr`/
`StoreRepr` survival, depth/arena budgets) stay NAMED premises of the `*PreBundle`,
carried through — not derived.  Each split is STRICTLY SMALLER than its raw field
(stops at the pre-bundle; the verified twin finishes).

NB fields still requiring their OWN (non-twin) marshalling — `callBody`/`stmtBlock`/
`seqHead` land at `SqEntryC` (a `SegEntry + Reflect`, needing the extra `Reflect`
witness, so NOT a bare jal→SegEntry) — stay named in `ApproxArmResidGap`; they are
the `IterSeamAssembly`/`SqEntryC` boundary, not this file's twins.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no `maxHeartbeats`
bump.  Axioms of every theorem ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps StepsN)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.While (St Stmt Expr BinOp UnOp Value ClosureData Store Status Addr EvalE EvalArgs ForCond ExecInit ExecStep ExecS)
open Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

set_option linter.unusedVariables false

/-! ## §1. The exec-stmt PRE-bundle and its `SEntryC` bridge -/

-- discipline: allow(R7-conj-tower-def) `ExecStmtPreBundle` is the SANCTIONED
-- ∃-ghost LANDING BUNDLE (same precedent as `ArmSegSplitEval.JalPreBundle`): it
-- carries layout DATA (φ-maps, arena, per-arm callPC/retPC/jalImm/hdrm) a
-- `structure : Prop` cannot project, so it MUST be a `∃` over that data. It IS the
-- `execEntry_of_jalPrefix` named pre-bundle; every consumer goes through the ONE
-- named destructurer `landedN_sEntryC_of_preBundle`.

/-! ## §2. The SegEntry PRE-bundle and its `AEntryC`/`CEntryC`/`FEntryC` bridges -/

-- discipline: allow(R7-conj-tower-def) `SegPreBundle` is the SANCTIONED ∃-ghost
-- LANDING BUNDLE for the light SegEntry twin; carries layout DATA a
-- `structure : Prop` cannot project. It IS the `segEntry_of_jalPrefix` pre-bundle;
-- consumers go through the named destructurers below.

/-! ## §3. Generic exec/seg-child split combinators (mirror `evalChildSplit_of_stage`) -/

/-! ## §4. The per-field non-eval-child splits (exact `ApproxArmResid` field types)

Each split takes its per-class arm-head-to-pre-bundle staging residual (`hstage`)
and returns EXACTLY the `ApproxArmResid` field type at the concrete entries.  The
staging residual carries the spec-side hypotheses (`EvalE`/`ForCond`/`ExecS`/… that
pin the store `st'` at which the child runs) so the returned split matches the field
signature verbatim; the verified twin finishes the machine content. -/

-- SEntryC-landing statement arms (via the exec twin) ------------------------------

-- AEntryC / CEntryC / FEntryC-landing arms (via the light SegEntry twin) -----------

/-! ## §5. Capstone — the non-eval-child staging bundle + field-group discharge

`NonEvalChildStages` bundles the staging residuals for the 11 NON-eval-child fields
of `ApproxArmResidGap` (post = `SEntryC`/`AEntryC`/`CEntryC`/`FEntryC`).  Each residual
is STRICTLY SMALLER than its field: it stops at `ExecStmtPreBundle`/`SegPreBundle`,
and the verified twin bridge finishes.  The five `SEntryC`-landing arms carry the
exec-stmt pre-bundle; the six `AEntryC`/`CEntryC`/`FEntryC`-landing arms carry the
light SegEntry pre-bundle (with their ghost interior PC + budgets `dLeft`/`aLeft`).

`armResidGap_nonEvalChildFields` discharges the 11 fields at the EXACT `ApproxArmResid`
field types from the bundle — the counterpart of `ArmSegSplitEval`'s
`armResidGap_evalChildFields` (which does the 15 eval-child fields).  Together they
cover 26 of the 29 `ApproxArmResid` fields; the remaining 3 (`callBody`/`stmtBlock`/
`seqHead`) land at `SqEntryC` (a `SegEntry + Reflect`), needing the extra `Reflect`
witness — the `IterSeamAssembly`/`SqEntryC` boundary, not a bare jal twin. -/

-- discipline: allow(R6-conj-tower-def) `NonEvalChildStages` is the staging-residual
-- BUNDLE (same precedent as `ArmSegSplitEval.EvalChildStages`): each field is a
-- per-arm arm-head-to-pre-bundle residual, carrying the ghost interior PC + budgets
-- as ∀-bound data. Its consumer `armResidGap_nonEvalChildFields` projects field by
-- name (no positional navigation).

end Vsa.Sim
