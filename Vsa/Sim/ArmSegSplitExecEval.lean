import Vsa.Sim.ArmSegSplitEval

/-!
# `ArmSegSplitExecEval` — the exec-arm `jal eval_expr` marshalling twin (Wave 40)

`ArmSegSplit.evalEntry_of_jalPrefix` marshals the recursive `jal eval_expr` seam
that lives INSIDE `eval_expr`'s own text: its `hjalSite` is typed with
`Eval_exprLoaded σ.mem` (the jal's instruction bytes are eval_expr text).  The SIX
exec-eval `EvalChildStages` fields (`stmtExpr`/`stmtRet`/`stmtVarInit`/`stmtIfCond`/
`stmtWhileCond`/`flCond`) reach `eval_expr` from a `jal` sited in **`exec_stmt`'s
text** (e.g. `0x80004180`), whose bytes come from `Exec_stmtLoaded` — and
`0x80004180` is NOT covered by any `eval_exprChunk`.  So those arm-head cuts cannot
satisfy `JalPreBundle.hjalSite` (observation
`execframeshift-REAL-obstruction-is-jalSite-loaded-predicate-not-frame`).

This file is the TWIN:

* `execEvalEntry_of_jalPrefix` — a clone of `evalEntry_of_jalPrefix` whose
  `hjalSite` is typed with `Exec_stmtLoaded σ.mem`.  The landed child `EvalEntry` is
  IDENTICAL (the child eval frame still needs `Eval_exprLoaded mcall`, carried as a
  separate premise); only the seam's loaded-predicate flips.
* `ExecJalPreBundle` — the `JalPreBundle` twin whose `hjalSite` uses
  `Exec_stmtLoaded` (and which additionally carries `Exec_stmtLoaded mcall`, since
  the exec-arm jal site consumes it).
* `landedN_eentryC_of_execPreBundle` — the exec twin of
  `landedN_eentryC_of_preBundle`.

Everything else (the frame-shift ghost rebase `sp := esp+1088`, the wide-window
`StoreRepr` survival premise, the mv/ld site batteries) is unchanged from the eval
design; the twin is the ONE shared bridge the 6 exec arm heads land through.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no `maxHeartbeats` bump.
Axioms of every theorem ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps StepsN)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim

/-! ## The `ExecJalPreBundle` twin + its marshalling bridge -/

-- discipline: allow(R7-conj-tower-def) `ExecJalPreBundle` is the exec twin of the
-- SANCTIONED landing bundle `JalPreBundle` (carries layout DATA a `structure : Prop`
-- cannot project); its named destructurer is `landedN_eentryC_of_execPreBundle`.

/-! ## The 6 exec-eval `EvalChildStages` field splits (through `ExecJalPreBundle`)

Exact twins of `ArmSegSplitEval`'s `stmtExpr_split`/`stmtRet_split`/`stmtVarInit_split`/
`stmtIfCond_split`/`stmtWhileCond_split`/`flCond_split`, but the staging residual
lands at `ExecJalPreBundle` (the `Exec_stmtLoaded`-typed jal seam) and the exec
marshalling bridge finishes.  Each is a one-liner over `execEvalChildSplit_of_stage`;
the arm-head cut supplier (`blockB_<arm>_stagePre`) fills the residual. -/

end Vsa.Sim
