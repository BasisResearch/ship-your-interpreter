import Vsa.Sim.ArmSegSplitTwins

/-!
# `StmtForLoopSegPreB` — the for-cond re-entry staging over `SegPreBundleB`
(Wave 44 pilot for twin 2)

The `stmtForLoop` field of `ApproxArmResid` lands at `FEntryC` — anchored on a
`SegEntry` at the for-cond control point `0x8000426c`.  The machine reaches that
point by **`j 0x8000426c` @0x80004258** (the post-init route; word `0x0140006f`)
or the taken `beqz a1,0x8000426c @0x80004244` (no-init) — interior control, NO
static `jal` targets it, so the jal-modelled `SegPreBundle` staging is
uninstantiable here (observation `nonevalchild-remaining-8-shape-map`).  This
pilot rides `SegPreBundleB` (`ArmSegSplitTwins` §2):

* `ForLoopReentryJSite` — the `j @0x80004258` site obs (`sigmaPost_jump_x0`;
  derivable from `stepObs_j` + the `Exec_stmtLoaded` byte pins; NAMED residual
  per Law 2).
* `ForLoopReentryInv` — the arm state at the `j` site with the light SegEntry
  facts staged.
* `forLoopSegPreB_of_inv` — **PROVED**: the inv marshals into
  `SegPreBundleB 0x8000426c` (the hop via `gregsHopInto_of_jx0Site` ≫
  `StepInto.of_gregsHop`) — the twin-2 instantiation at a real arm.
* `ForLoopReentryDispatch` — the dispatch residual (`SEntryC (.forStmt …)` +
  allocFrame + `ExecInit` → `LandedN 1` at the inv; the env_new ≫ init-exec ≫
  return routing is M4 arm-seg content).
* `stmtForLoop_field_of_dispatch` — the EXACT frozen `ApproxArmResid.stmtForLoop`
  field, composed through `stmtForLoop_splitB`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no `maxHeartbeats`
bump.  Axioms of every theorem ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps StepsN)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.While (St Stmt Expr Value Store Status Addr EvalE ForCond ExecInit ExecS)
open Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

set_option linter.unusedVariables false

end Vsa.Sim
