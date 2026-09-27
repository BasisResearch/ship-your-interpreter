import Vsa.Sim.ExecRecCommon
import Vsa.Sim.ExecEntry
import Vsa.Sim.StepCount

/-!
# `ArmSegSplitExec` — the `jal exec_stmt`→child-`ExecEntry` marshalling twin (Task #76, Half A.1)

`ArmSegSplit.evalEntry_of_jalPrefix` is the shared jal→child-`EvalEntry` marshalling
fact for the recursive `jal eval_expr` seam.  This file is its **exec_stmt twin**:
`execEntry_of_jalPrefix` — from an arm state at a recursive `jal exec_stmt` PC with
the child statement's ABI arguments staged (`a0 = aInterp`, `a1 = aStmt`,
`a2 = aEnv`, `a3 = aRet`, `sp` lowered), one `jal` step lands at the child's rich
`ExecEntry`.  It is `armTail_rec_es` (`ExecRecCommon.lean`) truncated *before* its IH
application, exactly as `evalEntry_of_jalPrefix` truncates `armTail_rec` — except the
landed post is `ExecEntry` (a child STATEMENT sub-call) rather than `EvalEntry`.

## What the jal step supplies vs. what must be premises (the exec-side audit)

`ExecEntry` (`Vsa/Sim/ExecEntry.lean`) mirrors `EvalEntry` with statement-specific
differences that shape the premise bundle:

* **Supplied by the jal step** (via `sigmaPost_jal`): `good`, `tick`, `pc`
  (= `execStmtEntry`, via `hjaltgt`), `a0`/`a1`/`a2`/`a3` (the four staged args —
  note `a3` is the RETSLOT, absent on the eval side), `ra` (= link `retPC`),
  `spReg` (= lowered `sp - hdrm`), `minstret`, `mem` (= `mcall`), `out`, `frame`,
  `spill_defined` (FOUR spills: s0/s1/s2/s3, not three).
* **Must be premises of the arm-head bundle**: the child-frame GEOMETRY at the
  lowered `sp` — `stackOK` for the lowered sp with `176 + 1088` headroom (statement
  frame + one eval frame), the child `Stmt` node's `StmtRepr`/RAM/
  disjointness at `aStmt`, `StoreRepr` + its survival clause (NO sret carve-out —
  `ExecEntry.store_survives` frames only `[SL.lo, sp)`), and the `exec_stmt`
  code-region disjointness re-checked against the lowered `sp`.

So `execEntry_of_jalPrefix` is the ONE reusable exec-side seam; the statement-arm
classes whose recursion goes into a child STATEMENT (`stmtIfThen`/`stmtIfElse`/
`stmtWhileBody`/`stmtForInit`/`flBody`) instantiate it after their own arm-head
staging span establishes the bundle.

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
open Vsa.Alloc
open Vsa.Sim.Code

