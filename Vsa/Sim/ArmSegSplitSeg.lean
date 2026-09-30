import Vsa.Sim.EvalSimCommon
import Vsa.Sim.ExecEntry
import Vsa.Sim.InductionScaffold
import Vsa.Sim.StepCount

/-!
# `ArmSegSplitSeg` — the `jal`→child-`SegEntry` marshalling variant (Task #76, Half A.2)

`ArmSegSplit.evalEntry_of_jalPrefix` / `ArmSegSplitExec.execEntry_of_jalPrefix` are
the RICH-entry marshalling twins (eval / exec).  The remaining non-eval-child arm
classes of `ApproxArmResid` land at interior control points that have NO dedicated
rich struct — the EX_CALL arg loop (`AEntryC`), the callee-inline body head at
depth `d+1` (`CEntryC`), the for-loop re-entry (`FEntryC`).  `ApproxArmReseat`
anchors those on `SegEntry` at a ghost interior PC.

`SegEntry` (`InductionScaffold.lean`) is a LIGHT entry — PC + `StoreRepr` + `OutRepr`
+ ghost frame + two SKELETON budgets (`depth_budget`/`arena_budget`).  So the jal→
`SegEntry` marshalling is much lighter than the rich twins: the jal step supplies
`good`/`tick`/`pc`/`mem`, and the store/out/budget facts are carried straight
through as premises (nothing frame-lowering-specific is projected — `SegEntry` has
no `stackOK`/`aExpr`/`spill_defined`).

`segEntry_of_jalPrefix` is the ONE shared fact; `AEntryC`/`CEntryC`/`FEntryC`
instantiate it at their own ghost `entryPC` (`argLoopPC`/`calleeBodyPC`/`forCondPC`),
supplying the depth/arena budgets that the interior control point respects.

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

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

end Vsa.Sim
