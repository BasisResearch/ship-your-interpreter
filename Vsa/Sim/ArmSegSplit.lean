import Vsa.Sim.EvalRecCommon
import Vsa.Sim.StepCount

/-!
# `ArmSegSplit` — the shared jal→child-entry marshalling fact (Task #75)

The divergence fold in `ApproxDispatchSuppliers.ApproxArmResid` needs, per arm
class, the **PRE-JAL PREFIX** of the arm: from the arm head, ≥1 machine step,
landing AT the child's rich entry (`EvalEntry` for a sub-expression, control at
the recursive `jal eval_expr` target, child NOT yet returned).  Every *landed*
M4 arm Triple (`armTail_rec`, `blockB_unary`, …) instead consumes the child as a
RETURNING IH: it builds the child `EvalEntry`, applies `hIH : EvalIH`, and lands
at `SubEvalReturn` (post-return).  The child `EvalEntry` is therefore reached
mid-chain but never exposed.

This file EXTRACTS that reach as ONE shared marshalling fact,
`evalEntry_of_jalPrefix`: the `armTail_rec` Triple pre (arm state with the
sub-call arguments already staged, at the `jal eval_expr` PC) advances exactly
one machine step to a config satisfying the child's `EvalEntry`.  This is
`armTail_rec` truncated *before* the IH application — lines 311–401 of
`EvalRecCommon.armTail_rec`, verbatim, minus the `hIH` call — packaged as a
`LandedN 1`.

## What the jal-step config supplies vs. what must be premises (the finding)

`EvalEntry` (`Vsa/Sim/InterpEntry.lean`) is a ~40-field structure.  Reading which
fields the post-`jal` config *supplies for free* from the marshalling vs. which
must be carried as premises of the arm-head bundle:

* **Supplied by the jal step itself** (from `sigmaPost_jal`): `good`, `tick`,
  `pc` (= `evalExprEntry`, via `hjaltgt`), `a0`/`a1`/`a2` (the staged
  sret/interp/operand registers, transported by `obs_jalT_other`), `ra` (= the
  link `retPC`, via `hlink`), `spReg` (= the lowered `sp - 1088`), `minstret`,
  `mem` (= `mcall`, unchanged by jal), `out`, `frame` (the sub-ghosts are the
  post-jal register file, so `frame` is `rfl`), `spill_defined`.
* **Must be premises of the arm-head bundle** (NOT derivable from a PC-only or
  even a returning-IH-shaped entry): the sub-call GEOMETRY at the *lowered*
  frame — `stackOK` for `sp - 1088` (needs `SL.lo + 3264 ≤ sp`, one extra frame
  of headroom), the operand node's `ExprRepr`/RAM/disjointness at the
  lowered `sp`, the sub-result buffer geometry, `StoreRepr` + its survival
  clause, and the code/table/arena disjointness re-checked against `sp - 1088`.
  These are exactly the "recursive-case extras" `blockB_unary` takes beyond its
  `ArmEntryK` (the `ArmEntryK` widening residual), and they are why the split
  `EEntryC (.unary op e) → LandedN 1 (EEntryC e)` is NOT closable from `EEntryC`
  alone (see `armSegSplit-*` in `experiments/observations.md`).

So `evalEntry_of_jalPrefix` is the ONE reusable seam (analogous to
`jalStep_of_obs` for the CALL seam); every arm class instantiates it after its
own arm-head staging span establishes the bundle.

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

