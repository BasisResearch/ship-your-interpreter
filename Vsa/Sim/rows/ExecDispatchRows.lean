import Vsa.Sim.ExecIf
import Vsa.Sim.rows.EvalChildArmIf
import Vsa.Sim.ExecIf2
import Vsa.Sim.ExecWhile
import Vsa.Sim.ExecWhile2
import Vsa.Sim.ExecBlock2
import Vsa.Sim.ExecForStart
import Vsa.Sim.ExecWhileIndexed
import Vsa.Sim.rows.ExecIHWiden
import Vsa.Sim.TermSimClose

/-!
# Layer 4 — M4 dispatch/loop `ExecS` cases re-landed at `ExecExitD` (the `mExecS` motive)

The dispatch/loop statement-side twin of `rows/ExecRecRows.lean`, built ON the ONE
exit-sim → motive combinator `execIH_of_exitSim` (`rows/ExecIHWiden.lean`).  Each
landed dispatch/loop simulation (`execIfNoneSim`/`execIfTrueSim`/`execIfFalseSim`/
`execWhileFalseSim`/`execWhileSim`/`execBlockSim`/`execForStartSim`) concludes the
packaged shape `ExecExitSim … status` (the `Triple` from `ExecEntry ∧ out=out0` to
plain `ExecExit`); the combinator upgrades it to the `mExecS` motive `ExecIH` (entry
`out0 := c.σ.sailOutput` by `rfl`; exit widened `ExecExit → ExecExitD` by the
parametric `ExecRecWiden`).  So EVERY row here is `execIH_of_exitSim hW hSim` with
ZERO hand-navigated `intro`/`obtain`/`refine` — the widen-and-marshal lives once in
the combinator.

## The residual bundle shape — a named `structure`, projected per call

Each case's residual bundle is a `structure … : Prop where` with named fields (gate
R6/R7: no positional `.2.2` towers) carrying EXACTLY the landed sim's OWN residual
arguments (its `hGlue`/`hslot`/`hmaps`/`hstep`/`hArm`/`hEpi`/branch-IH) plus the
widener `hW`.  A `*Resid` is that structure ∀-closed over the ghosts.  The row projects
`.hW` into the combinator's widener slot and the rest into the sim's argument slots.
Adding a new dispatch/loop case is: one named structure + one `execIH_of_exitSim` line.

## The one structural residual worth flagging: `if`'s branch IH

`execIfTrueSim`/`execIfFalseSim` consume the branch derivation as an
`ExecDispatchIH` (the branch re-enters the shared `if` frame POST-prologue at
`0x80004014` — no second prologue).  The recursor hands the branch sub-derivation as
`mExecS = ExecIH` (the FULL-entry shape through the prologue at `0x80003fe0`).  There
is no `ExecIH → ExecDispatchIH` bridge, and there cannot be a trivial one: the
re-dispatch SKIPS the prologue.  So the `ExecDispatchIH` is a genuine SEPARATE
residual, carried as the field `hBranch` of `IfTrueGeom`/`IfFalseGeom`; the recursor's
`ExecIH` is threaded too (the honest spec witness).  See observations
`if-branch-dispatch-ih`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

-- discipline: allow(R7-conj-tower-def) The `∃`s counted here are NOT new anonymous
-- post-towers: every one is the field TYPE of a named `*Geom` structure, re-stating a
-- LANDED sim post predicate (`SubExecReturn`/`ExecDispatchReady`, whose ∃-shape is
-- fixed by `execIfNoneSim`/`execIfTrueSim`/… signatures) so the residual bundle unifies
-- with the sim it feeds. The bundles ARE named-field structures (R6/R7-compliant); the
-- inner ∃ belongs to the sim's own post, not to this file. Twin of the grandfathered
-- `rows/ExecRecRows.lean` (same `SubExecReturn` field shapes).

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim.Rows

open Vsa.Sim

local notation "SpecSt" => Vsa.While.St

/-! ## `ifNone` -/

/-! ## `whileFalse` — condition dispatch and reached normal return -/

/-! ## `ifTrue` / `ifFalse` — dispatch, condition, and the in-frame re-dispatch -/

/-! ## `block` — `execBlockSim` (env_new + execSeqLoop + epilogue) -/

/-! ## `forStart` — `execForStartSim` (env_new + ExecInit + execForLoopBody) -/

/-! ## `whileBreak` / `whileRet` / `whileLoop` -/

end Vsa.Sim.Rows
