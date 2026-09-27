import Vsa.Sim.rows.ExecRecRows

/-!
# Layer 4 — `execIH_of_exitSim`: the ONE exit-sim → `ExecIH` combinator

Every landed dispatch/loop statement simulation (`execIfNoneSim`,
`execWhileFalseSim`, `execIfTrueSim`, `execBlockSim`, `execWhileSim`,
`execForStartSim`, …) concludes the SAME packaged shape (at a fixed ghost layout):

    Triple (fun c => ExecEntry … c ∧ c.σ.sailOutput = out0) (ExecExit … st' status …)

quantified over the entry `sailOutput` array `out0`; while the `mExecS` recursor
motive (`TermSimAssembly.mExecS = ExecBlock.ExecIH` by defeq) demands the ghost-∀

    ExecIH … = ∀ ghosts, Triple (ExecEntry …) (ExecExitD … st' status …)

The gap is UNIFORM (per `rows/ExecCaseGeom.lean`, `rows/ExecRecRows.lean`):

1. entry `out0 := c.σ.sailOutput` by `rfl` (drop the `∧ … = out0` conjunct), and
2. exit `ExecExit → ExecExitD` via the parametric widener `ExecRecWiden`
   (`= Widen … (stackFoot SL)`) and its bridge `execExitD_of_execExit_rec`.

`execIH_of_exitSim` performs BOTH — over the FULL ghost-∀ — once, for ANY producer
of the packaged exit Triple.  Then every dispatch/loop `*SimD` is a ONE-LINE
instantiation: the case supplies (a) a ghost-∀ widener `hW` and (b) a ghost-∀ sim
`hSim` (the landed sim, its `out0` argument threaded), and `execIH_of_exitSim`
returns the `ExecIH` motive with NO `intro`/`obtain`/`refine` boilerplate and no
per-case marshalling.  This is the exponentiating layer
(`experiments/exponentiation-endgame-design.md` §T1.2): the widen-and-marshal is
proven ONCE and instantiated, not re-navigated per case.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim

/-! ## The exit-sim shape, named once

`ExecExitSim … status` is the packaged output every dispatch/loop sim produces at a
fixed ghost layout and entry `sailOutput` array `out0`: the `Triple` from the
`ExecEntry ∧ out=out0` precondition to the plain `ExecExit`. -/

end Vsa.Sim

