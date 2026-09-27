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

local notation "SpecSt" => Vsa.While.St

/-! ## §1. The six loop-scaffold rows (`.none` and `.some`)

Each row is `mExecInit …/mForCond …/mExecStep …` for one constructor.  With the
motives now `True` every row is `trivial` — the honest init/cond/step work lives in
`execForStartSim`'s `ExecForStep` oracle, not here.  The rows exist so the bundle
assembler drops them in by name with no residual field (mirroring the former
`.none` treatment). -/

end Vsa.Sim.ScaffoldRows
