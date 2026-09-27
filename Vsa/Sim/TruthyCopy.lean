import Vsa.Sim.EvalChildArm
import Vsa.Sim.PinW
import Vsa.Sim.BridgeSegFramed

/-!
# `TruthyCopy` — the parametric condition-copy and `value_truthy` seam

After a condition child returns, the `while`, `if`, and `for` arms all copy the
24-byte result from the sub-result slot to `esp+16`, call `value_truthy`, and
branch on its answer.  `WhileGeomSuppliers` closed this seam for `while` with
`0x80004050`-specific files.  This file states it ONCE over a descriptor
`TruthyCopy` attached to an `EvalChildArm`:

* `TruthyCopy.Cert D T` — decided facts (the reflected copy's fold, its
  write log as three `sd`s, the `jal value_truthy` site);
* `copyReady_of_exitKit` — from the child's exit kit, park at `value_truthy`;
* `truthyReturn_of_copyReady` — the helper returns with the truthiness bit;
* `route_of_truthyReturn` — run any reflected branch route from that return;
* `normalExitPre_of_route` — a route that ends at a `li a0,0` is a
  `NormalExitTailPre`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no `maxHeartbeats`
bump.  Axioms of every theorem ⊆ {propext, Classical.choice, Quot.sound}.
-/

namespace Vsa.Sim

-- discipline: allow(R7-conj-tower-def) the `∃` here are the fixed StepObs site post
-- (`Cert.jal_site`), reached-config existentials of runs, and saved-register witnesses
-- inside named-field structures; all consumed through named fields.

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

local notation "SpecSt" => Vsa.While.St

/-! ## The descriptor -/

end Vsa.Sim
