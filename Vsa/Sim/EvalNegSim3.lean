import Vsa.While.Cost
import Vsa.Sim.EvalNegSim2
import Vsa.Sim.EntryGroundKit
import Vsa.Sim.EvalIntSim2

/-!
# Recursive negation simulation

Compose the prologue, child call, integer negation, and return epilogue.
The actual call path preserves byte presence. `NegExtras` carries operand
geometry; `EvalEntry.negExtras` in `rows/Field_hNegClosed.lean` supplies it
from the existing entry contract and child stack budget.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## `NegExtras` — the recursive-case facts beyond `EvalEntry`

Everything `blockB_unary`/`blockC_neg` demand that the leaf `EvalEntry` structure
does not carry. `gpre` is the call-point ghost register file (the frame at the
`jal eval_expr`), `aIn` the live `interp*` in `x11`, `aOperand` the operand node
address, `esub` the operand expression. These are the "ArmEntryK widening"
residual (memory `m4-recursive-cases.md` #1) plus `blockC_neg`'s entry-ghost
bridge; a future `blockA_k` widening + full stack-layout derivation discharges
them. -/

/-! ## `EvalNegSimGoal` — the `EvalE.neg` projection of the simulation

In the `EvalIH` motive shape (`EvalEntry → EvalExitD`, mirroring
`Scaffold.motive_EvalE` with `EvalExit` upgraded), taking the sub-derivation's
induction hypothesis `EvalIH st d env esub st' (.int n)`.

Conditional ONLY on:
* `NegExtras` — the operand-node `ExprRepr`+geometry, the extra 1088-byte
  recursive stack headroom, the arena/code/table disjunctions and the `EX_UNARY`
  slot pin, supplied by `EvalEntry.negExtras`.

The arm-register facts (`x11 = interp*`, the call-point ghost bridge) and the
`EvalExitD` upgrade are now DISCHARGED internally from the widened
`ArmEntryK`/`blockC_neg`/`blockD_v_rec` machinery. -/

end Vsa.Sim
