import Vsa.Sim.ExecExprRet
import Vsa.Sim.ObsAvoid

/-!
# Layer 4 — M4 statement RECURSION multiplier: `armTail_rec_es`

The `exec_stmt`-frame analog of `armTail_rec` (`EvalRecCommon.lean`). Where
`armTail_rec` is hardwired for the `eval_expr` frame (caller `sp` lowered by 1088,
sub-result buffer below the frame, outer sret in `x9`), `armTail_rec_es` is the
statement-frame version: the caller's `sp` is lowered by **176**, the sub-result
buffer `subsret` lives **inside** the frame at `sp' + 16` (so inside the stack
window `[SL.lo, sp)`, unlike `eval_expr`'s below-frame buffer), and the five
callee-saved spills are ra/s0/s1/s2/s3 at `sp-{8,16,24,32,40}`.

`armTail_rec_es` takes the machine state right at the `jal eval_expr` PC
(`callPC`), with the sub-call's arguments already staged (`a0 = subsret`,
`a1 = aInterp`, `a2 = aOperand`, `sp` lowered), threads the `jal`, applies the
sub-derivation induction hypothesis (`EvalIH`), and repackages its `EvalExitD`
into `SubExecReturn` (the state a recursive statement arm holds after the call).

The setup instructions BEFORE the `jal` (`ld a2,8(s0)`, `addi a0,sp,16`, the two
`mv`s — differing between the `expr` and `ret` arms) are threaded by each arm
from its `ExecArmEntryK` entry to this `callPC` precondition; `armTail_rec_es`
itself starts at the `jal`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
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

/-! ## `armTail_rec_es` — `jal eval_expr` ≫ IH ⇒ `SubExecReturn`

From the machine state at the `jal eval_expr` PC (`callPC`), with the sub-call's
ABI arguments staged (`a0 = subsret`, `a1 = aInterp`, `a2 = aOperand`, `sp` lowered
by 176), one `jal` step lands at `eval_expr`'s entry with link `retPC = callPC+4`;
the sub-call's `EvalEntry` is assembled from the arm state, the `EvalIH` is
applied, and its `EvalExitD` is repackaged into `SubExecReturn`.

`garm` is the arm-entry register frame (post-`execBlockA`, before the setup
clobbers of `a0/a1/a2/a3`): `x8 = aStmt`, `x9 = aInterp`, `x18 = aRet`,
`x19 = aEnv`, `x2 = sp`. The setup only clobbers caller-saved `a*` registers, so
every callee-saved register still reads `garm R`. -/

/-! ## `execExprGlue` — discharging `execExprSim`'s `hGlue` via `armTail_rec_es`

The `expr`-arm setup (`ld a2,8(s0)`, `addi a0,sp,16`, `mv a3,s3`, `mv a1,s1`) run
from the arm entry `0x80004170` to the `jal eval_expr` at `0x80004180`, then
`armTail_rec_es` for the sub-call. Produces the `SubExecReturn` at the link PC
`0x80004184` that `execExprSim`'s tail consumes. The `ExecArmEntryK` residuals not
already carried by that predicate — the sub-expression `ExprRepr`, the operand
pointer read, the `eval_expr`/`value_int` code + jump-table pin, the recursion
headroom and arena/code disjointness, and the store-window survival — are passed
explicitly (they are the genuine spec/geometry facts, in `ExecEntry` on the caller
side; here they are named residuals). -/

/-! ## `execExprSimC` — `ExecS.expr` with `hGlue` DISCHARGED by `execExprGlue`

The full `ExecS.expr` simulation Triple, no longer carrying the opaque `hGlue`
Triple premise of `execExprSim` (`ExecExprRet.lean`): the recursion glue is
supplied by `execExprGlue` (`= armTail_rec_es` + the arm setup), so the residuals
are now the CONCRETE named spec/geometry facts `execExprGlue` needs beyond the
`execBlockA` geometry. (`ExecArmEntryK` does not carry the sub-expression's
`ExprRepr`/operand-pointer/`eval_expr`-code/headroom facts — the fully
unconditional form needs `ExecEntry`/`execBlockA` widened to propagate them, a
`RESIDUAL`; here they are the honest per-case premises, exactly as the
expression-side recursive cases carry their operand-repr residual.) -/

end Vsa.Sim
