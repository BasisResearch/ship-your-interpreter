import Vsa.Sim.RamReadPins
import Vsa.Sim.EvalRecCommon
import Vsa.Sim.EntryGroundKit
import Vsa.Sim.DecodeTable.Batch05Part16
import Vsa.Sim.DecodeTable.Batch09Part03
import Vsa.Sim.DecodeTable.Batch14Part06
import Vsa.Sim.ObsAvoid

/-!
# Layer 4 — M4 pilot RECURSIVE case: the `EX_UNARY` arm head (`blockB_unary`)

The FIRST recursive `EvalE` case walk: the `EX_UNARY` arm of `eval_expr`
(`ExprKind` tag `k = 8`, jump-table slot bytes `88 96 fe ff` @ `0x80019f78`,
arm PC `0x800035e0`). Decoded machine path (`experiments/pctrace.md`):

```
800035e0: ld   a2,16(a2)      -- a2 := e->as.unary.operand
800035e4: addi a0,sp,144      -- a0 := sub-result buffer (sp' + 144 = sp - 944)
800035e8: jal  80003164       -- RECURSIVE eval_expr(subsret, in, operand, env)
-- post-call (op dispatch): --
800035ec: lw   a4,8(s0)       -- op (T_MINUS = 12 → neg @ 0x800039ac; else not)
…
800039ac..800039dc (neg):     -- kind check (VAL_INT = 2), neg a1,a1,
                              -- mv a0,s1, jal value_int, j 0x800033ec
```

This module lands the arm HEAD: the three sites (`ld`/`addi`/`jal`) and
**`blockB_unary`** — from the dispatch landing (`ArmEntryK` at `0x800035e0`
plus the recursive-case extras `blockA_k` does not yet expose) through the
payload load, the sub-buffer setup, and the recursive call *composed with the
induction hypothesis* (`armTail_rec`, `EvalRecCommon.lean`), to
`SubEvalReturn`: control back at `0x800035ec` with the sub-value represented
at `sp - 944`, the store re-represented for the sub-derivation's post state,
the outer frame's spill slots intact, and `eval_expr` still loaded.

`blockB_unary` is op-agnostic (`neg` and `not` share the arm head; the op is
inspected only post-call). The post-call `neg` tail
(`0x800035ec–f8, 0x800039ac–dc` + `value_int` + `blockD_v`) is the next
module (`blockC_neg`); the residuals for wiring `blockA_k` into this case are
recorded in `memory/m4-recursive-cases.md`.

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

/-! ## The three `EX_UNARY` arm-head sites (@0x800035e0/e4/e8) -/

/-! ## The unary-arm callee bundle

The dispatch must carry through the spills everything the ARM (not just one
`value_*` callee) needs loaded: the sub-call's `EvalEntry` demands
`Value_intLoaded` AND the `EX_INT` jump-table slot (`IntSlotPinned` — the
operand may be an int literal), and the `neg` tail itself calls `value_int`.
This is the `calleeLoaded` instantiation for `blockA_k` at this arm. -/

/-! ## `blockB_unary` — arm head + recursive call, composed with the IH

`ArmEntryK` (at arm PC `0x800035e0`, callee bundle `UnaryArmCallee`, expression
`.unary op esub`) plus the RECURSIVE-CASE EXTRAS — facts the current
`blockA_k`/`ArmEntryK` do not yet thread (recorded as the `ArmEntryK` widening
residual): the live `a1 = interp*` register, the call-point ghost frame `gpre`,
the operand node's `ExprRepr` + geometry, the extra 1088-byte stack headroom,
and the arena/code/table disjointness facts. Output: `SubEvalReturn` at the
link PC `0x800035ec` with sub-result buffer `(sp - 1088) + 144`, plus the
memory frame of the pre-call memory against the case entry memory `m0`. -/

end Vsa.Sim
