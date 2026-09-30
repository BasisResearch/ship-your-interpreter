import Vsa.Sim.WordLoadData
import Vsa.Sim.EvalRecCommon
import Vsa.Sim.EntryGroundKit
import Vsa.Sim.EvalNegSim2
import Vsa.Sim.EvalNegSim3
import Vsa.Sim.BinHeadSites
import Vsa.Sim.LoadSitesTot
import Vsa.Sim.LoadSitesTotB
import Vsa.Sim.ObsAvoid
import Vsa.Sim.ArmTailFootprint

/-!
# Layer 4 — M4 RECURSIVE case: the two-operand head `blockB_binary`

The `EX_BINARY` arm of `eval_expr` (`ExprKind` tag `k = 6`, jump-table slot
bytes `90 95 fe ff` @ `0x80019f70`, arm PC `0x800034e8`). Unlike the unary
arm, it evaluates BOTH operands with two nested recursive `jal eval_expr`
calls before dispatching on the operator. Decoded machine path
(`experiments/pctrace.md` + objdump):

```
800034e8: ld   a2,16(a2)      -- a2 := e->left  (first operand ptr)
800034ec: addi a0,sp,120      -- a0 := sret_L = (sp-1088)+120 = sp-968
800034f0: sd   s3,1048(sp)    -- spill s3   → sp-40
800034f4: sd   a3,0(sp)       -- spill a3(env) → sp-1088
800034f8: jal  eval_expr      -- LEFT call; ra := 0x800034fc
-- post-left: --
800034fc: ld   a2,24(s0)      -- a2 := e->right (second operand ptr; s0 = node)
80003500: ld   a3,0(sp)       -- a3 := env (reload)
80003504: lw   a6,120(sp)     -- a6 := left-value low word (dead here; reload/respill)
80003508: addi a0,sp,144      -- a0 := sret_R = (sp-1088)+144 = sp-944
8000350c: mv   a1,s2          -- a1 := interp*
80003510: ld   s3,128(sp)     -- s3 := left-value payload (dead here)
80003514: sd   a6,0(sp)       -- respill a6 → sp-1088
80003518: jal  eval_expr      -- RIGHT call; ra := 0x8000351c
-- dispatch @0x8000351c on the operator token → add/sub/mul/…/cmp tails --
```

**`blockB_binary`** is the reusable TWO-operand head: from the dispatch landing
(`ArmEntryK` at `0x800034e8`, expression `.binary op l r`) plus the recursive
extras, it evaluates `l` (consuming `IH_l`, producing `vl` at `sp-968`) and then
`r` in the FIRST call's output state (consuming `IH_r`, producing `vr` at
`sp-944`), and lands control at `0x8000351c` with BOTH sub-values represented
(`vl@sp-968`, `vr@sp-944`), the store re-represented for the second call's output
state `st''`, the outer spill slots intact, `eval_expr` loaded, and the
`EvalExitD`-style presence/survival widenings. The two recursive calls are each
discharged by `armTail_rec` (`EvalRecCommon.lean`); the intermediate straight-line
handling threads `mcall1 → mcall2` and the left value's survival across the right
call (its buffer `[sp-968, sp-944)` is disjoint from the right call's frame, arena
and right-sret window).

Both child calls use the same stack pointer sequentially. The shared
recursive helper requires `SL.lo + 3264 ≤ sp`.

Conditional (like `blockB_unary`) only on geometry residuals bundled as
`BinExtras` + the pre-call layout facts `hMcallPop`-style.

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

/-! ## `TwoSubReturn` — the post-second-call package (both sub-values live)

The machine state a binary arm holds at `0x8000351c` (after BOTH recursive
calls return): control at the dispatch PC, `sp` still lowered, `s1 = sret`
(the OUTER result buffer), callee-saved registers restored to the call-point
frame `gpre`; the RIGHT sub-value `vr` represented at `sp-944` and the LEFT
sub-value `vl` still represented at `sp-968`; the store re-represented for the
SECOND call's output state `st''` (+ survival on `[SL.lo, SL.hi)`); the four
outer spill slots intact; `eval_expr` loaded; memory framed to the case-entry
memory `m0` outside `[SL.lo, sp)` and presence-extended. -/

/-! ## `BinExtras` — the binary-arm geometry residual bundle

Beyond `ArmEntryK` (which pins the node + entry registers + entry store) and the
two induction hypotheses, `blockB_binary` needs a bundle of pure program-structure
facts, analogous to `NegExtras` for the unary arm but doubled (two operands) and
with two extra classes:

* **operand geometry** for BOTH operands (RAM/HTIF-window; disjointness of
  each operand node from the deep stack region);
* **recursive headroom** `SL.lo + 3264 ≤ sp`, with `sp % 16 = 0`;
* **AST-vs-stack/arena disjointness** for the RIGHT operand node — it is read
  (`ld a2,24(s0)`) and its `ExprRepr` re-derived AFTER the left call returns, so it
  must survive the left sub-call's stack scribble and any arena allocation;
* **second-frame slot presence** (`hSlot2`): the four spill slots of the RIGHT
  call's own frame `[sp-1120, sp-1088)` are populated in the pre-call memory — an
  M6 Layout fact (like `hMcallPop`), stated for the entry memory and transported.

The right-operand pointer / `ExprRepr` come from the `.binary` node's `ExprRepr`
(offset 24), so they are NOT separate hypotheses — only the geometry + survival
disjointness are.  The env register `a3` at arm entry is `φf env`; the left call
needs it directly, and the right call transports it across `φf` extension. -/

/-! ## `blockB_binary` — the reusable TWO-operand recursive head -/

end Vsa.Sim
