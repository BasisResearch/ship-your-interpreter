import Vsa.Sim.EvalBinSim
import Vsa.Sim.EvalNegSim3
import Vsa.Sim.AddTailSites

/-!
# Layer 4 — M4 RECURSIVE case: `evalAddSim` (the `EvalE.binary .add` int pilot)

Composes the two-operand binary arm of `eval_expr` for `op = .add` on two
integer operands, in the `EvalIH` motive shape (`EvalEntry → EvalExitD`) taking
TWO induction hypotheses (LEFT `el` over `st→st'`, RIGHT `er` over `st'→st''`):

```
blockA_k        (prologue + dispatch → widened ArmEntryK @0x800034e8)
  ≫ blockB_binary (arm head + TWO recursive calls ⋈ IH_l/IH_r → TwoSubReturn @0x8000351c)
  ≫ blockC_add    (operator dispatch tail + add-int path + s3 restore
                    → PreEpilogueVD .int(wrap64 (a+b)) @0x800033ec)
  ≫ blockD_v_rec  (shared epilogue → EvalExitD .int(wrap64 (a+b)))
```

The operator dispatch tail decodes the token (`lw a2,8(s0)`; `addiw a5,a2,-11`;
`bltu a4,a5` range-check; `slli`/`srli`/`auipc`/`lw`/`jr` jump-table dispatch off
the `CSWTCH.18` operator table at `0x80019f84`) landing at the ADD-int arm
`0x80003888`, where the machine computes `add a1,s3,a7` (`s3 = vl.payload`,
`a7 = vr.payload`), wrapping at 64 bits, and calls `value_int(sret, a+b)` — so
the produced value is `.int (wrap64 (a+b))` (`add_wrap_bridge`).

`blockD_v_rec` (not a bespoke `blockD_add`) is reused: the `ld s3,1048(sp)` s3
restore sits INSIDE the add tail (before the `j 0x800033ec`), so by the epilogue
entry `x19` is already back to its entry value, and the epilogue register set is
the standard one.

RESTRICTED to `op = .add`, `vl = .int a`, `vr = .int b`. `blockC_add` carries two
register/memory residuals that a `blockB_binary`/`TwoSubReturn` widening would
discharge (they are values the head knows but `TwoSubReturn` drops):
* `hX19` — `x19 (s3) = Wl`, the LEFT payload word (read by `add a1,s3,a7`), tied
  to `a` via `read64 (sp-960) = Wl.toNat` + the LEFT `ValueRepr`;
* `hKindResp` — `read64 (sp-1088) = (2#64).toNat`, the respilled `vl.kind` word
  (read by `ld a6,0(sp)` and used in the `bne`/`beqz` int-kind guards).

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

/-! ## The `wrap64` bridge for the `add` exit value -/

/-! ## `AddSlotPinned` — the operator jump-table slot pin for `.add`

The `CSWTCH.18` operator table lives at `0x80019f84` (`= 0x80019f58 + 0x2c`);
slot `op-index` (`= binOpTok op - 11`) at `+ 4*index`, storing a signed 32-bit
offset added back to the table base. `.add` (token 11, index 0) → slot bytes
`04 99 fe ff` @ `0x80019f84`, target `0x80019f84 + (Int32)0xfffe9904 = 0x80003888`. -/

end Vsa.Sim
