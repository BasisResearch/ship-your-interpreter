import Vsa.Sim.EvalIntSim4
import Vsa.Sim.DecodeTable.Batch16Part01
import Vsa.Sim.DecodeTable.Batch14Part09
import Vsa.Sim.ObsAvoid

/-!
# Layer 4 — M4: the `EvalE.null` simulation Triple (`evalNullSim`)

The second M4 leaf case (after `EvalE.int`). Mirrors `evalIntSim`
(`EvalIntSim4.lean`) but for the `EX_NULL` arm (`ExprKind` tag `k = 3`, arm PC
`0x8000342c`). The arm is only two instructions — `jal value_null` (no payload
load; `null` takes no argument) and `j 0x800033ec` — so its block C is exactly
the shared `armTail_v` (`EvalSimCommon.lean`) instantiated at the `value_null`
callee and produced value `.null`.

Structure:

* **`value_null_spec_full`** — the strengthened `value_null` spec: from the null
  callee precondition it runs to a post carrying (besides `ValueRepr … .null`)
  the console-output and memory-frame facts `armTail_v` needs (the base
  `value_null_spec`'s `null_post` omits them). Re-runs the three `value_null`
  instructions, mirroring `value_int_spec`.
* **`blockC_null`** — the arm `ArmEntryK … 0x8000342c Value_nullLoaded .null →
  PreEpilogueV … .null`, via `armTail_v` with `value_null_spec_full` and the two
  arm sites `site_8000342c_ee` / `site_80003430_ee` (proved here from
  `Eval_exprLoaded`, mirroring the int arm's `jal`/`j` sites).
* **`EvalNullSimGoal`/`evalNullSim`** — the `EvalE.null` Triple, composed
  `blockA_k (→ArmEntryK) ≫ blockC_null (→PreEpilogueV .null) ≫ blockD_v
  (→EvalExit .null)`. Null entry predicate `EvalNullEntry` mirrors `EvalEntry`
  but carries `KindSlotPinned 3 0x8000342c` + `Value_nullLoaded` in place of the
  int-specific slot/callee.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc Vsa.Sim.Code
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## The two `EX_NULL` arm sites (@0x8000342c, @0x80003430)

Mirror the int arm's `site_8000340c_ee` (jal) and `site_80003410_ee` (j), with
the null arm's PCs/words: `jal value_null` (`bc0ff0ef`, imm `0x1ff3c0`, target
`0x800027ec`) and `j 0x800033ec` (`fbdff06f`, imm `0x1fffbc`). -/

/-! ## `value_null_spec_full` — strengthened `value_null` (output + memFrame)

`null_post` (`ValueSpec.lean`) carries `ValueRepr … .null` + the `NotWrittenV`
register frame, but NOT the console-output invariance or the sret-buffer memory
frame that `armTail_v` needs. This re-runs the three `value_null` instructions
(`sw zero,0(a0); sd zero,8(a0); ret`), mirroring `value_int_spec`'s output/memFrame
threading, and adds those two facts to the post. -/

/-! ## `blockC_null` — the `EX_NULL` arm via `armTail_v`

`ArmEntryK … 0x8000342c Value_nullLoaded .null → PreEpilogueV … .null`, closing
the arm through `armTail_v` at the `value_null` callee. No payload load precedes
the tail (null takes no argument), so block C *is* the tail. -/

/-! ## `NullSlotPinned` — the `EX_NULL` (tag 3) jump-table slot pin

The slot at `jumpTableBase + 12` holds `d4 94 fe ff` (LE) = offset `0xfffe94d4`,
and `0x80019f58 + (Int32)0xfffe94d4 = 0x8000342c` (the null arm). Mirrors
`IntSlotPinned`; discharges `KindSlotPinned 3 0x8000342c` for the loaded image.
The def itself was RELOCATED to `InterpEntry.lean` (wave 47f, `GeomFrom`) so
`EvalEntry.nbs_pins` can carry it; same name/namespace. -/

/-! ## `EvalNullEntry` — the machine precondition for the `EvalE.null` case

Mirrors `EvalEntry` (`InterpEntry.lean`), but carries `NullSlotPinned` +
`Value_nullLoaded` (with the value_null geometry) in place of the int-specific
`int_slot`/`value_int_code`, and `ExprRepr … .null` (`read32 = 3`). -/

end Vsa.Sim
