import Vsa.Sim.RamReadPins
import Vsa.Sim.EvalNullSim
import Vsa.Sim.EvalRecCommon
import Vsa.Sim.DecodeTable.Batch16Part04
import Vsa.Sim.DecodeTable.Batch14Part10
import Vsa.Sim.DecodeTable.Batch03Part22
import Vsa.Sim.ObsAvoid

/-!
# Layer 4 — M4: the `EvalE.bool` simulation Triple (`evalBoolSim`)

The third M4 leaf case (after `EvalE.int` and `EvalE.null`). Mirrors `evalNullSim`
(`EvalNullSim.lean`) but for the `EX_BOOL` arm (`ExprKind` tag `k = 2`, arm PC
`0x80003420`). The arm is three instructions — `lw a1,8(a2)` (the 32-bit bool
word → `x11`), `jal value_bool` and `j 0x800033ec` — so block C is the payload
`lw` site followed by the shared `armTail_v` (`EvalSimCommon.lean`) instantiated
at the `value_bool` callee (from PC `0x80003424`) and produced value `.bool b`.

Structure (mirrors `EvalNullSim.lean` + the int payload-load site from
`EvalIntSim4.lean`):

* **`site_80003420_ee`** — the payload-load site (`lw a1,8(a2)`, 32-bit signed →
  `x11`), mirroring the int arm's `site_80003408_ee` (`ld a1,8(a2)`) but 4-byte.
* **`value_bool_spec_full`** — the strengthened `value_bool` spec: from the bool
  callee precondition it runs to a post carrying (besides `ValueRepr … (.bool _)`)
  the console-output and memory-frame facts `armTail_v` needs (`bool_post` omits
  them). Re-runs the five `value_bool` instructions, mirroring `value_bool_spec`.
* **`blockC_bool`** — the arm `ArmEntryK … 0x80003420 Value_boolLoaded (.bool b) →
  PreEpilogueV … (.bool b)`: runs the payload `lw`, then `armTail_v` at the `jal`
  PC `0x80003424` with `value_bool_spec_full` and the two tail sites
  `site_80003424_ee` / `site_80003428_ee`.
* **`EvalBoolSimGoal`/`evalBoolSim`** — the `EvalE.bool` Triple, composed
  `blockA_k (→ArmEntryK) ≫ blockC_bool (→PreEpilogueV .bool b) ≫ blockD_v
  (→EvalExit .bool b)`. Bool entry predicate `EvalBoolEntry` mirrors `EvalNullEntry`
  but carries `BoolSlotPinned 2 0x80003420` + `Value_boolLoaded` and `ExprRepr …
  (.bool b)` in place of the null-specific slot/callee/expr.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc Vsa.Sim.Code
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## The payload-load site `site_80003420_ee` (@0x80003420, `lw a1,8(a2)`)

Mirrors the int arm's `site_80003408_ee` (`ld a1,8(a2)`), but the bool payload is
a 32-bit signed word (`lw`, funct3=010), so it uses `exec_lw` (as in the kind-load
`site_80003164_ee`) writing `x11` from `x12 + 8`. The result is
`sign_extend (b3 ++ b2 ++ b1 ++ b0 : BitVec 32)`. -/

/-! ## The two `EX_BOOL` tail sites (@0x80003424, @0x80003428)

Mirror the null arm's `site_8000342c_ee` (jal) and `site_80003430_ee` (j), with the
bool arm's PCs/words: `jal value_bool` (`bd4ff0ef`, imm `0x1ff3d4`, target
`0x800027f8`, link `0x80003428`) and `j 0x800033ec` (`fc5ff06f`, imm `0x1fffc4`). -/

/-! ## `Value_boolLoaded` survives an 8-byte spill write

Mirror `loaded_null_writeMap8`, for `value_bool`'s code `[0x800027f8, 0x8000280c)`.
Needed by `blockA_k`'s `hcalleeSurv` (the prologue `sd` spills). -/

/-! ## `value_bool_spec_full` — strengthened `value_bool` (output + memFrame)

`bool_post` (`ValueSpec.lean`) carries `ValueRepr … (.bool _)` + the `NotWrittenV`
register frame, but NOT the console-output invariance or the sret-buffer memory
frame that `armTail_v` needs. This re-runs the five `value_bool` instructions
(`snez a1,a1; li a5,1; sw a1,8(a0); sw a5,0(a0); ret`), mirroring
`value_null_spec_full`'s output/memFrame threading, and adds those two facts to the
post. -/

/-! ## The `.bool` payload value bridge

The `lw a1,8(a2)` loads `payV = sign_extend (word32)` where `word32.toNat =
read32 ment (aExpr+8)`. `value_bool` produces `.bool (payV != 0#64)`. From
`ExprRepr ment aExpr (.bool b)`: for `b = true` the payload word is nonzero, for
`b = false` it is `0`. Since `sign_extend` preserves zero-ness of the 32-bit word,
`(payV != 0#64) = b`. -/

/-! ## `blockC_bool` — the `EX_BOOL` arm: `lw`, then `armTail_v`

`ArmEntryK … 0x80003420 Value_boolLoaded (.bool b) → PreEpilogueV … (.bool b)`.
Runs the payload `lw a1,8(a2)` (arm entry 0x80003420 → 0x80003424), then closes
the two-instruction tail `jal value_bool; j 0x800033ec` through `armTail_v` at the
jal PC `0x80003424` with `value_bool_spec_full`. -/

/-! ## `BoolSlotPinned` — the `EX_BOOL` (tag 2) jump-table slot pin

The slot at `jumpTableBase + 8` holds `c8 94 fe ff` (LE) = offset `0xfffe94c8`,
and `0x80019f58 + (Int32)0xfffe94c8 = 0x80003420` (the bool arm). Mirrors
`NullSlotPinned`; discharges `KindSlotPinned 2 0x80003420` for the loaded image.
The def itself was RELOCATED to `InterpEntry.lean` (wave 47f, `GeomFrom`) so
`EvalEntry.nbs_pins` can carry it; same name/namespace. -/

/-! ## `EvalBoolEntry` — the machine precondition for the `EvalE.bool` case

Mirrors `EvalNullEntry` (`EvalNullSim.lean`), but carries `BoolSlotPinned` +
`Value_boolLoaded` (with the value_bool geometry) in place of the null-specific
`null_slot`/`value_null_code`, and `ExprRepr … (.bool b)` (`read32 = 2`). -/

end Vsa.Sim
