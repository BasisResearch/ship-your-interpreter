import Vsa.Sim.EvalRecCommon
import Vsa.Sim.RamReadPins
import Vsa.Sim.EvalNullSim
import Vsa.Sim.DecodeTable.Batch16Part07
import Vsa.Sim.DecodeTable.Batch14Part13
import Vsa.Sim.DecodeTable.Batch03Part22
import Vsa.Sim.ObsAvoid

/-!
# Layer 4 — M4: the `EvalE.str` simulation Triple (`evalStrSim`)

The `EvalE.str` leaf case (`ExprKind` tag `k = 1`, arm PC `0x80003414`). Mirrors
`evalNullSim` (`EvalNullSim.lean`) but with an `ld a1,8(a2)` payload load (the
64-bit `char*` string pointer → `x11`) before the shared `jal <callee>; j` arm
tail — exactly the payload-load shape of `blockC_ee` (`EvalIntSim4.lean`,
`site_80003408_ee`). The arm is three instructions:

    0x80003414: ld a1, 8(a2)     -- load the str payload pointer  (word 0x00863583)
    0x80003418: jal value_str    -- callee fills the sret buffer  (→ 0x8000281c)
    0x8000341c: j   0x800033ec    -- shared PreEpilogue entry

Structure (mirrors `EvalNullSim.lean`):

* **`site_80003414_ee`** — the `ld a1,8(a2)` payload site (identical form to int's
  `site_80003408_ee`, only the PC changes).
* **`site_80003418_ee` / `site_8000341c_ee`** — the `jal value_str` / `j` tail
  sites (mirror `site_8000342c_ee` / `site_80003430_ee`).
* **`exprRepr_str_pay64`** — the `ExprRepr.str` inversion: `read64 (a+8) = p`
  plus `CString m p s` (mirrors `exprRepr_int_pay64`).
* **`value_str_spec_full`** — the strengthened `value_str` spec adding the
  console-output invariance + sret-buffer memory frame `armTail_v` needs (the
  base `str_post` omits both). Re-runs the four `value_str` instructions.
* **`blockC_str`** — the arm `ArmEntryK … 0x80003414 Value_strLoaded (.str s) →
  PreEpilogueV … (.str s)`: runs the `ld` payload site, then `armTail_v` with
  `value_str_spec_full`.
* **`EvalStrEntry` / `evalStrSim`** — the `EvalE.str` Triple, composed
  `blockA_k (→ArmEntryK) ≫ blockC_str (→PreEpilogueV .str s) ≫ blockD_v
  (→EvalExit .str s)`.

## CString survival across the prologue spills (the new difficulty vs null/bool)

`ExprRepr … (.str s)` carries a `CString m p s` fact for the string bytes at the
payload pointer `p`. `blockA_k`'s `hexprSurv` must re-establish `ExprRepr` at the
post-prologue memory `m'` (which agrees with `m0` outside the spill window
`[SL.lo, sp)`). The `read32`/`read64` fields transfer via the `expr_stack_disjoint`
geometry (as for `.int`); the CString bytes `[p, p + s.length]` transfer via
`cstring_agreeP` provided that range is disjoint from `[SL.lo, sp)`. Since the
string pointer `p` is an arbitrary runtime value with no a-priori bound relative
to the stack, `EvalStrEntry` carries a `str_stack_disjoint` field asserting that
disjointness (the string region lives in `.rodata`/heap, disjoint from the live
`eval_expr` stack frame). It is discharged there and threaded into `hexprSurv`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc Vsa.Sim.Code
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## The `EX_STR` arm sites (@0x80003414, @0x80003418, @0x8000341c) -/

/-! ## `ExprRepr.str` inversion — the payload the `ld a1,8(a2)` loads -/

/-! ## `value_str_spec_full` — strengthened `value_str` (output + memFrame)

`str_post` (`ValueSpec.lean`) carries `ValueRepr … (.str s)` + the `NotWrittenV`
register frame, but NOT the console-output invariance or the sret-buffer memory
frame that `armTail_v` needs. This re-runs the four `value_str` instructions
(`li a5,3; sd a1,8(a0); sw a5,0(a0); ret`), mirroring `value_null_spec_full`'s
output/memFrame threading, and adds those two facts to the post. -/

/-! ## `blockC_str` — the `EX_STR` arm (`ld a1,8(a2); jal value_str; j`)

`ArmEntryK … 0x80003414 Value_strLoaded (.str s) → PreEpilogueV … (.str s)`.
Because the arm carries a payload (`x11 := p`), this cannot reuse the payload-free
`armTail_v`; it mirrors int's `blockC_ee` directly, replacing `value_int_spec`
with `value_str_spec_full` and the three arm sites with the `EX_STR` ones. The
string pointer `p` is threaded into `x11`, the sret buffer ends holding
`ValueRepr (.str s)`, and the spills/store/output survive the callee's sret write
(disjoint from `[SL.lo, sp)` and the string bytes). -/

/-! ## `StrSlotPinned` — the `EX_STR` (tag 1) jump-table slot pin

Slot at `jumpTableBase + 4` holds `bc 94 fe ff` (LE) = offset `0xfffe94bc`, and
`0x80019f58 + (Int32)0xfffe94bc = 0x80003414` (the str arm). Mirrors
`NullSlotPinned`; discharges `KindSlotPinned 1 0x80003414`.
The def itself was RELOCATED to `InterpEntry.lean` (wave 47f, `GeomFrom`) so
`EvalEntry.nbs_pins` can carry it; same name/namespace. -/

/-! ## `EvalStrEntry` — the machine precondition for the `EvalE.str` case

Mirrors `EvalNullEntry`, but carries `StrSlotPinned` + `Value_strLoaded` (with the
value_str geometry) in place of the null-specific slot/callee, `ExprRepr … (.str s)`
(kind `read32 = 1`), and — the one field new to `.str` — `str_stack_disjoint` /
`str_sret_disjoint`, placing the runtime string bytes disjoint from the live stack
frame and the sret buffer (they live in rodata/heap). These discharge the
`hexprSurv` CString survival and `blockC_str`'s `hstr`. -/

end Vsa.Sim
