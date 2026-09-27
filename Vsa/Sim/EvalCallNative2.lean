import Vsa.Sim.EvalCallNative
import Vsa.Sim.NativeAssertSites
import Vsa.Sim.ValueTruthySpec
import Vsa.Sim.OmegaHelpers2
import Vsa.Sim.ValueSpec
import Vsa.Sim.ReprCopy
import Vsa.Sim.EvalNotSim
import Vsa.Sim.EvalNullSim
import Vsa.Sim.ObsAvoid
import Vsa.Sim.StepFrameOut

/-!
# Layer 4 — M4: discharging the `native_assert` INTERNAL run (`Call.assertOk`)

`NativeAssertOkSpec` (`EvalCallNative.lean`) bundles the WHOLE native branch of
`Call.assertOk`: the `fv`-kind dispatch (`0x80003254`), the native arm marshal +
indirect `jalr a6` (`0x800039e0`), the `native_assert` internal run
(`0x80002df4 … ret`), and the return to the epilogue join (`0x800033ec`). This
file lands the CORE, reusable piece: the `native_assert` internal run itself,
threaded straight-line against the 33-site battery (`NativeAssertSites.lean`)
composing `value_truthy_spec` and `value_null_spec` — exactly the `blockC_not`
(Value copy → `value_truthy` → tail value-call) discharge shape.

`nativeAssertInternal` is a `Triple` in `native_assert`'s OWN 80-byte frame:
from the entry (`0x80002df4`, ABI `a0 = sret`, `a2 = argc`, `a3 = args base`,
with `args[0]` a `ValueRepr` of a TRUTHY `v` and `argc ∈ {1,2}`) to the `ret`
(`0x80002e74`) with `.null` written into the `sret` buffer (`ValueRepr … sret
.null`), the console output UNCHANGED, and the callee-saved registers + frame
restored.

The truthy machine path is gated by the `Call.assertOk` premises: `argc ∈ {1,2}`
(⇒ `argc-1 ∈ {0,1}` ⇒ the arity `bltu 1,argc-1` is NOT taken) and `v.truthy =
true` (⇒ `value_truthy` returns non-zero ⇒ the `beqz` at `0x80002e50` is NOT
taken and falls through to the `value_null` write). The falsy / arity-error arms
call `runtime_error` and are underivable in the spec (M5), matching
`Call.assertOk`.

STILL RESIDUAL (the dispatch/`jalr` wrapper): composing this internal run into
`NativeAssertOkSpec`'s `SegEntry → SegExit` shape needs the `fv`-kind dispatch
decode, the native-arm marshal, and the indirect `jalr a6 = N.addr .assert`
(`stepObs_jalr`) plus the `SegEntry` `StoreRepr → ValueRepr(.native .assert)` /
arg-vector bridge — deferred here.

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

set_option maxHeartbeats 12000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Region facts for the `native_assert` internal run

`fsp` is `native_assert`'s stack pointer at entry; the prologue subtracts 80,
so the callee frame is `[fsp-80, fsp)` and the two nested callees
(`value_truthy`/`value_null`) run with `sp = fsp-80`. The truthy arg buffer is
`fsp+16 … fsp+40` (24 bytes); the frame spills live in `[fsp-80, fsp)`. The
`sret` buffer (`.null` return target) is 24 bytes. All writes must be disjoint
from the three code regions:
* `native_assert` `[0x80002df4, 0x80002ed4)`
* `value_truthy`  `[0x8000282c, 0x8000285c)`
* `value_null`    `[0x800027ec, 0x800027f8)`
and `sret` must be disjoint from the frame + truthy buffer (so the null write
does not clobber the reloaded spills). -/

/-! ## The three code regions survive the frame / buffer / sret stores -/

/- `loaded_null_agreeP` RELOCATED to `InterpEntry.lean` (wave 47f, `GeomFrom`);
same name/namespace. -/

/-! ## `nativeAssertInternal` — the `native_assert` internal run

From the entry (`0x80002df4`) to the `ret` (`0x80002e74`). The truthy path
(`v.truthy = true`, `argc ∈ {1,2}`) copies `args[0] = v` into the truthy arg
buffer, `value_truthy` returns non-zero, the `beqz` falls through, `value_null`
writes `.null` into the `sret` buffer, and the epilogue restores the frame and
returns. Console output unchanged; `.null` produced at `sret`. -/

end Vsa.Sim
