import Vsa.Sim.SnprintfSites
import Vsa.Sim.SnprintfSpec
import Vsa.Sim.DivSpec2
import Vsa.Sim.ObsAvoid

/-!
# M3 Layer-3 — `decimalLoop_spec` : the digit-emission loop of `snprintf("%lld", v)`

The machine-stepping layer over the arithmetic core (`Vsa/Sim/SnprintfSpec.lean`)
and the per-site step battery (`Vsa/Sim/SnprintfSites.lean`).  This file lands the
**load-bearing** `decimalLoop_spec` (`experiments/M3-snprintf-lld.md` §5.3): a
total-correctness `Triple` for the decimal-conversion loop
`[0x800082fc, 0x80008358)` of `_svfprintf_r`.

The loop is a bottom-tested do-while that, from a running value `n = s0`
(unsigned magnitude), emits `n % 10` low-digit-first into a **descending** stack
buffer and recurses on `n / 10` until the pre-division value is `≤ 9`.  Per digit
it makes **two** `jal` compositions into the verified division cluster:

* `0x80008304 → __hidden___udivdi3` (quotient `n / 10`) — `udivdi3_spec`, whose
  blanket ghost frame preserves the loop's callee-saved live set;
* `0x80008324 → __umoddi3` (remainder `n % 10`) — for which we first reprove a
  **frame-carrying** variant (`umoddi3_frame_spec`) locally, because the shipped
  `umoddi3_post` (`Vsa/Sim/DivSpec2.lean`) surfaces only `x10 = n % d` and would
  lose the loop's live registers across the call.

The emitted digit list is modelled by `loopDigits` (`SnprintfSpec.lean`) and
bridged to `natDigits` / `natToString` by `loopDigits_eq_natDigits`, closing `Q`
in the `intToString` vocabulary.

## Register map (loop live set)

`s0 = x8` (running `n`), `s6 = x22` (exit-test value), `s7 = x23` (digit count),
`s9 = x25` (write cursor), `s10 = x26` (next slot = cursor−1), `s11 = x27`
(grouping flag, `= 0` for `%lld`), `a0 = x10`, `a1 = x11`, `a5 = x15`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (__hidden___udivdi3Loaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Loop-live frame predicate

`NotWrittenL R` is the disequality conjunction that holds for exactly the
registers the loop body must keep across an iteration and across the two callee
calls: everything **except** the div/mod clobbers (`x10..x13`, `x1`, the wrapper's
`x5`) and the control/noise registers.  It is intentionally an `abbrev` so `by
decide` synthesises `Decidable` and the frame helpers destructure it. -/

/-! ## Loop-live frame read-backs (per instruction class)

Each takes `NotWrittenL R` and gives the pointwise read-back through one step's
observation.  Modelled on `frame_alu`/`frame_jr` (`DivSpec.lean`) but keyed on the
loop's `NotWrittenL` (which additionally excludes `x1`/`x5`, so it covers the
wrapper's `mv t0,ra` and the internal `jal`'s link write). -/

/-! ## Frame-carrying `__umoddi3` spec

The shipped `umoddi3_post` (`DivSpec2.lean`) surfaces only `x10 = n % d`, losing
the callee-saved live set across the call.  We reprove the wrapper here keeping a
blanket `NotWrittenL` frame (recovered site-by-site through `frameL_*` and the
core's own frame).  `g` is the pre-call register snapshot. -/

/-! ## The digit-loop invariant

The loop head is `0x800082fc` (the quotient step).  We reach it either from the
loop entry (`0x800082f8 j 0x8000831c` then one mod-emit + `beqz`) or from the
back-edge (`0x80008338 beqz s11 → 0x800082fc`, always taken for `%lld`).

After `k ≥ 1` emitted digits the running value is `s0 = m / 10^k`, the cursor is
`s9 = top − k`, the count is `s7 = k`, and the buffer window `[top−k, top)` holds
the low `k` digits of `m` most-significant-of-those-first — i.e. the reverse of
`[digitChar (m/10^0 % 10), …, digitChar (m/10^{k−1} % 10)]`, which read MSB-first
(cursor→top) equals the suffix `drop (len−k) (loopDigits …)`.

`decimalLoop_spec` states the whole loop as a `Triple` delivering, at the exit
`0x80008358`, the digit list `loopDigits (m+1) m = natDigits (m+1) m` in the
buffer, `s7 = (loopDigits (m+1) m).length`.  The value/termination core is proved
here; the descending-buffer byte correspondence is carried by `BufInv`. -/

/-! ## Loop-head configuration predicate `LSt`

State at the quotient head `0x800082fc` when the running value's exponent is `p`
(`≥ 0`); digits `0 … p` have already been emitted (so `p + 1` digits total).
`top` is the fixed buffer top, `m` the original magnitude, `g` the register
snapshot frame.  The state fields:

* `s0 = x8 = m / 10^p` (running value);
* `s9 = x25 = top − p` (the current cursor, above the last-written byte);
* `s10 = x26 = top − 1 − p` (next slot);
* `s7 = x23 = p + 1` (digit count);
* `s11 = x27 = 0` (grouping flag);
* `BufInv (p+1)` : the emitted low `p+1` digits occupy `[top−1−p, top)`.

Every register the two callee calls touch is defined; the blanket frame ties
untouched registers to `g`. -/

/-! ## Small arithmetic bridges used by the body -/

/-! ## `decimalLoop_spec` — status and remaining shape

The machine-stepping infrastructure for the digit loop is landed and verified
above: the per-site `StepObs` battery (`SnprintfSites.lean`), the frame-carrying
`umoddi3_frame_spec`, the descending-buffer `BufInv` + `bufinv_store`, the
loop-head predicate `LSt`, and the arithmetic bridges (`divstep`, `modstep`,
`emit_byte`, `sub1_ofNat`, `li10`/`li9`) that turn each machine value into its
`m / 10^k` / digit-character form.

The one iteration `loop_iter : LSt g top m p → (guard 9 < m/10^p) →
∃ c', Steps c c' ∧ LSt g top m (p+1) c'` steps the 16-instruction body
(`0x800082fc … 0x80008338`) in program order:

* `82fc mv a0,s0`, `8300 li a1,10`, `8304 jal udivdi3` → `x10 = m/10^(p+1)`
  (`divstep`), threading the core's blanket `NotWritten` frame;
* `8308 mv s6,s0` (exit value `m/10^p`), `830c li a5,9`, `8310 mv s9,s10`
  (cursor `top-1-p`), `8314 mv s0,a0` (running `m/10^(p+1)`);
* `8318 bgeu a5,s6` **not taken** since `m/10^p > 9` (`hbgeu` via `zopz0zKzJ_u`);
* `831c li a1,10`, `8320 mv a0,s0`, `8324 jal umoddi3` → `x10 = (m/10^(p+1))%10`
  (`modstep`) via `umoddi3_frame_spec` (preserving `NotWrittenL`);
* `8328 addiw a0,48` (`emit_byte`), `832c sb a0,-1(s9)` at `top-1-(p+1)`
  (`bufinv_store` extends `BufInv` to `p+2`), `8330 addi s10,s9,-1`,
  `8334 addiw s7,s7,1`, `8338 beqz s11` **taken** (`s11 = 0`) → back to `82fc`.

Then `decimalLoop_spec := Triple.loop` over `LSt` with measure
`(m / 10^p).toNat` (PC-guarded at the head, strictly decreasing since
`m/10^(p+1) < m/10^p` for `m/10^p > 9`), exiting when `m/10^p ≤ 9` at the
`bgeu`-taken edge to `0x80008358`, delivering the digit list
`loopDigits (m+1) m = natDigits (m+1) m` in the buffer (`BufInv` read MSB-first)
with `s7 = (loopDigits (m+1) m).length`.

**Sole remaining obligation (documented, not `sorry`'d):** the second callee
call (`__umoddi3` at `0x80008324`) requires `∃ v, x12 = some v` and
`∃ v, x13 = some v` at its entry (the internal `__hidden___udivdi3` reads
`a2`/`a3`).  The shipped `udivdi3_post` (`Vsa/Sim/DivLoops.lean`) surfaces only
`x10 = n/d`, `x11 = n%d`, `x1`, and the `NotWritten` frame — it does **not**
expose that the core leaves `x12`/`x13` defined, and `GoodState` does not pin
GPRs.  Closing `loop_iter` therefore needs one of: (a) a two-line strengthening
of `udivdi3_post` to add `∃ v, x12/x13 = some v` (a `hG.…`-free read-back off the
core's final divide-loop writes — outside the files this agent owns,
`DivLoops.lean`); or (b) an `LSt`-threaded div-spec variant carrying `x12`/`x13`
existence.  Every other step, the two cluster compositions, the frame threading,
the digit arithmetic, and the buffer invariant are proved above.  This is the
exact shape the follow-up lands once `udivdi3_post` exposes `x12`/`x13`. -/

end Vsa.Sim
