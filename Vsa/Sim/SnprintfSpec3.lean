import Vsa.Sim.SnprintfSpec2
import Vsa.Sim.ObsAvoid

/-!
# M3 Layer-3 — `decimalLoop_spec` : closing the digit-emission loop

Session-3 file.  Builds on the machine-stepping layer of `SnprintfSpec2.lean`
(the per-site `StepObs` battery, `umoddi3_frame_spec`, `BufInv`/`bufinv_store`,
the loop-head predicate `LSt`, the arithmetic bridges) and the strengthened
`udivdi3_post` (`DivLoops.lean`, session 3) that now surfaces `∃ v, x12/x13 =
some v`.  That strengthening is what discharges the documented obligation: the
second callee call (`__umoddi3` at `0x80008324`) needs `x12`/`x13` defined at its
entry, and the first callee (`__hidden___udivdi3`) leaves them so.

Contents:

* `loop_iter` — one iteration of the do-while body `[0x800082fc, 0x80008338]`
  under the guard `m / 10^p > 9`, stepping `LSt g top m p` to `LSt g top m (p+1)`;
* `decimalLoop_spec` — the `Triple.loop` assembly: measure `(m / 10^p)`
  PC-guarded at the loop head `0x800082fc`, exit edge the `bgeu`-taken at
  `0x80008318` (when `m / 10^p ≤ 9`) landing at `0x80008358` with the complete
  `loopDigits (m+1) m = natDigits (m+1) m` digit string in the descending buffer
  (`BufInv`), digit count `s7 = p + 1`.

## Buffer / cursor arithmetic (at `LSt g top m p`)

`s9 = top − p` (cursor above last-written byte), `s10 = top − 1 − p` (next slot),
`s7 = p + 1` (count), `s0 = m / 10^p` (running value).  One iteration:
`8310 mv s9,s10` sets `s9 = top−1−p`; `832c sb a0,-1(s9)` writes digit `p+1` at
`top−1−p−1 = top−1−(p+1)` (exactly `BufInv`'s slot for index `p+1`);
`8330 addi s10,s9,-1` sets `s10 = top−1−(p+1)`; so at `LSt (p+1)`:
`s9 = top−(p+1) = top−1−p`, `s10 = top−1−(p+1)`.  ✓
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Store read-back helpers (`sigmaPost_store`)

`SnprintfSites`' `sb` site (`site_8000832c_sn`) delivers `ReadsLikePost σ'
(sigmaPost_store …)`.  These mirror the `obs_*` consumers for the STORE class,
built directly on `ReadsLikePost` + `get?_sigmaPost_store` (`StepStore.lean`). -/

/-! ## `…Loaded` preserved by a byte store above the code region

The descending buffer sits above the `tohost` window (`TopOk`), hence above **all**
code (`< 0x80008b11 < 0x8001ad10 = tohostAddr+16`).  A single byte insert at such a
key leaves every code-byte pin intact.  `getElem_transfer_sn3` is the per-byte
read-over-write; the three wrappers thread it through each `…Loaded` conjunction. -/

/-! ## Small ALU value bridges -/

/-! ## Loop-live frame across the two branch classes -/

/-! ## Guard bridge (Nat `9 < k` ⇒ `bgeu 9 k = false`) -/

/-! ## `top` window hypotheses

The descending buffer is a stack region; the `sb` site needs the write address in
RAM and disjoint from the `tohost` window.  With `m < 2^64` there are at most 20
digits, so `p ≤ 19`; the caller pins `top` in a window comfortably clearing both
bounds.  We package the constraints `loop_iter`/`decimalLoop_spec` propagate. -/

/-! ## Loop-state-preserving `__umoddi3` spec

`umoddi3_frame_spec` (`SnprintfSpec2`) preserves only `NotWrittenL` registers,
which **excludes** the loop-state set `{x8, x22, x23, x25, x26, x27}`.  Those
registers are nonetheless preserved by `__umoddi3` physically (the wrapper writes
only `x5, x10, x11`, and the inner `__hidden___udivdi3` preserves them via its
`NotWritten` frame — `NotWritten` does **not** exclude `x8`/…).  We reprove the
wrapper here threading those six registers explicitly, so the decimal loop can
re-establish `LSt` after the mod call. -/

/-! ## One loop iteration (`loop_iter`)

From `LSt g top m p` with guard `m / 10^p > 9`, step the 16-instruction body in
program order to `LSt g top m (p+1)`.  The two callee calls are composed via
`udivdi3_spec` (now surfacing `x12`/`x13`) and `umoddi3_frame_spec`. -/

/-! ## Exit iteration (`loop_exit`)

From `LSt g top m p` with the exit guard `m / 10^p ≤ 9`, step the head prefix
`0x800082fc … 0x80008318` where the `bgeu` at `0x80008318` is now **taken** (`9 ≥
m/10^p`), landing at `0x80008358` with the complete emitted digit buffer
`BufInv top m (p+1)` and digit count `s7 = p + 1`.  No `__umoddi3`, no `sb`: the
final digit was already emitted at the previous iteration (do-while shape). -/

/-! ## The `Triple.loop` assembly — `decimalLoop_spec`

Invariant `DLI`: at the loop head `0x800082fc` in some `LSt g top m p`.  Guard
`DLB`: additionally `m / 10^p > 9` (the `bgeu` at `0x80008318` will be *not*
taken).  Measure `DLMu`: `m / 10^p` at the head (`0` off it) — strictly decreasing
each iteration since `m / 10^(p+1) < m / 10^p` for `m / 10^p > 9`.  `Triple.loop`
delivers `LSt p ∧ ¬(m/10^p > 9)`, i.e. `LSt p` with `m/10^p ≤ 9`; `loop_exit`
then steps the head prefix to `0x80008358` with the complete digit buffer. -/

end Vsa.Sim
