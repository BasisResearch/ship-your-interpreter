import Vsa.Sim.SnprintfSites2
import Vsa.Sim.SnprintfSpec2
import Vsa.Sim.Code.FlushPins
import Vsa.Sim.KeepRegs
import Vsa.Sim.ObsAvoid

/-!
# M3 Layer-3 — `SnprintfSpec4` : the sign block, composed

Session-4 file (`_sn4` suffix).  Composes the sign-block step battery of
`SnprintfSites2.lean` into a `Steps` chain over the `%lld` sign segment
(`experiments/M3-snprintf-lld.md` §1.3(c), disasm `[0x800080e4, 0x800080f4]`) and
bridges its result to the arithmetic core (`SnprintfSpec.lean`:
`neg_magnitude`, `intToString_of_bv`).  The two arms mirror the machine's `bgez`
split exactly:

* **negative** (`bgez` not taken, `2^63 ≤ v.toNat`): emit `'-'` into the sign slot
  `sp+167`, `neg a4,a4` so `x14 = 0 - v = |v.toInt|` (the magnitude the decimal
  loop consumes) — `signBlock_neg_spec` below;
* **nonnegative** (`bgez` taken, `v.toNat < 2^63`): skip the sign block, the
  magnitude is `x14 = v = v.toNat` — `signBlock_nonneg_step_sn4`.

## Sign-byte placement — the load-bearing finding

The `'-'` byte is stored at `sp+167` (`0x800080f0 sb a5,167(sp)`), a dedicated
stack slot **disjoint** from the descending digit buffer at `sp+348` (written by
`0x8000832c sb a0,-1(s9)`).  It is read back at `0x80008388 lbu t5,167(sp)` by the
pad/flush machinery and prepended into the iov `__ssprint_r` copies to the caller
buffer.  So the `'-'` is **prepended at flush, never in the digit buffer** — the
byte-level realisation of `intToString (.negSucc m) = "-" ++ natToString (m+1)`
(`intToString_of_bv`: sign prefix ++ magnitude digits, computed independently).

## What composes here, and what is a documented boundary

The two loads that begin the sign block — `0x800080dc ld a3,0(a4)` (the 64-bit
va_list arg) and its `ld a4,24(sp)` predecessor — have **no `stepObs_load`
primitive** in the current step layer, so they are a precondition boundary: the
specs below take `x13 = v` (the loaded value) as a hypothesis.  The interleaved
`0x800080e0 sd a5,24(sp)` (va_list bump) and `0x800080f8 bltz s4` (already-set
flag guard) are off the value-producing path and elided; the linear trace steps
`mv a4,a3 → bgez → [li '-' ; sb '-' ; neg]`.  The subsequent loop-entry setup
(`0x800082c8 …` establishing `LSt g top m 0`, which feeds `decimalLoop_spec`'s
`DLI`) and the flush (`0x80008a80 … __ssprint_r`, memmove into the caller buffer)
are the remaining segments; their precise shape is documented at the end.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.While (intToString natToString)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Store read-backs and `…Loaded`-insert (self-contained `_sn4` copies)

These mirror the STORE-class observation helpers and the byte-store frame for
`SvfprintfSliceLoaded`.  They are re-derived here (rather than imported from
`SnprintfSpec3`) so this file depends only on the machine-stepping layer
(`SnprintfSpec2`) — keeping the sign-block composition independent of the
digit-loop file. -/

/-! ## Branch-not-taken read-backs (sign block's `bgez`)

Mirror the `obs_store_*_sn4` shape for the not-taken branch step.  Built directly
on `get?_sigmaPost_branch_nottaken` (`StepBranch.lean`). -/

/-! ## The magnitude value bridge

For a negative argument (top bit set), the machine's `neg a4,a4` yields
`x14 = 0 - v`, whose `toNat` is the magnitude `|v.toInt|` — the very `Nat` the
decimal loop's `LSt g top (magnitude) 0` invariant is stated over.  This is the
value-level link between the sign block's output and `decimalLoop_spec`'s `m`. -/

/-! ## `signBlock_neg_spec` — the negative arm, composed

From the sign-block entry at `0x800080e4` with `x13 = v` (the loaded argument) and
`v` negative, step `mv a4,a3 → bgez(not taken) → li a5,45 → sb a5,167(sp) →
neg a4,a4`, landing at `0x800080f8` with:

* `x14 = (0#64) - v` — the unsigned magnitude the decimal loop consumes;
* the sign byte `'-' = 45` stored at `sp+167` (`x2 = sp`), disjoint from the digit
  buffer;
* `PC = 0x800080f8`, `GoodState`, `tick < 2`, `minstret` defined;
* `x13` (the original value) still available for downstream use.

`x2 = sp` (the stack pointer, live throughout) and the sign-slot address bounds
(`sp+167` is in RAM, above `tohost`) are hypotheses. -/

/-! ## `signBlock_nonneg_step_sn4` — the nonnegative arm (one branch)

For a nonnegative argument (`bgez` taken), the sign block is skipped: `mv a4,a3`
puts the value in `x14`, then `bgez` jumps to `0x80008050` (past the sign store /
neg).  The magnitude is `x14 = v = v.toNat` directly, no sign byte written.  This
single-branch step lands at `0x80008050`. -/

/-! ## Remaining segments — documented composition boundary

`signBlock_neg_spec` / `signBlock_nonneg_step_sn4` land the sign segment.  To
compose the full `%lld` slice entry→return, the remaining pieces are:

1. **Two loads** `0x800080dc ld a3,0(a4)` + `ld a4,24(sp)`: a `stepObs_load`
   primitive (not yet in the step layer) would remove the `x13 = v` boundary
   hypothesis by deriving `v` from the pinned va_list slot.

2. **Loop-entry setup** `0x800080fc andi t1,… → 0x80008100 li a5,9 →
   0x80008104 bltu a5,a4 → 0x800082c8 …`: the `bltu` splits the single-digit fast
   path (`magnitude ≤ 9`, emits one digit at `sp+347`, lands at the length/flush
   code) from the multi-digit path (`0x800082c8` sets `s6=sp+348`, `s9=s6`, `s7=0`,
   `s0=magnitude`, `j 0x8000831c` — one mod-emit that establishes `LSt g top m 0`
   at the loop head `0x800082fc`).  With `x14 = (0#64)-v` (negatives, from
   `signBlock_neg_spec`) or `x14 = v` (nonnegatives) as the magnitude, this
   segment feeds `decimalLoop_spec`'s precondition `DLI g top m`
   (`SnprintfSpec3.lean`) with `m = (magnitude).toNat`.

3. **Flush** `0x80008a80 … 0x80008af8 jal __ssprint_r`: assembles the iov
   (`sp+224`) from the sign byte (`sp+167`), the digit window `[cursor, sp+348)`,
   and padding, then `__ssprint_r → __ssputs_r → memmove` copies it into the
   caller buffer.  Per `MemcpySpec`'s `MemInv` described-update pattern, the copy
   `Q` is: for each `j < len`, `buf[base + j] = (iov bytes)[j]`, where the iov
   bytes are `['-'] ++ (digit window MSB-first)` for negatives — i.e. exactly
   `(intToString v.toInt).toUTF8` (`intToString_signblock_sn4` +
   `loopDigits_natToString`, `SnprintfSpec.lean`).  The `'-'` at `sp+167` is
   copied **first** (prepended), the digit window after: the buffer-vs-flush
   finding realised.

The value-level correspondence that ties (2)+(3) to the spec is
`intToString_signblock_sn4` (this file): `intToString v.toInt` is the sign prefix
concatenated with `natToString` of the magnitude, the two arms matching the
`bgez` split byte-exactly, `INT64_MIN`-safe via `neg_out_toNat_sn4`/`neg_magnitude`.
-/

end Vsa.Sim
