import Vsa.Sim.SnprintfSpec13
import Vsa.Sim.DecodeTable.Batch16Part11
import Vsa.Sim.DecodeTable.Batch08Part03
import Vsa.Sim.DecodeTable.Batch06Part25
import Vsa.Sim.DecodeTable.Batch06Part14
import Vsa.Sim.DecodeTable.Batch05Part30
import Vsa.Sim.DecodeTable.Batch02Part31
import Vsa.Sim.DecodeTable.Batch02Part12
import Vsa.Sim.ObsAvoid

/-!
# M3 Layer-3 — `SnprintfSpec14` : `%`-format jump-table **slot-address arithmetic** + full dispatch (`_da`)

`SnprintfSpec13.parseDispatchHop_spec` verifies the *load-and-transfer* tail of the
`svfprintf` conversion dispatch (`0x800077b4 → handler`), but takes as a *given*
that the slot address `base + 4*k` is already sitting in `x15`.  This module
supplies the missing **upstream slot-address arithmetic** — the `sext.w`/`addiw`/
`bltu`/`slli`/`srli`/`add` sequence at `[0x80007798, 0x800077b4)` that turns the
conversion **character** (in `s8 = x24`) into that slot address — and composes it
with `parseDispatchHop_spec` to obtain a single `Steps` chain from the dispatch
loop head `0x80007798` **through the jump table** to the conversion handler entry.

## Executed footprint `[0x80007798, 0x800077bc]` (the dispatch block)

```
  7798: addi  s9,s9,1        s9  += 1                 (loop-counter bump, dead here)
  779c: sext.w s8,s8         s8  := sext32(s8)        (char, canonicalized)
  77a0: addiw a5,s8,-32      a5  := sext32(char-32)   (jump-table index k = ch-32)
  77a4: bltu  s10,a5,+..     if 90 < k goto out-of-range   ← NOT taken (k ≤ 90)
  77a8: slli  a4,a5,0x20     a4  := a5 <<< 32
  77ac: srli  a5,a4,0x1e     a5  := a4 >>> 30 = 4*k   ← the (k<<32)>>30 = 4*k trick
  77b0: add   a5,a5,s6       a5  := base + 4*k        (the slot address)
  --> 77b4  (parseDispatchHop_spec: lw / add / jr → handler)
```

The load-bearing bitvector fact is `slotIndexShift`:
`((ofNat 64 k) <<< 32) >>> 30 = ofNat 64 (4*k)` for `k < 2^30` — i.e. the machine
`srli (slli a5 0x20) 0x1e` computes `4*k` exactly (the compiler's byte-scaled
table index, since each `.rodata` slot is a 4-byte signed offset).

## Register preconditions (honest, from the parse loop upstream)

The dispatch block reads four live registers set by the (still-unformalized)
`%`-parse scan loop just before `0x80007798`:

* `x24 (s8)` — the **conversion character** `ch` (for the `%lld` path, `'l' = 0x6c`);
* `x26 (s10)` — the dispatch **upper bound** `90` (`'Z'`), set by `parseInit_spec`;
* `x22 (s6)` — the jump-**table base** `0x8001a0fc = parseTableBase`, set by
  `parseInit_spec` (its `auipc`/`addi` pair);
* `x25 (s9)` — the loop counter (read + bumped at `0x80007798`; its value is
  irrelevant to the dispatch and left existential).

`parseInit_spec` (`SnprintfSpec12`) *establishes* `x22 = parseTableBase`,
`x26 = 90`, and `x24 = zext(format[1])` at its exit `0x80007798`, but its stated
postcondition currently surfaces only `x2/x20/x6`.  Chaining `parseInit → this`
end-to-end therefore requires widening `parseInit_spec`'s post to additionally
surface `x22`, `x24`, `x26` (and, for the concrete `%lld` path, pinning
`format[1] = 'l'` so `x24 = ofNat 0x6c`).  That widening is mechanical (three more
`obs_alu_other` threads per step) but is left to a follow-up; this module states
the three register facts as explicit entry hypotheses and documents their origin.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## The reusable slot-index bitvector lemma `slotIndexShift`

`srli (slli a5 0x20) 0x1e = 4*a5` when the index fits in 30 bits.  Concretely,
`((ofNat 64 k) <<< 32) >>> 30 = ofNat 64 (4*k)` for `k < 2^30`.  This is the exact
arithmetic the compiler emits to scale a jump-table index into a byte offset
(4-byte slots): shift left 32 then right 30 nets a left-shift by 2 (`×4`) *after*
zeroing the high 32 bits, so it works for any 32-bit-clean index.  Reused by every
`.rodata` jump-table dispatch (parse, `eval_expr`, `value_equal`). -/

/-! ## `parseDispatchArith_l_spec` — slot-address arithmetic for `'l'`

`0x80007798 → 0x800077b4`: from the dispatch loop head with the character `'l'`
(`0x6c`) in `x24`, table base in `x22`, and upper bound `90` in `x26`, run the
`sext.w`/`addiw`/`bltu`(not-taken)/`slli`/`srli`/`add` block, landing at the slot
load `0x800077b4` with `x15 = ofNat(parseTableBase + 4*(0x6c-32))` — exactly the
entry `parseDispatchHop_spec` requires. -/

/-! ## `parseDispatch_l_full_spec` — full `%lld` dispatch `0x80007798 → 0x80008534`

Composes `parseDispatchArith_l_spec` (slot-address arithmetic) with
`SnprintfSpec13.parseDispatch_l_spec` (load + transfer through the jump table) to
obtain a single `Steps` chain from the dispatch loop head `0x80007798` through the
`.rodata` jump table to the `'l'` length-modifier conversion handler entry
`0x80008534`.  The frame pointer `x2` is preserved throughout. -/

end Vsa.Sim
