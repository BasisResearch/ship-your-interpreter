import Vsa.Sim.SnprintfSpec7

/-!
# M3 Layer-3 — `SnprintfSpec8` : sign block → PRINT entry, composed (`_ep`)

This module glues the two already-verified halves of the negative-`%lld`
digit-formatting path into a **single** `Triple` covering the executed footprint

  `[0x800080e4, 0x8000782c)`   (sign block → split → loop entry → decimal loop
                                → exit restore → three hops → PRINT entry)

for the negative case (`v < 0`, magnitude `> 9`):

* `signToDigits_neg_spec` (`SnprintfSpec6`) : `0x800080e4 → 0x80008358`, emitting
  the complete decimal digit buffer and leaving the `'-'` sign byte at `sp+167`;
* `exitToPrint_spec` (`SnprintfSpec7`) : `0x80008358 → 0x8000782c`, the restore
  block (five spill reloads, `len = top − cursor`, width test, the sign-byte
  read-back into `t5`, `a6 := len+1`) and the three hops.

The composition is a `Steps.trans`.  Two of `exitToPrint_spec`'s hypotheses are
**discharged here from what `signToDigits_neg_spec` already delivers**:

* `hsb`  — the sign byte at `sp+167` : this is literally
  `signToDigits_neg_spec`'s last post-conjunct, with `sb := '-'`;
* `hsbne` — the sign byte is non-zero : `'-' = 0x2d ≠ 0`, closed by `decide`.

The remaining `exitToPrint_spec` hypotheses (`x2/x26/x20/x23`, the six
`SlotHolds`, and the width test `hwlt`) are the loop-carried spill/cursor facts
that the digit loop preserves but does not yet *surface* in
`signToDigits_neg_spec`'s postcondition (the wiring gap tracked as "part 2b
item 1").  They are carried here as an explicit hypothesis bundle
(`hExit`) about the exit configuration, so this lemma reduces the whole
`[0x800080e4, 0x8000782c)` obligation to exactly that spill-threading task —
without touching, or re-deriving, any of the green machinery below it.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (__hidden___udivdi3Loaded)

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

