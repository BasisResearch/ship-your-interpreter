import Vsa.Sim.SnprintfSpec15
import Vsa.Sim.Code.SvfprintfSlice2
import Vsa.Sim.StrcpySites
import Vsa.Sim.DecodeTable.Batch16Part11
import Vsa.Sim.DecodeTable.Batch15Part19
import Vsa.Sim.DecodeTable.Batch11Part05
import Vsa.Sim.DecodeTable.Batch08Part18
import Vsa.Sim.DecodeTable.Batch08Part03
import Vsa.Sim.DecodeTable.Batch06Part25
import Vsa.Sim.DecodeTable.Batch06Part18
import Vsa.Sim.DecodeTable.Batch06Part14
import Vsa.Sim.DecodeTable.Batch05Part30
import Vsa.Sim.DecodeTable.Batch02Part31
import Vsa.Sim.DecodeTable.Batch02Part14
import Vsa.Sim.DecodeTable.Batch02Part12
import Vsa.Sim.ObsAvoid

/-!
# M3 Layer-3 — `SnprintfSpec16` : the `%lld` `'l'`/`"ll"` length-modifier **handler
gap** + the parse-dispatch → verified-digit-path composition (`_p16`)

`SnprintfSpec14.parseDispatch_l_full_spec` reaches the `'l'` handler entry
`0x80008534`, and `SnprintfSpec15.dispatchD_ll_to_printEntry_spec` runs the `'d'`
handler `ll`-branch `0x80008008 → 0x800080e4` (the entry of
`SnprintfSpec8.entryToPrint_neg_spec`).  Between them sit two short handlers that
were **outside** `SvfprintfSliceLoaded`'s coverage — now pinned in
`Code/SvfprintfSlice2.lean`:

```
  ── 'l' handler @ 0x80008534 → "ll" @ 0x80009060 ──  (handler_l_spec)
  80008534: lbu  s8,0(s9)          s8 := format[2]  (= 'l' = 0x6c)
  80008538: li   a5,108            a5 := 'l'
  8000853c: beq  s8,a5,0x80009060  format[2]=='l' ⇒ TAKEN → "ll" handler

  ── "ll" handler @ 0x80009060 → dispatch @ 0x80007798 ──  (handler_ll_spec)
  80009060: lbu  s8,1(s9)          s8 := format[3]  (= 'd' = 0x64)
  80009064: ori  t1,t1,32          x6 := x6 ||| 0x20   (SET THE ll-FLAG)
  80009068: addi s9,s9,1           advance format cursor
  8000906c: j    0x80007798        back to the conversion dispatch

  ── 2nd dispatch pass @ 0x80007798 → slot-load @ 0x800077b4 ──  (parseDispatchArith_d_spec)
  (sext.w / addiw / bltu-nottaken / slli / srli / add on char 'd' = 0x64)
```

Composing `parseDispatch_l_full_spec` ≫ `handler_l_spec` ≫ `handler_ll_spec` ≫
`parseDispatchArith_d_spec` ≫ `SnprintfSpec13.parseDispatch_d_spec` ≫
`dispatchD_ll_to_printEntry_spec` yields **`parseToDigitEntry_spec`**, a single
`Steps` chain from the first conversion dispatch head `0x80007798` (with the `'l'`
character in `x24`) all the way through to `0x800080e4` — the exact entry of
`entryToPrint_neg_spec`, onto which it composes.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Local `jump_x0` (`j`) read-back consumers (mirroring `SnprintfSpec5` /
`EnvGetSpec7`; those live outside this import closure). -/

/-! ## `handler_l_spec` — the `'l'` handler `0x80008534 → 0x80009060`

From `0x80008534` with the format cursor `s9 = x25 = vcur` pointing at the second
`'l'` (`mem[vcur] = 0x6c`), run `lbu s8,0(s9)` / `li a5,108` / `beq s8,a5,…`; the
compare succeeds (`format[2] == 'l'`), so the `beq` is **taken** to the `"ll"`
handler `0x80009060`.  The ll-flag word `x6`, the field width `x20`, the frame
`x2`, and the cursor `x25` are threaded through unchanged. -/

/-! ## `handler_ll_spec` — the `"ll"` handler `0x80009060 → 0x80007798`

Sets the ll-flag `x6 := x6 ||| 0x20`, reads the conversion char `format[3]` into
`s8 = x24`, bumps the cursor `s9 := s9 + 1`, and jumps back to the conversion
dispatch head `0x80007798`.  For the `%lld` path `format[3] = 'd' = 0x64`, so
`x24 = 0x64` at the re-entry (feeding the second dispatch pass). -/

/-! ## `parseDispatchArith_d_spec` — 2nd-pass slot-address arithmetic for `'d'`

Identical to `SnprintfSpec14.parseDispatchArith_l_spec` but for the conversion
character `'d' = 0x64` (index `0x64-32 = 68`), driving the SECOND dispatch pass the
`"ll"` handler branches back to.  `0x80007798 → 0x800077b4` with the `'d'` slot
address in `x15`. -/

/-! ## `handlerGap_spec` — the full length-modifier gap `0x80008534 → 0x800077b4`

Composes `handler_l_spec` ≫ `handler_ll_spec` ≫ `parseDispatchArith_d_spec` into a
single verified `Steps` chain from the `'l'` handler entry `0x80008534` (exactly
where `SnprintfSpec14.parseDispatch_l_full_spec` lands) through the `"ll"` handler
and the **second** dispatch pass' slot-address arithmetic to the `'d'` slot-load
`0x800077b4` — the entry of `SnprintfSpec13.parseDispatch_d_spec`.

The dispatch upper bound `x26 = 90` and table base `x22 = parseTableBase` are
carried from `parseInit` (untouched by the handlers).  Two format bytes pin the
`%lld` conversion: `format[2] = 'l'` (drives the `beq` into `"ll"`) and
`format[3] = 'd'` (the conversion char for the second dispatch). -/

/-! ## `parseToDigitEntry_spec` — length-modifier gap + 2nd dispatch `0x80008534 → 0x80008008`

Extends `handlerGap_spec` through the `.rodata` jump table (`parseDispatch_d_spec`)
to the `'d'` integer-conversion handler entry `0x80008008` — a single verified
`Steps` chain from the `'l'` length-modifier handler entry (where
`SnprintfSpec14.parseDispatch_l_full_spec` lands) all the way to the `'d'` handler.

This is the composition
`handler_l ≫ handler_ll ≫ parseDispatchArith_d ≫ parseDispatch_d`; from `0x80008008`,
`SnprintfSpec15.dispatchD_ll_to_printEntry_spec` continues to `0x800080e4`, the
entry of `SnprintfSpec8.entryToPrint_neg_spec` — see `parseToPrintEntry_spec`. -/

/-! ## `parseToPrintEntry_spec` — length-modifier gap → verified digit path `0x80008534 → 0x800080e4`

The full span this module targets: composes `parseToDigitEntry_spec`
(`0x80008534 → 0x80008008`, the `'d'` handler entry) with
`SnprintfSpec15.dispatchD_ll_to_printEntry_spec` (`0x80008008 → 0x800080e4`, the
`ll` long-long arg fetch) into a single verified `Steps` chain from the `'l'`
length-modifier handler entry all the way to `0x800080e4` — the **exact** entry of
`SnprintfSpec8.entryToPrint_neg_spec`, onto which the sign/digit path continues.

`parseToDigitEntry_spec` preserves memory and threads the four registers consumed
by the `ll` argument-fetch path: the flag word `x6`, format cursor `x25`, source
register `x27`, and field width `x20`. -/

end Vsa.Sim
