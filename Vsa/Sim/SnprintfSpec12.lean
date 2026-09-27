import Vsa.Sim.SnprintfSpec11
import Vsa.Sim.DecodeTable.Batch16Part26
import Vsa.Sim.DecodeTable.Batch13Part21
import Vsa.Sim.DecodeTable.Batch09Part07
import Vsa.Sim.DecodeTable.Batch08Part09
import Vsa.Sim.DecodeTable.Batch04Part29
import Vsa.Sim.DecodeTable.Batch02Part30
import Vsa.Sim.DecodeTable.Batch01Part31
import Vsa.Sim.DecodeTable.Batch01Part09
import Vsa.Sim.DecodeTable.Batch01Part02
import Vsa.Sim.DecodeTable.Batch01Part01
import Vsa.Sim.ObsAvoid

/-!
# M3 Layer-3 — `SnprintfSpec12` : `%`-format parse-init (width/flags reset) (`_pi`)

The single upstream `svfprintf` fact that all remaining `snprintf("%lld", …)`
residuals funnel through: the **parse-init block** that (immediately after the
`'%'` conversion-spec introducer is found) resets the field-width accumulator
`x20` and the flags word `x6` to their "nothing specified" defaults.

## Executed footprint `[0x8000776c, 0x80007798)` (11 instructions, straight-line)

```
  776c: addi x15,x22,1      x15 := fmt+1          (fmt-pointer past '%')
  7770: lbu  x24,1(x22)     x24 := format[1]      (the char after '%')
  7774: sb   x0,167(sp)     mem[sp+167] := 0      (sign-byte slot cleared)
  7778: sd   x15,0(sp)      mem[sp+0]   := fmt+1  (spilled fmt cursor)
  777c: addi x20,x0,-1      x20 := -1             ← WIDTH accumulator = "unset"
  7780: addi x6,x0,0        x6  := 0              ← FLAGS word = 0 (no flags)
  7784: addi x26,x0,90      x26 := 90  ('Z')      (dispatch upper bound)
  7788: auipc x22,0x13000                          jump-table base hi
  778c: addi x22,x22,-1676  x22 := 0x8001a0fc     (conv-char jump-table base)
  7790: addi x27,x0,0       x27 := 0
  7794: addi x25,x15,0      x25 := fmt+1          (scan cursor)
  --> 7798  (the flag/length/conversion char-read + jump-table dispatch loop head)
```

`parseInit_spec` is one `Steps` chain over exactly these 11 instructions.  Its
postcondition pins the two load-bearing parse facts at `0x80007798`:

* **`x20 = -1`** (the width accumulator's "no field width" sentinel), and
* **`x6  = 0`**  (the flags word — no `-`/`+`/`0`/`#`/`' '` flag seen).

These are exactly the facts the two `snprintf("%lld")` residuals reduce to:

* `SnprintfSpec8.entryToPrint_neg_spec`'s `hwidth` — `v20.toInt < (p+1)` — holds
  because the parsed width is `-1 < 1 ≤ p+1`.  On the executed `%lld` path
  (`'l' → "ll" → 'd'`, `0x80009060` then `0x800080d8`) `x20` is **never** written
  between `0x8000777c` and `0x800080e4`, so `v20 = -1` there.
* `SnprintfSpec11.printEntryToSignIov_spec`'s `hflag84` — `vt1 &&& 0x84 = 0` —
  and `SnprintfSpec6`'s `hflag` — `vt1 &&& 0x400 = 0` — hold because the flags
  word entering the digit path is `x6 = 0x20` (only the "ll"-handler's
  `ori x6,x6,32` fires on the `%lld` path), and `0x20 &&& 0x84 = 0`,
  `0x20 &&& 0x400 = 0`.  This module pins the *reset to 0* that the `ori`s build
  on; the `%lld`-specific `0x20` is added downstream (`0x80009060`).

The format string `"%lld"` enters only through the byte at `fmt+1` read by
`lbu x24,1(x22)`.  That byte is carried as an opaque pinned precondition
(`hfmt1 : mem[fmt+1]? = some bfmt1`); for the concrete `"%lld"` literal in rodata
`bfmt1 = 'l' = 0x6c`, but the width/flags reset is independent of it — hence it is
left general.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

