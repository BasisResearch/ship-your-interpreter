import Vsa.Sim.SnprintfSitesFast
import Vsa.Sim.SnprintfSitesFast2
import Vsa.Sim.SnprintfSpec7
import Vsa.Sim.ObsAvoid

/-!
# M3 Layer-3 — `SnprintfSpec43` : the single-digit fast path, negative arm (`_f43`)

From the fast/multi split `0x80008100` with magnitude `w` in `a4`, `w.toNat ≤ 9`:
the machine skips the decimal loop entirely — `bltu` at `0x80008104` falls
through, `addiw a4,a4,48` forms the single digit character, `sb a4,347(sp)`
stores it at the buffer top-1, the `blez s4` precision test (default `s4 < 1`)
jumps to the `0x80008ea4` tail block (sign read-back `lbu t5,167(sp)`, `a6:=1`,
`t6:=0`, `s6:=1` = len, `s10:=sp+347` = digit base, `j 0x8128`), the parse slot
`sp+0x20` is re-zeroed, and the seam `0x8000812c` (`beqz t5` NOT taken — the
sign byte is `'-'`) bumps `a6` to `2 = len+1` and hops via `0x8088`/`0xa830`
to the PRINT entry `0x8000782c` — the SAME landing state shape as
`exitToPrint_spec` (SnprintfSpec7) with `p = 0`.

Sites: `_fs`/`_fs2` (generated, `SnprintfSitesFast{,2}`) + the `_fl` seam
sites (SnprintfSitesFlush) + `site_80008100_sn5` (SnprintfSites3).
Arm-tail code pins: `Code/ArmPins.lean` (`ArmPinsLoaded`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

