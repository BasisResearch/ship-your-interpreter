import Vsa.Sim.SnprintfSpec21
import Vsa.Sim.SnprintfSitesRet3
import Vsa.Sim.SnprintfSitesRet4
import Vsa.Sim.SnprintfSitesRet5
import Vsa.Sim.CodeRangeInsert

/-!
# M3 Layer-3 — `SnprintfSpec22` : flush return, segment B
## `0x80007720` (parse-loop head) → `0x80007960` (NUL exit)

The parse loop re-reads the format cursor — which now points at the
terminating NUL of `"%lld"` — and exits through the `mbtowc = 0` arm:

```
  80007720: ld   s6,0(sp)          s6 := fmt cursor (→ NUL)
  80007724: ld   s4,232(s1)        s4 := __global_locale.mbtowc = __ascii_mbtowc
  80007728: jal  80010234          call __locale_mb_cur_max
    80010234: lbu a0,1000(gp)        a0 := __mb_cur_max = 1
    80010238: ret
  8000772c: mv   a3,a0             n := 1
  80007730: addi a4,sp,200         state buffer
  80007734: mv   a2,s6             s := cursor
  80007738: addi a1,sp,180         pwc := sp+180
  8000773c: mv   a0,s0             reent
  80007740: jalr s4                call __ascii_mbtowc  (indirect!)
    80012268: beqz a1,…              NOT taken (pwc ≠ 0)
    8001226c: beqz a2,…              NOT taken (s ≠ 0)
    80012270: beqz a3,…              NOT taken (n = 1 ≠ 0)
    80012274: lbu  a5,0(a2)          a5 := *cursor = 0  (the NUL)
    80012278: sw   a5,0(a1)          *pwc := 0
    8001227c: lbu  a0,0(a2)          a0 := 0
    80012280: snez a0,a0             a0 := 0
    80012284: ret
  80007744: beqz a0,80007960       TAKEN → the NUL exit
```

`retB_spec`: one `Steps` chain over the 20 sites (incl. both callee bodies —
inlined, not composed: they are 2 and 8 instructions).  Memory changes only by
the `sw` (`writeMap4` at `sp+180`).  Locale data facts (`mbtowc` pointer at
`0x8001b880`, `__mb_cur_max` byte at `0x8001b8f8`, `gp = 0x8001b510`,
`s1 = 0x8001b798`) are caller obligations — link-time constants of the binary,
dischargeable from the ELF image at the top level.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

