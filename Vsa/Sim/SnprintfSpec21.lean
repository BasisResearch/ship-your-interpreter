import Vsa.Sim.SnprintfSpec11
import Vsa.Sim.SlotFrame
import Vsa.Sim.RegPins
import Vsa.Sim.PtrArith
import Vsa.Sim.SnprintfSitesRet
import Vsa.Sim.SnprintfSitesRet2

/-!
# M3 Layer-3 — `SnprintfSpec21` : flush return, segment A
## `0x80008688` (post-`__ssprint_r` `beqz a0`) → `0x80007720` (parse-loop head)

The first segment of the `%lld` flush **return path** (pctrace "Flush part 3",
step after `ssprint_iov2_spec`): the `jal __ssprint_r` at `0x80008684` has
returned with `a0 = 0`, and svfprintf cleans up the gather state and jumps back
to the parse-loop head:

```
  80008688: beqz a0,80007918      a0 = 0 (ssprint_iov2_post) ⇒ TAKEN
  80007918: ld   a5,32(sp)        a5 := mem[sp+32]  (= 0: no malloc'd conv buffer)
  8000791c: sw   zero,232(sp)     iov count := 0
  80007920: beqz a5,80007930      TAKEN (no _free_r call — a5 = 0)
  80007930: mv   s7,s5            iov cursor := iov array base
  80007934: j    80007720         back to the parse-loop head
```

`retA_spec`: one `Steps` chain over the six sites, memory changed only by the
`sw` (`writeMap4` at `sp+232`), `x2/x3/x8/x9/x21` carried, `x23 := s5`.  The
`mem[sp+32] = 0` slot is a caller obligation (the conversion path never
allocates for `%lld`; the slot is `sd zero`-initialized in the prologue).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

