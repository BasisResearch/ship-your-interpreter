import Vsa.Sim.ValueSites
import Vsa.Sim.Code.__ssputs_r
import Vsa.Sim.DecodeTable.Batch16Part01
import Vsa.Sim.DecodeTable.Batch06Part31
import Vsa.Sim.DecodeTable.Batch04Part10
import Vsa.Sim.DecodeTable.Batch06Part30
import Vsa.Sim.DecodeTable.Batch06Part28
import Vsa.Sim.DecodeTable.Batch01Part19
import Vsa.Sim.DecodeTable.Batch01Part22
import Vsa.Sim.DecodeTable.Batch08Part01
import Vsa.Sim.DecodeTable.Batch01Part24
import Vsa.Sim.DecodeTable.Batch01Part13
import Vsa.Sim.DecodeTable.Batch01Part26
import Vsa.Sim.DecodeTable.Batch01Part29
import Vsa.Sim.DecodeTable.Batch01Part14
import Vsa.Sim.DecodeTable.Batch15Part04
import Vsa.Sim.DecodeTable.Batch04Part09
import Vsa.Sim.DecodeTable.Batch01Part01
import Vsa.Sim.DecodeTable.Batch11Part19
import Vsa.Sim.DecodeTable.Batch03Part29
import Vsa.Sim.DecodeTable.Batch04Part21
import Vsa.Sim.DecodeTable.Batch04Part30
import Vsa.Sim.DecodeTable.Batch07Part17
import Vsa.Sim.DecodeTable.Batch07Part07
import Vsa.Sim.DecodeTable.Batch07Part23
import Vsa.Sim.DecodeTable.Batch01Part04

/-!
# M3 Layer-3 — `SsputsSites` : per-site step battery for the `__ssputs_r` fast path (`_sp`)

Per-site `StepObs` lemmas for the `__ssputs_r` fast path (`0x8001438c …
0x800143f0`): prologue (frame setup, spills of `s0/s1/ra`), the `bgeu a3,s1`
dispatch (only the NOT-taken — fast-path — site is built), argument marshalling
into the `memmove` call at `0x800069c4`, and the post-call cursor/space update +
epilogue restore + `ret`.

```
  8001438c: addi sp,sp,-64
  80014390: sd   s1,40(sp)
  80014394: lw   s1,12(a1)      s1 := space left in the sink
  80014398: sd   s0,48(sp)
  8001439c: sd   ra,56(sp)
  800143a0: mv   s0,a1
  800143a4: mv   a5,a2
  800143a8: bgeu a3,s1,…        NOT taken on the fast path (len < space)
  800143ac: sext.w a4,a3
  800143b0: ld   a0,0(s0)       a0 := cursor
  800143b4: mv   s1,a4
  800143b8: mv   a1,a5
  800143bc: mv   a2,s1
  800143c0: jal  ra,0x800069c4  memmove(cursor, buf, len)
  800143c4: lw   a4,12(s0)      ┐ space -= len (32-bit)
  800143c8: ld   a5,0(s0)       │ cursor += len
  800143cc: li   a0,0           │
  800143d0: subw a4,a4,s1       │
  800143d4: add  a5,a5,s1       │
  800143d8: sw   a4,12(s0)      │
  800143dc: sd   a5,0(s0)       ┘
  800143e0: ld   ra,56(sp)      ┐ epilogue
  800143e4: ld   s0,48(sp)      │
  800143e8: ld   s1,40(sp)      │
  800143ec: addi sp,sp,64       │
  800143f0: ret                 ┘
```
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

