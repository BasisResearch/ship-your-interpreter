import Vsa.Sim.SnprintfSpec7
import Vsa.Sim.DecodeTable.Batch14Part05
import Vsa.Sim.DecodeTable.Batch13Part02
import Vsa.Sim.DecodeTable.Batch12Part07
import Vsa.Sim.DecodeTable.Batch11Part27
import Vsa.Sim.DecodeTable.Batch10Part30
import Vsa.Sim.DecodeTable.Batch09Part28
import Vsa.Sim.DecodeTable.Batch09Part26
import Vsa.Sim.DecodeTable.Batch09Part25
import Vsa.Sim.DecodeTable.Batch09Part24
import Vsa.Sim.DecodeTable.Batch09Part10
import Vsa.Sim.DecodeTable.Batch08Part31
import Vsa.Sim.DecodeTable.Batch06Part28
import Vsa.Sim.DecodeTable.Batch05Part21
import Vsa.Sim.DecodeTable.Batch05Part07
import Vsa.Sim.DecodeTable.Batch04Part07
import Vsa.Sim.DecodeTable.Batch03Part15
import Vsa.Sim.DecodeTable.Batch03Part01
import Vsa.Sim.DecodeTable.Batch02Part24
import Vsa.Sim.DecodeTable.Batch02Part20
import Vsa.Sim.DecodeTable.Batch01Part21
import Vsa.Sim.DecodeTable.Batch01Part02
import Vsa.Sim.ObsAvoid

/-!
# M3 Layer-3 — `SnprintfSpec11` : PRINT-macro entry → first (sign) iovec entry (`_pe`)

The `svfprintf` PRINT/iov segment head that `snprintf("%lld", negative)` runs
straight after digit formatting.  From the PRINT-macro entry `0x8000782c` (where
`entryToPrint_neg_spec`, `SnprintfSpec8`, lands) this covers the executed path

```
  782c: ld   a2,240(sp)     a2 := cursor  (running dest-buffer pointer)
  7830: andi t0,t1,132      t0 := flags & 0x84   (left-justify / zero-pad bits)
  7834: mv   a0,a2
  7838: beq  t0,zero,7cd4   taken (no adjust-justify flags for %lld)
  7cd4: subw a4,t3,a6       a4 := (payload_end - len)  (pad count)
  7cd8: blt  zero,a4,8c38   NOT taken (no left padding)
  7cdc: lbu  a4,167(sp)     a4 := the sign byte  ('-')
  7ce0: bne  a4,zero,7844   taken (there IS a sign)
  7844: lw   t4,232(sp)     t4 := iovcnt
  7848: li   s11,0
  784c: addi a1,sp,167      a1 := &sign_byte
  7850: addi a2,a2,1        a2 := cursor+1
  7854: addiw t4,t4,1       t4 := iovcnt+1
  7858: li   a5,1
  785c: sd   a1,0(s7)       iov[k].iov_base := &sign_byte
  7860: sd   a5,8(s7)       iov[k].iov_len  := 1
  7864: sd   a2,240(sp)     store cursor+1
  7868: sw   t4,232(sp)     store iovcnt+1
  786c: li   a1,7
  7870: addi s7,s7,16       iov pointer += 16
  7874: blt  a1,t4,7b00     NOT taken (iovcnt+1 ≤ 7, no flush)
  7878: beq  s11,zero,78ac  taken → 0x800078ac
```

`printEntryToSignIov_spec` is one `Steps` chain over exactly these 21
instructions.  The **postcondition** is the first `iovec` entry of the FILE
sink's gather buffer — the sign byte `'-'`:

* `iov[k].iov_base := sp+167` (the address of the `'-'` byte the digit path left
  at `sp+167`) and `iov[k].iov_len := 1`, written at the iov cursor `s7 = viov`;
* the iov cursor `s7` advanced by 16 (one `struct iovec`);
* the cursor field `mem[sp+240]` bumped by 1 and the iov count `mem[sp+232]`
  bumped by 1.

This is the field-level postcondition a later agent feeds into the
`__ssputs_r`/memcpy composition.

The three branch guards are discharged from explicit hypotheses about the parsed
flag word (`hflag84`), the (non-positive) pad count (`hpad`), and the
sign-present marker byte at `sp+167` (`hsignbyte`).  See the report for how they
compose onto `entryToPrint_neg_spec`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

