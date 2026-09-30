import Vsa.Sim.SnprintfSpec11
import Vsa.Sim.DecodeTable.Batch12Part08
import Vsa.Sim.DecodeTable.Batch12Part03
import Vsa.Sim.DecodeTable.Batch12Part16
import Vsa.Sim.DecodeTable.Batch12Part18
import Vsa.Sim.DecodeTable.Batch11Part29
import Vsa.Sim.DecodeTable.Batch11Part04
import Vsa.Sim.DecodeTable.Batch10Part29
import Vsa.Sim.DecodeTable.Batch09Part29
import Vsa.Sim.DecodeTable.Batch09Part24
import Vsa.Sim.DecodeTable.Batch09Part25
import Vsa.Sim.DecodeTable.Batch09Part26
import Vsa.Sim.DecodeTable.Batch09Part22
import Vsa.Sim.DecodeTable.Batch08Part27
import Vsa.Sim.DecodeTable.Batch06Part10
import Vsa.Sim.DecodeTable.Batch05Part30
import Vsa.Sim.DecodeTable.Batch05Part31
import Vsa.Sim.DecodeTable.Batch05Part21
import Vsa.Sim.DecodeTable.Batch05Part22
import Vsa.Sim.DecodeTable.Batch05Part11
import Vsa.Sim.DecodeTable.Batch04Part24
import Vsa.Sim.DecodeTable.Batch04Part29
import Vsa.Sim.DecodeTable.Batch03Part15
import Vsa.Sim.DecodeTable.Batch03Part09
import Vsa.Sim.DecodeTable.Batch03Part18
import Vsa.Sim.DecodeTable.Batch02Part27
import Vsa.Sim.DecodeTable.Batch02Part17
import Vsa.Sim.DecodeTable.Batch02Part02
import Vsa.Sim.DecodeTable.Batch01Part11
import Vsa.Sim.DecodeTable.Batch01Part12
import Vsa.Sim.ObsAvoid

/-!
# M3 Layer-3 — `SnprintfSpec17` : second iovec entry + `__ssprint_r` call setup (`_i2`)

The flush continuation of `printEntryToSignIov_spec` (`SnprintfSpec11`), which
lands at `0x800078ac` with the sign-byte iovec built.  This file covers the
executed path that builds the SECOND iovec entry (the digit string) and enters
the string-sink flush routine `__ssprint_r`:

```
  78ac: li   a4,128
  78b0: beq  t0,a4,8548      NOT taken (t0 = flags&0x84 ≠ 0x80)
  78b4: subw s4,s4,s6        s4 := width − digit_count
  78b8: bgtz s4,7cec         NOT taken (no left padding: width ≤ len)
  78bc: andi a4,t1,256
  78c0: bnez a4,7e00         NOT taken (flags&0x100 = 0)
  78c4: lw   a5,232(sp)      a5 := iov count
  78c8: add  a2,a2,s6        a2 := cursor + digit_count
  78cc: sd   a2,240(sp)      store cursor
  78d0: addiw a5,a5,1        a5 := count + 1
  78d4: sd   s10,0(s7)       iov[k+1].iov_base := digit buffer base
  78d8: sd   s6,8(s7)        iov[k+1].iov_len  := digit count
  78dc: li   a4,7
  78e0: sw   a5,232(sp)      store count + 1
  78e4: blt  a4,a5,7bf4      NOT taken (count + 1 ≤ 7, no early flush)
  78e8: addi s7,s7,16        iov cursor += 16
  78ec: andi t1,t1,4
  78f0: beqz t1,78fc         taken (flags&4 = 0)
  78fc: mv   a5,t3           a5 := payload end
  7900: bge  t3,a6,7908      taken ⇒ a5 := t3 ; not taken ⇒ 7904
  7904: mv   a5,a6           a5 := len
  7908: ld   a4,16(sp)       a4 := running total
  790c: addw a5,a5,a4        a5 := total + max(t3, a6)
  7910: sd   a5,16(sp)       store total
  7914: bnez a2,8678         taken (cursor ≠ 0 — there is buffered output)
  8678: ld   a1,8(sp)        a1 := the string-sink cursor struct
  867c: addi a2,sp,224       a2 := &sink
  8680: mv   a0,s0           a0 := reent
  8684: jal  e908 <__ssprint_r>   call; ra := 0x80008688
```

`iov2Tail_spec` is the shared tail from `0x80007908` (either `bge` outcome);
`iov2ToSsprintCall_spec` composes the head with it and is stated with the
`bge` outcome as an `if`, so both outcomes are covered by one specification.
The postcondition is exactly the `__ssprint_r` ABI entry state: `a0` = the
reent pointer, `a1` = the string-sink cursor struct pointer, `a2` = the sink,
`ra` = the return point `0x80008688`, PC = `0x8000e908`, and the memory with
the second iovec entry, the bumped cursor/count/total fields written.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 16000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## The tail: `0x80007908` → the `jal` at `0x80008684` completed

Shared by both `bge t3,a6` outcomes; `vsel` is whichever of `t3`/`a6` the
branch selected (`a5` at entry). -/

/-! ## The composed segment: `0x800078ac` → the `__ssprint_r` call (`0x8000e908`)

`iov2ToSsprintCall_spec` runs the head (`li/beq/subw/bgtz/andi/bne/lw/add/sd/
addiw/sd/sd/li/sw/blt/addi/andi/beq/mv`) to the `bge t3,a6` at `0x80007900`,
case-splits its outcome, and finishes with `iov2Tail_spec` — both outcomes
covered, the selected `a5` written as an `if`. -/

end Vsa.Sim
