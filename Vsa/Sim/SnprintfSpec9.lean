import Vsa.Sim.SnprintfSpec7
import Vsa.Sim.Code.__ssprint_r
import Vsa.Sim.DecodeTable.Batch07Part23
import Vsa.Sim.DecodeTable.Batch07Part17
import Vsa.Sim.DecodeTable.Batch06Part30
import Vsa.Sim.DecodeTable.Batch01Part15
import Vsa.Sim.DecodeTable.Batch01Part14
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part01
import Vsa.Sim.ObsAvoid

/-!
# M3 Layer-3 — `SnprintfSpec9` : the `__ssprint_r` return epilogue (`_ss`)

The common return tail of `__ssprint_r` (`0x8000e908`, the string-sink flush that
`snprintf("%lld", …)` calls to move the formatted iov into the caller buffer).
Both the empty-flush branch and the post-loop fall-through converge on the block
`0x8000e9b0 … 0x8000e9c8`:

```
8000e9b0: ld   ra,56(sp)       reload the return address
8000e9b4: sd   zero,16(s1)     clear the sink's _uio.uio_resid  (bytes-remaining)
8000e9b8: sw   zero,8(s1)      clear the sink's _uio.uio_iovcnt (iov-count)
8000e9bc: li   a0,0            return value 0 (success)
8000e9c0: ld   s1,40(sp)       reload s1
8000e9c4: addi sp,sp,64        pop the 64-byte frame
8000e9c8: ret                  jr ra  → the caller (svfprintf) resume PC
```

`ssprintTail_spec` is a `Triple` (`Steps`) over exactly these seven straight-line
instructions.  It is self-contained: no branch, no call, so it composes onto any
`__ssprint_r` run that reaches `0x8000e9b0` — in particular the empty-flush path
`0x8000e908 → 0x8000e91c (beqz resid=0) → 0x8000e9b0`, and (once the iov loop and
`__ssputs_r` are verified) the non-empty flush.

The two spilled callee-saves it reads back (`ra` at `sp+56`, `s1` at `sp+40`) are
supplied as `SlotHolds` facts and threaded through the two sink stores by the
existing `slotHolds_*` transport lemmas (`SnprintfSpec5`).  The sink FILE window
(`s1+8 … s1+24`) is required disjoint from those two stack slots so the reloads
survive.

Built on the shared `StepObs` site helpers + `obs_*` accessors (`Muldi3Spec`,
`MemcpySpec`, `SnprintfSpec4`) and the `__ssprint_rLoaded` byte facts.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

