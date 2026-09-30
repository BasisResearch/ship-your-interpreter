import Vsa.Sim.SnprintfSpec23

/-!
# M3 Layer-3 — `SnprintfSpec24` : flush return, segment D
## `0x800079b0` (epilogue head) → `ret` (svfprintf returns `a0 = total`)

The svfprintf epilogue on the `%lld` path:

```
  800079b0: ld   a5,240(sp)        gather cursor (= 0 — __ssprint_r cleared it)
  800079b4: beqz a5,800079bc       TAKEN (no final flush at 0x80009e40)
  800079bc: ld   a5,8(sp)          a5 := the fake FILE (string sink) ptr
  800079c0: lhu  a5,16(a5)         a5 := FILE->_flags
  800079c4: andi a5,a5,64          __SMBF test — 0 (no malloc'd buffer)
  800079c8–800079e8: ld s2/s3/s4/s5/s7/s8/s9/s10/s11 from the spill slots
  800079ec: beqz a5,800079f4       TAKEN (no 0x8000a75c cleanup)
  800079f4: ld   ra,584(sp)
  800079f8: ld   s0,576(sp)
  800079fc: ld   a0,16(sp)         a0 := THE TOTAL (accumulated ret at sp+16)
  80007a00: ld   s1,568(sp)        ── the 4 FlushPins tail instructions ──
  80007a04: ld   s6,528(sp)
  80007a08: addi sp,sp,592
  80007a0c: ret                    PC := saved ra, a0 = total
```

`retD_spec`: 22 sites, no memory writes; every reload fed from a `SlotHolds`
carried by the caller (the prologue's spills, transported across the whole
body by the sub-call frames). -/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

