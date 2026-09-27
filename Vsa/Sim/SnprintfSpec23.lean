import Vsa.Sim.SnprintfSpec22

/-!
# M3 Layer-3 — `SnprintfSpec23` : flush return, segment C
## `0x80007960` (mbtowc = 0 arm) → `0x800079b0` (svfprintf epilogue head)

The NUL-exit hop: `mbtowc` returned 0, so the loop computes the length of the
pending literal text (`s6 - fmt0 = 0` — the cursor never moved past the NUL)
and, finding it zero, falls through to the epilogue:

```
  80007960: ld   a5,0(sp)          a5 := fmt cursor (= s6)
  80007964: mv   s4,a0             s4 := 0 (the mbtowc result)
  80007968: subw s8,s6,a5          s8 := sext32(s6₃₂ - a5₃₂) = 0
  8000796c: beqz s8,800079b0       TAKEN → epilogue
```

`retC_spec`: 4 sites, no memory writes.  The `subw` guard closes structurally
(`x - x = 0`) — `s6` and `a5` are the *same* slot value `vcur`. -/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

