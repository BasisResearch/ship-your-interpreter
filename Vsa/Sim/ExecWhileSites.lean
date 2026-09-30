import Vsa.Sim.ValueSites
import Vsa.Sim.Code.Exec_stmt
import Vsa.Sim.DecodeTable.Batch01Part01
import Vsa.Sim.DecodeTable.Batch03Part16

/-!
# Layer 4 — M4 `whileStmt` normal-exit tail sites

The two straight-line instructions on the `whileStmt` normal-exit fall-through
(condition falsy → `whileFalse`; body `.brk` → `whileBreak`), after the arm body
lands at `0x80004090`:

```
80004090:  li  a0,0        -- x10 := 0 = StatusCode .normal   (00000513)
80004094:  j   0x8000409c  -- into the shared epilogue         (0080006f)
```

These are IDENTICAL to the `expr`/`ifNone` `li a0,0` / `j 0x8000409c` tail; only
the PC and the `j` immediate differ. The rest of the `whileStmt` arm body (cond
eval + `value_truthy` + branch + optional body recursion + loop control) is
delivered as named glue residuals, so it needs no per-site battery here.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

