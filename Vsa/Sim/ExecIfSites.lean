import Vsa.Sim.ValueSites
import Vsa.Sim.Code.Exec_stmt
import Vsa.Sim.DecodeTable.Batch01Part01
import Vsa.Sim.DecodeTable.Batch15Part01

/-!
# Layer 4 — M4 `ifStmt` falsy-no-else tail sites (`ExecS.ifNone`)

The two straight-line instructions on the `ifNone` (condition falsy, no `else`)
fall-through path, after the condition eval + `value_truthy` + the two falsy
branches land at `0x800042d4`:

```
800042d4:  li  a0,0        -- x10 := 0 = StatusCode .normal   (00000513)
800042d8:  j   0x8000409c  -- into the shared epilogue         (dc5ff06f)
```

These mirror `site_80004184_es`/`site_80004188_es` (the `expr` arm's identical
`li a0,0` / `j 0x8000409c` tail); only the PC and the `j` immediate differ. The
rest of the `ifNone` arm body (cond eval + `value_truthy` + the two falsy
branches, `0x800041e8 → 0x800042d4`) is delivered as a named glue residual, so it
needs no per-site battery here.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

