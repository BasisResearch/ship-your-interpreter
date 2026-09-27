import Vsa.Sim.ErrorSim
import Vsa.Sim.ExecuteStore
import Vsa.Sim.HtifLift

/-!
# Layer 5 — discharging `errorTailHalts`'s residuals (`ExitStoreHalts`)

`errorTailHalts` (`Vsa/Sim/ErrorSim.lean`) lands the runtime_error → exit(70)
chain conditional on two residuals: `ErrorTailChain` (the interp_run-cont / main /
crt0 / exit decode span, `0x80004428 → _exit` store site) and `ExitStoreHalts`
(the exit `sd a5,tohost` step → HTIF halt bridge).  This file discharges
`ExitStoreHalts` — the **one genuine machine-plumbing residual** — by decoding the
`_exit` `sd a5,tohost` architectural step directly.

## The single-`stepOnce` halt

The key structural fact (`Vsa/Elf.lean:80`): a `stepOnce` that performs the
`sd a5,tohost` store **halts inside the same `stepOnce`**.  `stepOnce` runs
`try_step` (which performs the store, setting `htif_done := true`,
`htif_exit_code := 70` via `mem_write_value_tohost_exit`) and returns `false`;
then it re-checks `htif_done` (`Elf.lean:86`) — now `true` — and returns
`.inl (some 70, u+1)`.  No `tick_clock` fires (the tick check at `Elf.lean:90` is
past the early return).  So the exit-store `stepOnce` is a `Halted` node directly:
`ExitStoreHalts` is `Steps c c` (refl) followed by that `Halted`, with `output`
unchanged (the exit store touches only HTIF control registers, never
`sailOutput`).

The store is routed through the reusable stack:
`execute (STORE …)` = `execute_STORE_char` → `vmem_write_addr_w` (w = 8) with the
`mem_write_value` post-state supplied by `mem_write_value_tohost_exit`
(`Vsa/Sim/HtifLift.lean`), all lifted through `try_step_execute_char`
(`Vsa/Sim/Skeleton.lean`).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps Halted Halts output)
open Vsa.Sim.Code (LongjmpLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## The exit-store execute step

`execute (STORE (imm, rs2, rs1, 8))` on the `_exit` `sd a5,tohost` site, routed
through `execute_STORE_char` / `vmem_write_addr_w` / `mem_write_value_tohost_exit`.
The effective address is `tohostAddr`, the store data is the syscall-exit word
`(70 <<< 1) ||| 1`, and the post-state carries `htif_done := true`,
`htif_exit_code := 70`. -/

/-! ## The `try_step`-final state for the exit store

`sigmaExitFinal σ pc npc vminstret data` is the skeleton `σ₅` for the exit store:
`sigmaExit` (execute post-state) with `PC := npc` and `minstret := vminstret+1`. -/

/-! ## The exit-store `stepOnce` halts

`stepOnce i u` on the `_exit` `sd a5,tohost` store: `try_step` performs the store
(⇒ `false`, HTIF exit latched), then the *same* `stepOnce` re-checks `htif_done`
(`Elf.lean:86`) — now `true` — and returns `.inl (some 70, u+1)`.  This is a
`Halted` node.  No `tick_clock`. -/

/-! ## `ExitStorePre` and `ExitStoreHalts`

`ExitStorePre out c` pins the machine exactly at the `_exit` `sd a5,tohost` store:
the `GoodState`/PMP control state, the PC and the four instruction bytes, the
decode to `STORE (imm, rs2, rs1, 8)`, the base/data register reads with effective
address `tohostAddr` and store data `(70<<<1)|1`, the HTIF-mailbox pins
(`htif_payload_writes = 0`), and `output σ = out`.  (The *decode* facts — which
concrete `sd` encoding realizes these — belong to the `ErrorTailChain` span; here
they are consumed abstractly, so `ExitStoreHalts` composes without committing to
the encoding.) -/

/-! ## `errorTailHalts` with `ExitStoreHalts` discharged

`errorTailHalts_exit` supplies the (now-proved) `ExitStoreHalts` bridge to
`errorTailHalts`, leaving only the `ErrorTailChain` decode span (the interp_run-cont
/ main / crt0 / exit control-transfer battery, `0x80004428 → _exit` store site) as
the single remaining residual. -/

end Vsa.Sim
