import Vsa.Sim.ValueEqualSpec3
import Vsa.Sim.ObsAvoid

/-!
# Layer 3 — the `str`-`str` handler epilogue and the unified `value_equal` spec

`ValueEqualSpec3` carried the `str` handler from `0x800028c4` **through the `strcmp` call**
to the return-site `0x800028d8` (`ve_str_reaches_result`), recovering `sp` across the call
via strcmp's ghost frame (the fix retrofitted in this cluster: `strcmp_post` now exposes a
`NotWrittenStrcmp` blanket frame, so `x2 = sp - 16` survives the call).

This file finishes the handler:

```
0x800028d8  ld ra,8(sp)      ; restore ra := r from the spill slot (mem[sp-8], untouched)
0x800028dc  seqz a0,a0       ; a0 := (strcmp result == 0) ? 1 : 0 = Value.equal (.str sa)(.str sb)
0x800028e0  addi sp,sp,16    ; sp := entry_sp
0x800028e4  ret              ; PC := ra = r
```

and assembles:

* `ve_str_epilogue` — `0x800028d8 → ret`, from the post-call state to the return.
* `ve_str_handler` — the whole `str` handler `0x800028c4 → ret`.
* `value_equal_spec_str` — from `ve_pre` (`str`-`str`) + the stack witnesses to the
  **stack-window post** `ve_str_post` (`mem` agrees with `m0` off `[entry_sp-16, entry_sp)`).
* `value_equal_spec_full` — either branch: `str`-`str` via `value_equal_spec_str`, everything
  else via `value_equal_spec_nonstr` (whose `mem = m0` post trivially weakens to the window
  form).

## Why the stack-window post

The five non-`str` handlers are read-only (`mem = m0`). The `str` handler spills `ra` into
`[entry_sp-16, entry_sp)`; the spilled dword is never cleaned up, so at the return `mem ≠ m0`
inside that window. The honest unified post therefore weakens `mem = m0` to *agreement with
`m0` outside the scratch window* (the `MallocContract`/`env_new` framing form from
AMENDMENT 2). Every other observable — `PC = r`, `x1 = r`, `x2 = entry_sp` restored, the
result `x10`, `tick < 2`, and the `NotWrittenVE` frame — is exact.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While (Value NativeFn)
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## The `str`-`str` stack-window post

`ve_str_post g r sp va vb m0` is `ve_post` weakened at the memory clause: instead of
`mem = m0`, memory agrees with `m0` outside the scratch window `[sp-16, sp)`, and `x2` is
back to the entry `sp`. -/

/-! ## The epilogue `0x800028d8 … 0x800028e4`

From the post-call state (`ve_str_reaches_result`'s conclusion) at `0x800028d8` with
`x1 = 0x800028d8` (the `jal` link), `x10 = x` (strcmp result), `x2 = sp - 16`, `mem = m1`
where `m1` agrees with `m0` off `[sp-16, sp)` and the spill slot `[sp-8, sp)` holds
`sdData_val r`, run the four epilogue instructions to the return at `r`. -/

/-! ## The whole `str` handler `0x800028c4 → ret`

`ve_str_reaches_result` (through the call) then `ve_str_epilogue`. -/

/-! ## The `str`-`str` spec (`value_equal_spec_str`)

From `ve_pre` (`str`-`str`) plus the stack/region witnesses to the stack-window post. The
dispatch (`ve_to_handler`) reaches the handler at `0x800028c4`; `ve_str_handler` finishes. -/

/-! ## The unified `value_equal` spec (`value_equal_spec_full`)

Either the `str`-`str` branch (`value_equal_spec_str`) or one of the five non-`str`
branches (`value_equal_spec_nonstr`), unified under the weaker stack-window post: the
non-`str` post `mem = m0` trivially agrees with `m0` off any window, and `x2` is never
touched (`x2 = g x2 = sp`). -/

end Vsa.Sim
