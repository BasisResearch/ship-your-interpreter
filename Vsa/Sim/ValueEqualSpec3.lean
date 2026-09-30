import Vsa.Sim.ValueEqualSpec2
import Vsa.Sim.ValueEqualSites3
import Vsa.Sim.StrcmpSpecCond
import Vsa.Sim.ValueSpec
import Vsa.Sim.EnvDefSpec2
import Vsa.Sim.ObsAvoid

/-!
# Layer 3 — total-correctness spec for the `str`-`str` handler of `value_equal`

The final `value_equal` handler: `str`-`str` (`@0x800028c4`). Unlike the five non-`str`
handlers (all read-only, `mem = m0` post), this one has a **stack footprint** — it spills
`ra` at `[entry_sp-8, entry_sp)`, calls `strcmp`, restores `ra`, and returns. So at the
return `mem ≠ m0` (the spilled `ra` remains in the scratch slot), and the postcondition is
framed to agree with `m0` **outside** the stack window `[entry_sp-8, entry_sp)`.

## What the handler does

```
0x800028c4  ld a1,8(a1)      ; a1 := pb  (string ptr b, from ValueRepr .str)
0x800028c8  ld a0,8(a0)      ; a0 := pa  (string ptr a)
0x800028cc  addi sp,sp,-16   ; sp := entry_sp - 16
0x800028d0  sd ra,8(sp)      ; spill ra (= r) at (entry_sp-16)+8 = entry_sp-8
0x800028d4  jal strcmp       ; ra := 0x800028d8; PC := strcmp entry (0x80006ea0)
0x800028d8  ld ra,8(sp)      ; restore ra := r from the (untouched) spill slot
0x800028dc  seqz a0,a0       ; a0 := (strcmp result == 0) ? 1 : 0
0x800028e0  addi sp,sp,16    ; sp := entry_sp
0x800028e4  ret              ; PC := r
```

## Result bridge (`x10 == 0 ↔ sa = sb`)

`strcmp_full_spec` returns `strcmpSign x10 = strcmpSpecSign csa csb` where `sa = ofList csa`,
`sb = ofList csb`. `strcmpSign x = 0 ↔ x = 0` (definition), and (under the two `CStr`
witnesses) `strcmpSpecSign csa csb = 0 ↔ sa = sb` (`string_eq_iff_strcmpSpecSign_zero`,
reproved locally). Hence `(x10 == 0) = (sa == sb) = Value.equal (.str sa) (.str sb)`.
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

/-! ## Spec-sign ↔ string-equality bridge

Reuses `string_eq_iff_strcmpSpecSign_zero` (proved in `EnvDefSpec2`): under two `CStr`
witnesses, `strcmpSpecSign csa csb = 0 ↔ sa = sb`. -/

/-! ## `strcmpSign x = 0 ↔ x = 0`. -/

/-! ## `StrcmpLoaded` / `MaskPinned` transfer through an agreeing memory -/

/-! ## Small `sp` / spill arithmetic (reproved locally) -/

/-! ## Stack / disjointness bundle for the `str` handler

`entry_sp` is the entry stack pointer; the spill lives at `[entry_sp-16, entry_sp)` (the
`ra` at `entry_sp-8`). The stack window must be disjoint from the two string byte ranges,
the `strcmp` code, the mask rodata, RAM/HTIF, and be 8-aligned in RAM. -/

/-! ## Str-path ghost frame

The `str` handler additionally writes `x1` (`ra`: spill `ld`, `jal` link) and `x2` (`sp`:
two `addi`), both restored to their entry values by return. Mid-computation these differ
from the entry ghost, so they are threaded explicitly; `NotWrittenVEStr` excludes them (and
strcmp's caller-saved scratch `x5-x7`, `x12-x15`) so the blanket frame carries every other
register through the whole handler including the callee. -/

/-! ## `jal` observation consumers (inlined, analogue of `obs_alu_*`)

Copied from `DivSites2`/`EnvNewSpec` (which we do not import — heavy dependencies). From a
`jal` observation, read the framing fields off `σ'`. -/

/-! ## The `str`-`str` handler up to the `strcmp` result (`0x800028c4 → 0x800028d8`)

### ARCHITECTURAL BLOCKER (epilogue unreachable against the current `strcmp` spec)

The str handler spills `ra`, calls `strcmp`, then runs the epilogue `ld ra,8(sp); seqz;
addi sp,sp,16; ret`.  The epilogue's effective addresses (`ld`/`addi` off `sp`) and the
final `ret` target all require knowing `x2 = sp - 16` **after** the call — but
`strcmp_post` (`StrcmpSpec.lean:1038`) exposes **no register/`sp`/ghost frame at all**
(only `PC = r`, `x1 = r`, `x10`, `mem = m0`, `tick`, `GoodState`).  So `sp` (and every
callee-saved GPR) is lost across the call, and the epilogue cannot be threaded.  Extending
`strcmp_post` with a `NotWrittenStrcmp` blanket frame (as its own docstring at line 1070
*claims* but does not carry) is the prerequisite; that requires editing `StrcmpSpec.lean`,
which is out of scope here.

What IS provable — and proved below — is the run **through the `strcmp` call**: the spill,
the callee-contract composition (`strcmp_full_spec`, all witnesses transferred through the
spill via `cstr_writeMap8_disjoint` / `strcmpLoaded_of_agree` / `maskPinned_of_agree` /
`valueEqualLoaded_of_agree`), and the result bridge to `Value.equal (.str sa) (.str sb)`.

`ve_str_reaches_result`: from `0x800028c4` to the `strcmp` return `0x800028d8`, with
`x10`'s value being the machine `strcmp` result whose `== 0` test decides `sa = sb`, and
`mem = m1` (the spilled memory, agreeing with `m0` off the stack window). -/

end Vsa.Sim
