import Vsa.Sim.SnprintfSpec5
import Vsa.Sim.SnprintfSpec17
import Vsa.Sim.StrcpySpec
import Vsa.Sim.Code.Memmove
import Vsa.Sim.DecodeTable.Batch07Part26
import Vsa.Sim.DecodeTable.Batch07Part05
import Vsa.Sim.DecodeTable.Batch07Part02
import Vsa.Sim.DecodeTable.Batch06Part32
import Vsa.Sim.DecodeTable.Batch06Part15
import Vsa.Sim.DecodeTable.Batch04Part18
import Vsa.Sim.DecodeTable.Batch04Part10
import Vsa.Sim.DecodeTable.Batch02Part27
import Vsa.Sim.DecodeTable.Batch02Part24
import Vsa.Sim.DecodeTable.Batch02Part23
import Vsa.Sim.DecodeTable.Batch01Part21
import Vsa.Sim.DecodeTable.Batch01Part16
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch09Part23
import Vsa.Sim.DecodeTable.Batch16Part28
import Vsa.Sim.DecodeTable.Batch16Part15
import Vsa.Sim.DecodeTable.Batch16Part14
import Vsa.Sim.ObsAvoid

/-!
# M3 Layer-3 — `SnprintfSpec18` : `memmove` fast path (`_mv`) — forward byte loop

The `__ssputs_r` fast path (`0x8001438c`, next file) calls newlib `memmove`
(`0x800069c4 <memmove>`) to copy an iovec into the string sink's cursor buffer.
For the `%lld` flush the arguments are always **disjoint** regions (`dst` in the
caller's destination buffer, `src` on the `svfprintf` C stack) with `1 ≤ n ≤ 31`
(a sign byte or ≤ 20 digits), so the executed path is:

```
  69c4: bgeu a1,a0,69f0     taken when src ≥ dst        ┐ dispatch
  69c8: add  a5,a1,a2       a5 := src + n               │ (disjoint ⇒ one of
  69cc: bgeu a0,a5,69f0     taken when dst ≥ src + n     ┘  the two fires)
  69f0: li   a5,31
  69f4: bltu a5,a2,6a24     NOT taken (n ≤ 31 ⇒ byte path)
  69f8: mv   a5,a0           a5 := dst
  69fc: addi a3,a2,-1        a3 := n - 1
  6a00: beqz a2,6ae0         NOT taken (1 ≤ n)
  6a04: addi a3,a3,1         a3 := n
  6a08: add  a3,a5,a3        a3 := dst + n (end pointer)
  6a0c: lbu  a4,0(a1)        ┐ loop body (5 instrs, back-edge 6a1c → 6a0c
  6a10: addi a5,a5,1         │ while a5 ≠ a3): copy one byte
  6a14: addi a1,a1,1         │ src → dst
  6a18: sb   a4,-1(a5)       ┘
  6a1c: bne  a5,a3,6a0c
  6a20: ret
```

`memmove_fwd_spec` is the total-correctness segment for this path: from the
`memmove` entry with `dst/src/n` in place, regions disjoint (`dst+n ≤ src` or
`src+n ≤ dst`, unsigned), `1 ≤ n ≤ 31`, and the source bytes `bs` pinned in
`m0`, it returns to `ra = r` with

* `[dst, dst+n)` holding exactly the source bytes (`∀ i < n`,
  `mem[dst+i]? = some (bs i)`), and
* every other address still reading `m0` (frame).

Memory bookkeeping reuses the strcpy machinery (`CpyRegions`/`CpyInv`/
`cpyinv_store`, with `len := n-1` so the written window is exactly
`[dst, dst+n)`); the `MemmoveLoaded` code pins survive byte inserts above
`0x80006b00` (the function spans `[0x800069c4, 0x80006aec)`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Guard / pointer bridges -/

/-! ## `MemmoveLoaded` survival above the code region -/

/-! ## Per-site observational steps -/

/-! ## Region / no-wrap side conditions for the forward byte path

`MvRegions dst src n` bundles the disjointness / no-wrap facts for an `n`-byte
copy (`1 ≤ n ≤ 31` — the small-`n` byte path).  The written window is
`[dst, dst+n)`, the read window `[src, src+n)`; both in RAM above the HTIF
window (hence above the `memmove` code, `tohostAddr > 0x80006b00`). -/

/-! ## Blanket ghost-frame predicate (`NotWrittenMv`) + per-class helpers

The forward path writes GPRs `x11` (`a1`), `x13` (`a3`), `x14` (`a4`), `x15`
(`a5`).  `x10` (`a0 = dst`), `x12` (`a2 = n`) and `x1` (`ra`) are preserved. -/
abbrev NotWrittenMv (R : Register) : Prop :=
  (Register.x11 == R) = false ∧ (Register.x13 == R) = false ∧
  (Register.x14 == R) = false ∧ (Register.x15 == R) = false ∧
  (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
  (Register.minstret == R) = false ∧ (Register.minstret_increment == R) = false ∧
  (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
  (Register.mip == R) = false

/-! ## Pointer/window bounds for iteration `i` -/

/-! ## The config-level state predicate at the loop head `0x80006a0c`

`StMv g i r dst src n m0 bs c` holds at byte-loop iteration `i` (`i < n`):
`a0 = dst`, `a1 = src+i`, `a3 = dst+n` (end pointer), `a5 = dst+i`, `x1 = r`,
`CpyInv` at `len := n-1` (window `[dst, dst+n)`). -/

/-! ## One loop body iteration (`0x80006a0c → 0x80006a1c`)

Chains `lbu a4,0(a1) → addi a5,a5,1 → addi a1,a1,1 → sb a4,-1(a5)`. -/

/-! ## The `bne a5,a3` at `0x80006a1c` (loop back-edge / exit to ret) -/

/-! ## Loop invariant, guard, measure -/

/-! ## `ret` (`0x80006a20 → r`) and the described-update postcondition -/

/-! ## Entry dispatch (`0x800069c4 → 0x80006a0c`)

Both disjointness arms funnel to `0x800069f0`:
* `dst+n ≤ src`: `src ≥ᵤ dst`, so the `bgeu a1,a0` at `0x69c4` is taken.
* `src+n ≤ dst`: `src <ᵤ dst` (not taken), then `a5 := src+n` and the
  `bgeu a0,a5` at `0x69cc` is taken.
Then `li a5,31` / `bltu` (byte path, `n ≤ 31`) / `mv a5,a0` / `addi a3,a2,-1` /
`beqz a2` (not taken, `1 ≤ n`) / `addi a3,a3,1` / `add a3,a5,a3` set up the loop. -/

/-! ## The composed forward-path spec -/

end Vsa.Sim
