import Vsa.Sim.StepObs
import Vsa.Sim.ExecuteAlu
import Vsa.Sim.ExecuteBranch
import Vsa.Sim.ExecuteLoad
import Vsa.Sim.ExecuteStore
import Vsa.Sim.MemStore
import Vsa.Sim.RegAccess
import Vsa.Sim.DecodeTable.Batch01Part01
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part10
import Vsa.Sim.DecodeTable.Batch01Part18
import Vsa.Sim.DecodeTable.Batch01Part20
import Vsa.Sim.DecodeTable.Batch01Part29
import Vsa.Sim.DecodeTable.Batch01Part32
import Vsa.Sim.DecodeTable.Batch02Part20
import Vsa.Sim.DecodeTable.Batch02Part23
import Vsa.Sim.DecodeTable.Batch03Part03
import Vsa.Sim.DecodeTable.Batch03Part11
import Vsa.Sim.DecodeTable.Batch03Part20
import Vsa.Sim.DecodeTable.Batch03Part21
import Vsa.Sim.DecodeTable.Batch04Part24
import Vsa.Sim.DecodeTable.Batch05Part15
import Vsa.Sim.DecodeTable.Batch05Part16
import Vsa.Sim.DecodeTable.Batch07Part04
import Vsa.Sim.DecodeTable.Batch07Part06
import Vsa.Sim.DecodeTable.Batch11Part24
import Vsa.Sim.DecodeTable.Batch12Part27
import Vsa.Sim.ValueSites
import Vsa.Sim.Code.Value_equal

/-!
# Layer 3 — per-site observational step lemmas for `value_equal` (@0x8000285c)

`value_equal(Value a, Value b)` takes both 24-byte `Value`s **by reference**
(`a0`/`a1` = pointers). It:

* loads both kind tags (`lw a4,0(a0); lw a5,0(a1)`),
* `bne a5,a4 → 0x8000288c` (`li a0,0; ret`) if the kinds differ,
* `li a4,5; bltu a4,a5 → 0x8000288c` (out-of-range kind guard),
* dispatches through a `.rodata` jump table at `0x80019ef8` (`auipc/addi` build the
  base, `slli a5,a5,2; add a5,a5,a4; lw a5,0(a5); add a5,a5,a4; jr a5`).

Per-kind handlers:

* kind 0 (null)    → 0x800028a8: `li a0,1; ret`
* kind 1 (bool)    → 0x800028b0: `lw a0,8(a0); lw a5,8(a1); sub a0,a0,a5; seqz a0,a0; ret`
* kind 2 (int)     → 0x80002894: `ld a0,8(a0); ld a5,8(a1); sub; seqz; ret`
* kind 3 (str)     → 0x800028c4: `ld a1,8(a1); ld a0,8(a0); <strcmp call>; seqz; ret`
* kind 4 (closure) → 0x80002894 (SAME as int: compares the 8-byte `Closure*` at +8)
* kind 5 (native)  → 0x800028e8: `ld a0,16(a0); ld a5,16(a1); sub; seqz; ret`

The jump-table read at `0x80002880` (`lw a5,0(a5)`) reads `.rodata` *outside* the
code region, so its site takes the four table-entry bytes as explicit hypotheses.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## 0x8000285c — `lw a4,0(a0)` (kind of `a`). Writes `x14`. -/

/-! ## 0x80002860 — `lw a5,0(a1)` (kind of `b`). Writes `x15`. -/

/-! ## 0x80002864 — `bne a5,a4` (rs1=x15, rs2=x14), imm 0x028 → 0x8000288c -/

/-! ## 0x80002868 — `li a4,5` (addi a4,zero,5). Writes `x14 := 5`. -/

/-! ## 0x8000286c — `bltu a4,a5` (rs1=x14, rs2=x15), imm 0x020 → 0x8000288c -/

/-! ## 0x80002870 — `auipc a4,0x17`. Writes `x14 := pc + sext(0x17 <<< 12) = 0x80019870`. -/

/-! ## 0x80002874 — `addi a4,a4,1672` (0x688). Writes `x14 := v14 + sext 0x688`. -/

/-! ## 0x80002878 — `slli a5,a5,2` (rd=x15, rs1=x15, shamt=2). -/

/-! ## 0x8000287c / 0x80002884 — `add a5,a5,a4` (rd=x15, rs1=x15, rs2=x14). -/

/-! ## 0x80002880 — `lw a5,0(a5)` : the JUMP-TABLE read.

`a5 = 0x80019ef8 + 4*kind` (in `.rodata`, outside the code region), so the four
table-entry bytes `t0..t3` are passed as explicit hypotheses (not from
`Value_equalLoaded`). Writes `x15 := sign_extend (t3 ++ t2 ++ t1 ++ t0)`. -/

/-! ## 0x80002888 — `jr a5` : the computed dispatch jump (`jalr x0, 0(a5)`).

`a5 = jumptable-target` = one of the six handler addresses. `stepObs_jr` with
rs1=x15; the target-alignment side condition `htgt` selects a 4-aligned code addr. -/

/-! ## Shared handler-tail instructions -----------------------------------------

`sub a0,a0,a5` (rd=x10, rs1=x10, rs2=x15) and `seqz a0,a0` (sltiu a0,a0,1) appear
in the int/closure, bool, and native tails; `li a0,0/1` and `ret` close the
mismatch/null/tail paths. -/

/-! ### `sub a0,a0,a5` at 0x8000289c (int/closure), 0x800028b8 (bool), 0x800028f0 (native) -/

/-! ### `seqz a0,a0` at 0x800028a0 (int/closure), 0x800028bc (bool), 0x800028f4 (native)

`seqz a0,a0` = `sltiu a0,a0,1`: writes `x10 := cond (v10 = 0) 1 0`. -/

/-! ### `li a0,0` @0x8000288c (mismatch/oob), `li a0,1` @0x800028a8 (null) -/

/-! ### `ret` sites @0x80002890, 0x800028a4, 0x800028ac, 0x800028c0, 0x800028f8 -/

/-! ### Payload loads (int/closure @+8, bool @+8 word, native @+16) -/

end Vsa.Sim
