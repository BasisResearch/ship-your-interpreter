import Vsa.Sim.StepObs
import Vsa.Sim.ExecuteAlu
import Vsa.Sim.ExecuteBranch
import Vsa.Sim.ExecuteLoad
import Vsa.Sim.ExecuteStore
import Vsa.Sim.MemStore
import Vsa.Sim.MemLoadTotal
import Vsa.Sim.RegAccess
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part15
import Vsa.Sim.DecodeTable.Batch01Part16
import Vsa.Sim.DecodeTable.Batch01Part21
import Vsa.Sim.DecodeTable.Batch01Part27
import Vsa.Sim.DecodeTable.Batch01Part29
import Vsa.Sim.DecodeTable.Batch02Part23
import Vsa.Sim.DecodeTable.Batch02Part27
import Vsa.Sim.DecodeTable.Batch03Part02
import Vsa.Sim.DecodeTable.Batch03Part06
import Vsa.Sim.DecodeTable.Batch03Part09
import Vsa.Sim.DecodeTable.Batch03Part12
import Vsa.Sim.DecodeTable.Batch03Part13
import Vsa.Sim.DecodeTable.Batch03Part16
import Vsa.Sim.DecodeTable.Batch03Part21
import Vsa.Sim.DecodeTable.Batch04Part03
import Vsa.Sim.DecodeTable.Batch04Part16
import Vsa.Sim.DecodeTable.Batch04Part17
import Vsa.Sim.DecodeTable.Batch04Part18
import Vsa.Sim.DecodeTable.Batch04Part19
import Vsa.Sim.DecodeTable.Batch04Part22
import Vsa.Sim.DecodeTable.Batch04Part23
import Vsa.Sim.DecodeTable.Batch04Part25
import Vsa.Sim.DecodeTable.Batch04Part26
import Vsa.Sim.DecodeTable.Batch04Part32
import Vsa.Sim.DecodeTable.Batch05Part01
import Vsa.Sim.DecodeTable.Batch06Part23
import Vsa.Sim.DecodeTable.Batch06Part24
import Vsa.Sim.DecodeTable.Batch06Part25
import Vsa.Sim.DecodeTable.Batch07Part06
import Vsa.Sim.DecodeTable.Batch07Part27
import Vsa.Sim.DecodeTable.Batch09Part09
import Vsa.Sim.DecodeTable.Batch13Part06
import Vsa.Sim.DecodeTable.Batch15Part25
import Vsa.Sim.DecodeTable.Batch16Part10
import Vsa.Sim.DecodeTable.Batch16Part15
import Vsa.Sim.DecodeTable.Batch16Part18
import Vsa.Sim.DecodeTable.Batch16Part26
import Vsa.Sim.StrlenMagic
import Vsa.Sim.Code.Strcpy

/-!
# Layer 3 — per-site observational step lemmas for `strcpy`

One `StepObs` lemma per instruction of newlib `strcpy`
(55 instructions at `[0x80006dc4, 0x80006ea0)`), following `StrlenSites.lean` /
`StrcmpSites.lean` verbatim. Branch sites are split taken/nottaken.

Register aliases: a0=x10, a1=x11, a2=x12, a3=x13, a4=x14, a5=x15, a6=x16.

Loads: the two `ld a4,0(…)` word loads use the TOTAL 8-byte chain
(`vmem_read_data_eight_total`); the byte-tail/head `lbu` loads use the width-1
`some`-hyp chain (`vmem_read_data_one`).

Stores: the aligned `sd a4,0(a2)` word store uses the width-8 `vmem_write_addr_8`
chain; the byte `sb` stores use the width-1 `vmem_write_addr_1` chain (the
`DemoStore`/`MemcpySites` recipe). Store sites plug into `stepObs_store` and carry
`σ'.mem = m'` (the described insert chain).

Segment map (control flow):
* entry / alignment test (`0xdc4…dcc`): `or a5,a0,a1`; `andi a5,a5,7`;
  `bnez a5,0xe7c` (misaligned → byte head)
* magic setup (`0xdd0…df8`): `lui a5,0x7f7f8`; `addi a5,a5,-129` (a5 = 0x7f7f7f7f);
  `ld a4,0(a1)`; `slli a3,a5,0x20`; `add a3,a3,a5` (a3 = magic64);
  magic `a6 = ((a4&a3)+a3) | a4 | a3`; `li a5,-1`; `mv a2,a0`
* word loop (`0xdfc…e20`): `bne a6,a5,0xe24` (zero byte → byte tail); else
  `addi a1,a1,8`; `sd a4,0(a2)`; `ld a4,0(a1)`; `addi a2,a2,8`; magic on new a4;
  `beq a5,a6,0xe00` (loop back)
* byte tail (`0xe24…e78`): unrolled `lbu`/`sb`/`beqz` chain copying up to 7 bytes,
  with `bnez a4,0xe98` at the end; `ret`
* byte head (`0xe7c…e94`): `mv a5,a0`; `lbu a4,0(a1)`; `addi a5,a5,1;
  addi a1,a1,1`; `sb a4,-1(a5)`; `bnez a4,0xe80` (loop); `ret`
* NUL finisher (`0xe98…e9c`): `sb zero,7(a2)`; `ret`
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code (StrcpyLoaded)
open Vsa.Sim.DecodeTable

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Shared execute helpers (mirrors `StrcmpSites.lean`; re-declared here since
that file is not imported). Each lifts the register `some`-hypotheses through
`afterNextPC ∘ afterPrelude` and feeds the matching `execute_*_char`. Generic
helpers abstract the write target `σ'` to dodge the `RegisterType rd` coupling. -/

/-! ### Store helpers (`DemoStore`/`MemcpySites` recipe)

`sb` = width-1 `vmem_write_addr_1`; `sd` = width-8 `vmem_write_addr_8`. Both
produce `sigma3_store σ pc m'` with `m'` the described insert chain; the site
carries `σ'.mem = m'` through `stepObs_store`. -/

/-! ### Concrete RTYPE helpers for the two magic blocks (a6=x16 / a5=x15) -/

/-! ### Site 0x80006dc4 — `or a5,a0,a1` -/

/-! ### Site 0x80006dc8 — `andi a5,a5,7` -/

/-! ### Site 0x80006dcc — `bnez a5,0x80006e7c` (misaligned → byte head) -/

/-! ### Site 0x80006dd0 — `lui a5,0x7f7f8` -/

/-! ### Site 0x80006dd4 — `addi a5,a5,-129` -/

/-! ### Site 0x80006dd8 — `ld a4,0(a1)` (TOTAL 8-byte load) -/

/-! ### Site 0x80006ddc — `slli a3,a5,0x20` -/

/-! ### Site 0x80006de0 — `add a3,a3,a5` -/

/-! ### Site 0x80006de4 — `and a6,a4,a3` -/

/-! ### Site 0x80006de8 — `add a6,a6,a3` -/

/-! ### Site 0x80006dec — `or a6,a6,a4` -/

/-! ### Site 0x80006df0 — `or a6,a6,a3` -/

/-! ### Site 0x80006df4 — `li a5,-1` -/

/-! ### Site 0x80006df8 — `mv a2,a0` -/

/-! ### Site 0x80006dfc — `bne a6,a5,0x80006e24` (zero byte → byte tail) -/

/-! ### Site 0x80006e00 — `addi a1,a1,8` -/

/-! ### Site 0x80006e04 — `sd a4,0(a2)` (width-8 sd) -/

/-! ### Site 0x80006e08 — `ld a4,0(a1)` (TOTAL 8-byte load) -/

/-! ### Site 0x80006e0c — `addi a2,a2,8` -/

/-! ### Site 0x80006e10 — `and a5,a4,a3` -/

/-! ### Site 0x80006e14 — `add a5,a5,a3` -/

/-! ### Site 0x80006e18 — `or a5,a5,a4` -/

/-! ### Site 0x80006e1c — `or a5,a5,a3` -/

/-! ### Site 0x80006e20 — `beq a5,a6,0x80006e00` (loop back) -/

/-! ### Site 0x80006e24 — `lbu a5,0(a1)` (width-1 lbu) -/

/-! ### Site 0x80006e28 — `lbu a4,1(a1)` (width-1 lbu) -/

/-! ### Site 0x80006e2c — `lbu a3,2(a1)` (width-1 lbu) -/

/-! ### Site 0x80006e30 — `sb a5,0(a2)` (width-1 sb) -/

/-! ### Site 0x80006e34 — `beqz a5,0x80006e78` -/

/-! ### Site 0x80006e38 — `sb a4,1(a2)` (width-1 sb) -/

/-! ### Site 0x80006e3c — `beqz a4,0x80006e78` -/

/-! ### Site 0x80006e40 — `lbu a5,3(a1)` (width-1 lbu) -/

/-! ### Site 0x80006e44 — `sb a3,2(a2)` (width-1 sb) -/

/-! ### Site 0x80006e48 — `beqz a3,0x80006e78` -/

/-! ### Site 0x80006e4c — `lbu a4,4(a1)` (width-1 lbu) -/

/-! ### Site 0x80006e50 — `sb a5,3(a2)` (width-1 sb) -/

/-! ### Site 0x80006e54 — `beqz a5,0x80006e78` -/

/-! ### Site 0x80006e58 — `lbu a5,5(a1)` (width-1 lbu) -/

/-! ### Site 0x80006e5c — `sb a4,4(a2)` (width-1 sb) -/

/-! ### Site 0x80006e60 — `beqz a4,0x80006e78` -/

/-! ### Site 0x80006e64 — `lbu a4,6(a1)` (width-1 lbu) -/

/-! ### Site 0x80006e68 — `sb a5,5(a2)` (width-1 sb) -/

/-! ### Site 0x80006e6c — `beqz a5,0x80006e78` -/

/-! ### Site 0x80006e70 — `sb a4,6(a2)` (width-1 sb) -/

/-! ### Site 0x80006e74 — `bnez a4,0x80006e98` (→ NUL finisher) -/

/-! ### Site 0x80006e78 — `ret` = `jr x1,0` -/

/-! ### Site 0x80006e7c — `mv a5,a0` -/

/-! ### Site 0x80006e80 — `lbu a4,0(a1)` (width-1 lbu) -/

/-! ### Site 0x80006e84 — `addi a5,a5,1` -/

/-! ### Site 0x80006e88 — `addi a1,a1,1` -/

/-! ### Site 0x80006e8c — `sb a4,-1(a5)` (width-1 sb) -/

/-! ### Site 0x80006e90 — `bnez a4,0x80006e80` (loop) -/

/-! ### Site 0x80006e94 — `ret` = `jr x1,0` -/

/-! ### Site 0x80006e98 — `sb zero,7(a2)` (width-1 sb) -/

/-! ### Site 0x80006e9c — `ret` = `jr x1,0` -/

end Vsa.Sim
