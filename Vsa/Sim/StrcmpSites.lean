import Vsa.Sim.StepObs
import Vsa.Sim.ExecuteAlu
import Vsa.Sim.ExecuteBranch
import Vsa.Sim.ExecuteLoad
import Vsa.Sim.MemLoadTotal
import Vsa.Sim.RegAccess
import Vsa.Sim.DecodeTable.Batch01Part01
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part09
import Vsa.Sim.DecodeTable.Batch01Part18
import Vsa.Sim.DecodeTable.Batch01Part20
import Vsa.Sim.DecodeTable.Batch01Part21
import Vsa.Sim.DecodeTable.Batch02Part22
import Vsa.Sim.DecodeTable.Batch02Part23
import Vsa.Sim.DecodeTable.Batch03Part13
import Vsa.Sim.DecodeTable.Batch03Part16
import Vsa.Sim.DecodeTable.Batch03Part20
import Vsa.Sim.DecodeTable.Batch03Part21
import Vsa.Sim.DecodeTable.Batch04Part03
import Vsa.Sim.DecodeTable.Batch04Part16
import Vsa.Sim.DecodeTable.Batch04Part30
import Vsa.Sim.DecodeTable.Batch05Part01
import Vsa.Sim.DecodeTable.Batch05Part03
import Vsa.Sim.DecodeTable.Batch05Part14
import Vsa.Sim.DecodeTable.Batch05Part15
import Vsa.Sim.DecodeTable.Batch05Part16
import Vsa.Sim.DecodeTable.Batch05Part17
import Vsa.Sim.DecodeTable.Batch06Part04
import Vsa.Sim.DecodeTable.Batch06Part21
import Vsa.Sim.DecodeTable.Batch06Part22
import Vsa.Sim.DecodeTable.Batch06Part23
import Vsa.Sim.DecodeTable.Batch07Part03
import Vsa.Sim.DecodeTable.Batch07Part06
import Vsa.Sim.DecodeTable.Batch07Part10
import Vsa.Sim.DecodeTable.Batch07Part11
import Vsa.Sim.DecodeTable.Batch08Part02
import Vsa.Sim.DecodeTable.Batch09Part10
import Vsa.Sim.DecodeTable.Batch09Part17
import Vsa.Sim.DecodeTable.Batch09Part18
import Vsa.Sim.DecodeTable.Batch09Part28
import Vsa.Sim.DecodeTable.Batch09Part29
import Vsa.Sim.DecodeTable.Batch11Part22
import Vsa.Sim.DecodeTable.Batch11Part25
import Vsa.Sim.DecodeTable.Batch15Part02
import Vsa.Sim.DecodeTable.Batch15Part27
import Vsa.Sim.DecodeTable.Batch16Part05
import Vsa.Sim.DecodeTable.Batch16Part09
import Vsa.Sim.DecodeTable.Batch16Part25
import Vsa.Sim.StrlenMagic
import Vsa.Sim.Code.Strcmp

/-!
# Layer 3 — per-site observational step lemmas for `strcmp`

One `StepObs` lemma per instruction of newlib `strcmp`
(75 instructions at `[0x80006ea0, 0x80006fcc)`), following `StrlenSites.lean`
verbatim: each site = the fully-qualified `DecodeTable` decode lemma + the
`rX`/`wX` read-backs + the matching `ExecuteAlu`/`ExecuteBranch`/`ExecuteLoad`
character, assembled into the abstract `hexec` the generic `stepObs_*` wrapper
wants, and closed by one `stepObs_*` application. Branch sites are split
taken/nottaken.

Register aliases: t0=x5, t1=x6, t2=x7, a0=x10, a1=x11, a2=x12, a3=x13,
a4=x14, a5=x15.

Loads: every `ld` here is the word-wise NUL-scanning load whose trailing bytes
may be unmapped, so all `ld` sites use the TOTAL 8-byte chain
(`vmem_read_data_eight_total`), value `sign_extend (ldBytesT σ₂ addr)`. The two
`lbu` byte-loop sites read mapped bytes, so they use the width-1 `some`-hyp chain
(`vmem_read_data_one`).

Segment map (control flow):
* entry / alignment test (`0xea0…eac`): `or a4,a0,a1`; `li t2,-1`;
  `andi a4,a4,7`; `bnez a4,0xf84` (misaligned → byte loop)
* mask setup (`0xeb0…eb4`): `auipc a5,0x14`; `ld a5,-560(a5)` (load `mask`
  = 0x7f7f7f7f7f7f7f7f)
* word loop, 3 unrolled iterations each `ld a2,k(a0); ld a3,k(a1)`, magic
  `t0 = ((a2&a5)+a5) | a2 | a5`, `bne t0,t2` (zero byte? → tail), `bne a2,a3`
  (differ? → lane compare):
  * iter0 (`0xeb8…ed4`), iter1 (`0xed8…ef4`), iter2 (`0xef8…f10`)
  * `0xf14…f1c`: `addi a0,a0,24`; `addi a1,a1,24`; `beq a2,a3,0xeb8` (loop back)
* lane compare (`0xf20…f80`): shift-left probes to find differing byte, then
  `srli …,0x30`; `sub a0,a4,a5`; `zext.b a1,a0`; `bnez a1`; `ret` (twice), and
  the `zext.b a4;zext.b a5;sub;ret` finisher
* byte loop (`0xf84…fa0`): `lbu a2,0(a0); lbu a3,0(a1)`; `addi a0,a0,1;
  addi a1,a1,1`; `bne a2,a3` (differ→exit); `bnez a2,0xf84` (loop); `sub a0,a2,a3; ret`
* word-loop exit blocks (`0xfa4…fc8`): three `addi …,8/16; bne a2,a3,0xf84`
  fall-throughs and `li a0,0; ret` equal-return tails
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code (StrcmpLoaded)
open Vsa.Sim.DecodeTable

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Shared execute helpers

Concrete per-mnemonic execute helpers (mirroring `StrlenSites.lean`): each takes
the register `some`-hypotheses on `σ`, lifts them through `afterNextPC ∘
afterPrelude` via `get?_afterNextPC`, and feeds the matching `execute_*_char`.
Register combinations that recur across the three unrolled word-loop iterations
share a single helper. -/

/-! ## Entry / alignment test (`0x80006ea0 … 0x80006eac`) -/

/-! ### Site 0x80006ea0 — `or a4,a0,a1` -/

/-! ### Site 0x80006ea4 — `li t2,-1` -/

/-! ### Site 0x80006ea8 — `andi a4,a4,7` -/

/-! ### Site 0x80006eac — `bnez a4,0x80006f84` (misaligned → byte loop) -/

/-! ### Site 0x80006eb0 — `auipc a5,0x14` -/

/-! ### Site 0x80006eb4 — `ld a5,-560(a5)` (load mask) (TOTAL 8-byte load) -/

/-! ### Site 0x80006eb8 — `ld a2,0(a0)` (TOTAL 8-byte load) -/

/-! ### Site 0x80006ebc — `ld a3,0(a1)` (TOTAL 8-byte load) -/

/-! ### Site 0x80006ec0 — `and t0,a2,a5` = `and x5,x12,x15` -/

/-! ### Site 0x80006ec4 — `or t1,a2,a5` = `or x6,x12,x15` -/

/-! ### Site 0x80006ec8 — `add t0,t0,a5` = `add x5,x5,x15` -/

/-! ### Site 0x80006ecc — `or t0,t0,t1` = `or x5,x5,x6` -/

/-! ### Site 0x80006ed0 — `bne t0,t2,0x80006fac` (zero byte → exit0) -/

/-! ### Site 0x80006ed4 — `bne a2,a3,0x80006f20` (differ → lane compare) -/

/-! ### Site 0x80006ed8 — `ld a2,8(a0)` (TOTAL 8-byte load) -/

/-! ### Site 0x80006edc — `ld a3,8(a1)` (TOTAL 8-byte load) -/

/-! ### Site 0x80006ee0 — `and t0,a2,a5` = `and x5,x12,x15` -/

/-! ### Site 0x80006ee4 — `or t1,a2,a5` = `or x6,x12,x15` -/

/-! ### Site 0x80006ee8 — `add t0,t0,a5` = `add x5,x5,x15` -/

/-! ### Site 0x80006eec — `or t0,t0,t1` = `or x5,x5,x6` -/

/-! ### Site 0x80006ef0 — `bne t0,t2,0x80006fa4` (zero byte → exit1) -/

/-! ### Site 0x80006ef4 — `bne a2,a3,0x80006f20` (differ → lane compare) -/

/-! ### Site 0x80006ef8 — `ld a2,16(a0)` (TOTAL 8-byte load) -/

/-! ### Site 0x80006efc — `ld a3,16(a1)` (TOTAL 8-byte load) -/

/-! ### Site 0x80006f00 — `and t0,a2,a5` = `and x5,x12,x15` -/

/-! ### Site 0x80006f04 — `or t1,a2,a5` = `or x6,x12,x15` -/

/-! ### Site 0x80006f08 — `add t0,t0,a5` = `add x5,x5,x15` -/

/-! ### Site 0x80006f0c — `or t0,t0,t1` = `or x5,x5,x6` -/

/-! ### Site 0x80006f10 — `bne t0,t2,0x80006fb8` (zero byte → exit2) -/

/-! ### Site 0x80006f14 — `addi a0,a0,24` -/

/-! ### Site 0x80006f18 — `addi a1,a1,24` -/

/-! ### Site 0x80006f1c — `beq a2,a3,0x80006eb8` (loop back) -/

/-! ### Site 0x80006f20 — `slli a4,a2,0x30` -/

/-! ### Site 0x80006f24 — `slli a5,a3,0x30` -/

/-! ### Site 0x80006f28 — `bne a4,a5,0x80006f5c` -/

/-! ### Site 0x80006f2c — `slli a4,a2,0x20` -/

/-! ### Site 0x80006f30 — `slli a5,a3,0x20` -/

/-! ### Site 0x80006f34 — `bne a4,a5,0x80006f5c` -/

/-! ### Site 0x80006f38 — `slli a4,a2,0x10` -/

/-! ### Site 0x80006f3c — `slli a5,a3,0x10` -/

/-! ### Site 0x80006f40 — `bne a4,a5,0x80006f5c` -/

/-! ### Site 0x80006f44 — `srli a4,a2,0x30` -/

/-! ### Site 0x80006f48 — `srli a5,a3,0x30` -/

/-! ### Site 0x80006f4c — `sub a0,a4,a5` -/

/-! ### Site 0x80006f50 — `zext.b a1,a0` -/

/-! ### Site 0x80006f54 — `bnez a1,0x80006f74` -/

/-! ### Site 0x80006f58 — `ret` = `jr x1,0` -/

/-! ### Site 0x80006f5c — `srli a4,a4,0x30` -/

/-! ### Site 0x80006f60 — `srli a5,a5,0x30` -/

/-! ### Site 0x80006f64 — `sub a0,a4,a5` -/

/-! ### Site 0x80006f68 — `zext.b a1,a0` -/

/-! ### Site 0x80006f6c — `bnez a1,0x80006f74` -/

/-! ### Site 0x80006f70 — `ret` = `jr x1,0` -/

/-! ### Site 0x80006f74 — `zext.b a4,a4` -/

/-! ### Site 0x80006f78 — `zext.b a5,a5` -/

/-! ### Site 0x80006f7c — `sub a0,a4,a5` -/

/-! ### Site 0x80006f80 — `ret` = `jr x1,0` -/

/-! ### Site 0x80006f84 — `lbu a2,0(a0)` (width-1 lbu) -/

/-! ### Site 0x80006f88 — `lbu a3,0(a1)` (width-1 lbu) -/

/-! ### Site 0x80006f8c — `addi a0,a0,1` -/

/-! ### Site 0x80006f90 — `addi a1,a1,1` -/

/-! ### Site 0x80006f94 — `bne a2,a3,0x80006f9c` (differ → exit) -/

/-! ### Site 0x80006f98 — `bnez a2,0x80006f84` (loop) -/

/-! ### Site 0x80006f9c — `sub a0,a2,a3` -/

/-! ### Site 0x80006fa0 — `ret` = `jr x1,0` -/

/-! ### Site 0x80006fa4 — `addi a0,a0,8` -/

/-! ### Site 0x80006fa8 — `addi a1,a1,8` -/

/-! ### Site 0x80006fac — `bne a2,a3,0x80006f84` -/

/-! ### Site 0x80006fb0 — `li a0,0` -/

/-! ### Site 0x80006fb4 — `ret` = `jr x1,0` -/

/-! ### Site 0x80006fb8 — `addi a0,a0,16` -/

/-! ### Site 0x80006fbc — `addi a1,a1,16` -/

/-! ### Site 0x80006fc0 — `bne a2,a3,0x80006f84` -/

/-! ### Site 0x80006fc4 — `li a0,0` -/

/-! ### Site 0x80006fc8 — `ret` = `jr x1,0` -/

end Vsa.Sim
