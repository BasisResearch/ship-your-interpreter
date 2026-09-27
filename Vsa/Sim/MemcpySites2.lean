import Vsa.Sim.StepObs
import Vsa.Sim.ExecuteAlu
import Vsa.Sim.ExecuteBranch
import Vsa.Sim.ExecuteLoad
import Vsa.Sim.ExecuteStore
import Vsa.Sim.MemStore
import Vsa.Sim.RegAccess
import Vsa.Sim.DecodeTable.Batch01Part19
import Vsa.Sim.DecodeTable.Batch01Part25
import Vsa.Sim.DecodeTable.Batch01Part26
import Vsa.Sim.DecodeTable.Batch03Part22
import Vsa.Sim.DecodeTable.Batch03Part24
import Vsa.Sim.DecodeTable.Batch05Part23
import Vsa.Sim.DecodeTable.Batch07Part02
import Vsa.Sim.DecodeTable.Batch16Part13
import Vsa.Sim.DecodeTable.Batch16Part18
import Vsa.Sim.Code.Memcpy
import Vsa.Sim.DivSites
import Vsa.Sim.MemcpySites

/-!
# Layer 3 — per-site observational step lemmas for `memcpy`'s small word-copy loop

One observational-step (`StepObs`) lemma per instruction of the **small word-copy
loop** at `[0x80006bfc, 0x80006c38]` (the 8-byte-granularity copy used when the
source and destination are congruent mod 8, both aligned, and `n` is not large
enough to hit the unrolled ×8 loop).

Loop body / prologue (little-endian byte order noted per word):

| pc  | word     | mnemonic       | AST | class |
|-----|----------|----------------|-----|-------|
| bfc | 00058693 | mv a3,a1       | ITYPE(0x000,x11,x13,ADDI) | ALU |
| c00 | 00070793 | mv a5,a4       | ITYPE(0x000,x14,x15,ADDI) | ALU |
| c04 | 02c77a63 | bgeu a4,a2     | BTYPE(0x0034,x12,x14,BGEU) | BRANCH |
| c08 | 0005b683 | ld a6,0(a3)    | LOAD(0x000,x13,x16,false,8) | LOAD |
| c0c | 00878793 | addi a5,a5,8   | ITYPE(0x008,x15,x15,ADDI) | ALU |
| c10 | 00868693 | addi a3,a3,8   | ITYPE(0x008,x13,x13,ADDI) | ALU |
| c14 | ff07bc23 | sd a6,-8(a5)   | STORE(0xff8,x16,x15,8) | STORE |
| c18 | fec7e8e3 | bltu a5,a2     | BTYPE(0x1ff0,x12,x15,BLTU) | BRANCH |
| c38 | 01176863 | bltu a4,a7     | BTYPE(0x0010,x17,x14,BLTU) | BRANCH |

The `ld`/`sd` sites reuse the width-8 `DemoLoad`/`DemoStore` recipe
(`vmem_read_data_eight` + `execute_load_signed_char`; `vmem_write_addr_8` +
`execute_STORE_char`). BLTU characters come from `ExecuteBranch.lean`
(`execute_btype_bltu_{taken,nottaken}`); BGEU from `Vsa.Sim.DivSites` (as in
`MemcpySites.lean`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code (MemcpyLoaded memcpy_at_80006bfc memcpy_at_80006c00 memcpy_at_80006c04 memcpy_at_80006c08 memcpy_at_80006c0c memcpy_at_80006c10 memcpy_at_80006c14 memcpy_at_80006c18 memcpy_at_80006c38)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Byte-word / non-RVC facts (little-endian) -/

/-! ## Width-8 load/store helpers (little-endian 8-byte value and byte-insert chain) -/

/-- The 8-byte little-endian loaded value at `[a, a+8)`: `b0` is the byte at `a`.
Mirrors `DemoLoad.ldData` (kept local; `DemoLoad` is not imported here). -/
abbrev ldData8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : BitVec (8 * 8) :=
  ((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0

/-- The store-data slice for a width-8 `sd` (the `extractLsb` argument
`execute_STORE_char`'s `hwrite` demands). Mirrors `DemoStore.sdData`. -/
abbrev sdData8 (vdata : BitVec 64) : BitVec (8 * 8) :=
  Sail.BitVec.extractLsb vdata ((8 *i 8) -i 1) 0

/-! ## Site 0x80006bfc — `mv a3,a1` = `addi a3,a1,0` (rd = x13, rs1 = x11) -/

/-! ## Site 0x80006c00 — `mv a5,a4` = `addi a5,a4,0` (rd = x15, rs1 = x14) -/

/-! ## Site 0x80006c0c — `addi a5,a5,8` (rd = x15, rs1 = x15) -/

/-! ## Site 0x80006c10 — `addi a3,a3,8` (rd = x13, rs1 = x13) -/

/-! ## Site 0x80006c08 — `ld a6,0(a3)` (LOAD signed width 8, rd = x16, rs1 = x13)

Effective address `a3 + sext 0x000 = a3`. Loads the 8-byte little-endian value
into `x16 := sign_extend (ldData8 …)` (width-preserving at width 8). Recipe from
`DemoLoad.exec_ld_x11_x2`. -/

/-! ## Site 0x80006c14 — `sd a6,-8(a5)` (STORE width 8, rs2 = x16, rs1 = x15)

Effective address `a5 + sext 0xff8 = a5 - 8` (`sdAddrM8`). Stores the 8 low bytes
of `a6` (= `x16`) little-endian. Post memory is the 8-byte insert chain
`sdMem8 σ₂.mem (sdAddrM8 v15) v16`. Recipe from `DemoStore.exec_sd_x11_x2`. -/

/-! ## Site 0x80006c04 — `bgeu a4,a2` = BTYPE(0x0034, x12, x14, BGEU)

rs1 = x14, rs2 = x12. Taken (a4 ≥u a2) ⇒ `pc + sext 0x0034 = 0x80006c38`. Not-taken
(a4 <u a2) ⇒ fall through to `0x80006c08` (word-loop head). -/

/-! ## Site 0x80006c18 — `bltu a5,a2` = BTYPE(0x1ff0, x12, x15, BLTU)

rs1 = x15, rs2 = x12. Taken (a5 <u a2) ⇒ `pc + sext 0x1ff0 = 0x80006c08` (loop back).
Not-taken (a5 ≥u a2) ⇒ fall through to `0x80006c1c` (loop epilogue). -/

/-! ## Site 0x80006c38 — `bltu a4,a7` = BTYPE(0x0010, x17, x14, BLTU)

rs1 = x14, rs2 = x17. Taken (a4 <u a7) ⇒ `pc + sext 0x0010 = 0x80006c48` (byte loop).
Not-taken (a4 ≥u a7) ⇒ fall through to `0x80006c3c` (ret). -/

end Vsa.Sim
