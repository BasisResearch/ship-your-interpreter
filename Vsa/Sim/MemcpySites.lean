import Vsa.Sim.StepObs
import Vsa.Sim.ExecuteAlu
import Vsa.Sim.ExecuteBranch
import Vsa.Sim.ExecuteLoad
import Vsa.Sim.ExecuteStore
import Vsa.Sim.MemStore
import Vsa.Sim.RegAccess
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part16
import Vsa.Sim.DecodeTable.Batch01Part21
import Vsa.Sim.DecodeTable.Batch02Part23
import Vsa.Sim.DecodeTable.Batch02Part26
import Vsa.Sim.DecodeTable.Batch16Part15
import Vsa.Sim.DecodeTable.Batch16Part16
import Vsa.Sim.DecodeTable.Batch16Part19
import Vsa.Sim.Code.Memcpy
import Vsa.Sim.DivSites

/-!
# Layer 3 — per-site observational step lemmas for `memcpy` (byte-copy path)

One observational-step (`StepObs`) lemma per instruction of newlib `memcpy`'s
**byte-copy path** — the branch the binary takes when the alignment fast-path
does not apply (`(src ^ dst) & 7 ≠ 0` at `0x80006bd4`, jumping to the byte loop
at `0x80006c40`).

The byte path (addresses in `[0x80006c40, 0x80006c60)`):

| pc | word | mnemonic | AST | class |
|----|------|----------|-----|-------|
| c40 | 00050713 | mv a4,a0    | ITYPE(0x000,x10,x14,ADDI) | ALU |
| c44 | ff157ce3 | bgeu a0,a7  | BTYPE(0x1ff8,x17,x10,BGEU) | BRANCH |
| c48 | 0005c783 | lbu a5,0(a1)| LOAD(0x000,x11,x15,unsigned,1) | LOAD |
| c4c | 00170713 | addi a4,a4,1| ITYPE(0x001,x14,x14,ADDI) | ALU |
| c50 | 00158593 | addi a1,a1,1| ITYPE(0x001,x11,x11,ADDI) | ALU |
| c54 | fef70fa3 | sb a5,-1(a4)| STORE(0xfff,x15,x14,1) | STORE |
| c58 | fee898e3 | bne a7,a4   | BTYPE(0x1ff0,x14,x17,BNE) | BRANCH |
| c5c | 00008067 | ret         | JALR(0x000,x1,x0) | JUMP |

BGEU has no generic execute char in `ExecuteBranch.lean` (only up to BLTU), so we
clone `execute_btype_bge_taken`/`_nottaken` here for `bop.BGEU` (guard
`zopz0zKzJ_u` = unsigned `≥`).

A `lbu`'s post-state is a single `x15` insert holding `zero_extend (m := 64) data`
(`data : BitVec (8*1)`, width-1 load); a `sb`'s post-state is a single byte insert
`σ₂.mem.insert a.toNat (extractLsb vdata 7 0)`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code (MemcpyLoaded memcpy_at_80006c40 memcpy_at_80006c44 memcpy_at_80006c48 memcpy_at_80006c4c memcpy_at_80006c50 memcpy_at_80006c54 memcpy_at_80006c58 memcpy_at_80006c5c)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! BGEU execute characters come from `Vsa.Sim.DivSites` (canonical home). -/

/-! ## Byte-word / non-RVC facts (all four bytes little-endian) -/

/-! ## Site 0x80006c40 — `mv a4,a0` = `addi a4,a0,0` (rd = x14, rs1 = x10) -/

/-! ## Site 0x80006c4c — `addi a4,a4,1` (rd = x14, rs1 = x14) -/

/-! ## Site 0x80006c50 — `addi a1,a1,1` (rd = x11, rs1 = x11) -/

/-! ## Site 0x80006c48 — `lbu a5,0(a1)` (LOAD unsigned width 1, rd = x15, rs1 = x11)

The effective address is `a1 + sext 0x000 = a1`. The loaded byte `b : BitVec 8`
(`= data : BitVec (8*1)`) is written to `x15` as `zero_extend (m := 64) b`. -/

/-! ## Site 0x80006c54 — `sb a5,-1(a4)` (STORE width 1, rs2 = x15, rs1 = x14)

Effective address `a4 + sext 0xfff = a4 - 1`. Stores the low byte
`extractLsb v15 7 0` of `a5` (= `x15`). Post memory
`σ.mem.insert (a4-1).toNat (extractLsb v15 7 0)`. -/

/-- The store data slice for width 1: `extractLsb vdata 7 0` (auto-`setWidth (8*1)`). -/
abbrev sbData (vdata : BitVec 64) : BitVec (8 * 1) :=
  Sail.BitVec.extractLsb vdata ((1 *i 8) -i 1) 0

/-! ## Site 0x80006c44 — `bgeu a0,a7` = BTYPE(0x1ff8, x17, x10, BGEU)

Decode: `BTYPE (0x1ff8#13, x17, x10, BGEU)`, rs1 = x10, rs2 = x17. Taken (a0 ≥u a7)
⇒ branch to `pc + sext 0x1ff8 = pc - 8 = 0x80006c3c` (ret). Not-taken (a0 <u a7)
⇒ fall through to `pc + 4 = 0x80006c48` (byte loop). -/

/-! ## Site 0x80006c58 — `bne a7,a4` = BTYPE(0x1ff0, x14, x17, BNE)

Decode: `BTYPE (0x1ff0#13, x14, x17, BNE)`, rs1 = x17, rs2 = x14. Taken (a7 ≠ a4)
⇒ branch to `pc + sext 0x1ff0 = pc - 16 = 0x80006c48` (loop back). Not-taken
(a7 = a4) ⇒ fall through to `pc + 4 = 0x80006c5c` (ret). -/

/-! ## Site 0x80006c5c — `ret` = `jalr x0,ra,0` (rs1 = x1) -/

end Vsa.Sim
