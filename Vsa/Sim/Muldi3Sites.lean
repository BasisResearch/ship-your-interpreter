import Vsa.Sim.StepObs
import Vsa.Sim.ExecuteAlu
import Vsa.Sim.ExecuteBranch
import Vsa.Sim.RegAccess
import Vsa.Sim.DecodeTable.Batch01Part01
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part15
import Vsa.Sim.DecodeTable.Batch01Part23
import Vsa.Sim.DecodeTable.Batch02Part23
import Vsa.Sim.DecodeTable.Batch02Part24
import Vsa.Sim.DecodeTable.Batch04Part09
import Vsa.Sim.DecodeTable.Batch16Part09
import Vsa.Sim.Code.«__muldi3»

/-!
# Layer 3 — per-site observational step lemmas for `__muldi3`

One observational-step (`StepObs`) lemma per instruction of `__muldi3`
(9 instructions at `[0x80004640, 0x80004664)`), each consuming the generated
`__muldi3Loaded` fetch facts (`Vsa/Sim/Code/__muldi3.lean`), the fully-qualified
`DecodeTable` decode lemma, and the relevant `ExecuteAlu`/`ExecuteBranch`
character, assembled in the `DemoStore` style (decode + `rX`/`wX` read-backs +
execute char → the abstract `hexec` the generic `stepObs_*` wrapper wants).

Every lemma is **parity-agnostic**: it takes `i < 2` and produces
`∃ σ' i', Step ⟨σ,i,u⟩ ⟨σ',i',u+1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
ReadsLikePost σ' (sigmaPost_… )`, folding the tick/notick split.

The nine sites and their kinds:
| pc | word | mnemonic | class |
|----|------|----------|-------|
| 40 | 00050613 | mv a2,a0  (addi a2,a0,0)  | ALU ITYPE ADDI (rd x12, rs1 x10) |
| 44 | 00000513 | li a0,0   (addi a0,x0,0)  | ALU ITYPE ADDI (rd x10, rs1 x0) |
| 48 | 0015f693 | andi a3,a1,1              | ALU ITYPE ANDI (rd x13, rs1 x11) |
| 4c | 00068463 | beqz a3,+8 (beq a3,x0)    | BRANCH BEQ (rs1 x13, rs2 x0) |
| 50 | 00c50533 | add a0,a0,a2              | ALU RTYPE ADD (rd x10, rs1 x10, rs2 x12) |
| 54 | 0015d593 | srli a1,a1,1              | ALU SHIFTIOP SRLI (rd x11, rs1 x11) |
| 58 | 00161613 | slli a2,a2,1              | ALU SHIFTIOP SLLI (rd x12, rs1 x12) |
| 5c | fe0596e3 | bnez a1,-20 (bne a1,x0)   | BRANCH BNE (rs1 x11, rs2 x0) |
| 60 | 00008067 | ret (jalr x0,ra,0)        | JUMP jr x0 (rs1 x1) |

Per-site cost: one `hexec` assembly (decode + one/two `rX` read-backs + one `wX`)
+ one `stepObs_*` application. The straight-line ALU sites are ~15 lines each;
the branch sites split taken/not-taken; `ret` is the `stepObs_jr` instantiation.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Common address constants and fetch-side bounds

`__muldi3` sits at `0x80004640`, well inside RAM and below `tohostAddr`
(`0x8001ad00`). The fetch-side bounds (`0x80000000 ≤ pc`, `pc+4 ≤ tohostAddr`,
`pc % 4 = 0`) are decidable at each concrete site pc. -/

/-! ## Site 0x80004640 — `mv a2,a0` = `addi a2,a0,0` (rd = x12, rs1 = x10) -/

/-! ## Site 0x80004644 — `li a0,0` = `addi a0,x0,0` (rd = x10, rs1 = x0) -/

/-! ## Site 0x80004648 — `andi a3,a1,1` (rd = x13, rs1 = x11) -/

/-! ## Site 0x80004650 — `add a0,a0,a2` (rd = x10, rs1 = x10, rs2 = x12) -/

/-! ## Site 0x80004654 — `srli a1,a1,1` (rd = x11, rs1 = x11) -/

/-! ## Site 0x80004658 — `slli a2,a2,1` (rd = x12, rs1 = x12) -/

/-! ## Site 0x8000464c — `beqz a3,+8` = `beq a3,x0` (rs1 = x13, rs2 = x0)

Decode: `BTYPE (0x0008#13, x0, x13, BEQ)`. Taken (a3 = 0) ⇒ branch to
`pc + sext 0x0008 = pc + 8` (skip the `add`). Not-taken (a3 ≠ 0) ⇒ fall through
to `pc + 4`. Both variants below; the loop proof picks by the value of a3. -/

/-! ## Site 0x8000465c — `bnez a1,-20` = `bne a1,x0` (rs1 = x11, rs2 = x0)

Decode: `BTYPE (0x1fec#13, x0, x11, BNE)`. Taken (a1 ≠ 0) ⇒ branch to
`pc + sext 0x1fec = pc - 20 = 0x80004648` (loop back-edge). Not-taken (a1 = 0) ⇒
fall through to `pc + 4 = 0x80004660` (ret). -/

/-! ## Site 0x80004660 — `ret` = `jalr x0,ra,0` (rs1 = x1 = ra)

Decode: `JALR (0x000#12, x1, x0)`. The `x0` write is a no-op; `nextPC`/`PC` are
set to the bit-0-cleared return address `ra + sext 0 = ra` (with bit 0 cleared). -/

end Vsa.Sim
