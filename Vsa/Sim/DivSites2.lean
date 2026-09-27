import Vsa.Sim.DivLoops
import Vsa.Sim.Code.«__umoddi3»
import Vsa.Sim.Code.«__divdi3»
import Vsa.Sim.Code.«__moddi3»
import Vsa.Sim.DecodeTable.Batch15Part32
import Vsa.Sim.DecodeTable.Batch15Part28
import Vsa.Sim.DecodeTable.Batch08Part12
import Vsa.Sim.DecodeTable.Batch01Part10
import Vsa.Sim.DecodeTable.Batch01Part19
import Vsa.Sim.DecodeTable.Batch01Part04

/-!
# Layer 3 — site step lemmas OUTSIDE the shared `__hidden___udivdi3` core

Per-instruction observational-step `Triple`s for every instruction reachable
from the three wrapper entries `__divdi3` (0x800046a4), `__umoddi3` (0x800046f4)
and `__moddi3` (0x80004728) that lies OUTSIDE the shared unsigned core
`[0x800046ac, 0x800046f4)` (which `Vsa/Sim/DivSites.lean` + `DivSpec.lean` +
`DivLoops.lean` already handle).

Each wrapper block negates operands (`neg = sub rd,x0,rs`), saves the return
address to `t0` (`mv t0,ra`), calls the core (`jal`), fixes up the sign of the
result (`neg`), and returns via `t0` (`jr t0`). These sites use the `stepObs_jal`
/ `stepObs_j` / `stepObs_jr` wrappers (first use of `jal`/`j` in this project),
so we also build the `jal` observation consumers `obs_jal_*` here (analogues of
`obs_alu_*` in `Muldi3Spec`).

These lemmas are stated over the udivdi3 `Ust` predicate (`DivSpec.lean`) where
the PC lies in the core, and over local wrapper predicates elsewhere; but since
the wrapper code is loaded by a DIFFERENT `Loaded` predicate than the core, each
site lemma is stated as a bare machine-stepping `site_*`-style existential and the
config-level `Triple` glue lives in `DivSpec2.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## `jal` observation consumers (analogue of `obs_alu_*`)

From a `jal` observation `ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link)`
read framing fields off `σ'`: `obs_jal_pc` gives PC := pc + sext imm; `obs_jal_rd`
gives rd_reg := link; `obs_jal_other` reads any register outside the write-set
from `σ`; `obs_jal_minstret` gives minstret defined. -/

/-! ## `__umoddi3` entry sites (0x800046f4 – 0x80004700)

```
f4 mv t0,ra      ; t0 := ra           (ITYPE addi t0,ra,0; rd x5, rs1 x1)
f8 jal 46ac      ; ra := f8+4; → 46ac (JAL rd x1, imm 0x1fffb4)
fc mv a0,a1      ; a0 := a1           (ITYPE addi a0,a1,0; rd x10, rs1 x11)
00 jr t0         ; PC := t0           (JALR rd x0, rs1 x5)
```
-/

/-! ### 0x800046f4 — `mv t0,ra` = `addi t0,ra,0` (rd = x5, rs1 = x1) -/

/-! ### 0x800046f8 — `jal 0x800046ac` (rd = x1, imm 0x1fffb4 → 0x800046ac) -/

/-! ### 0x800046fc — `mv a0,a1` = `addi a0,a1,0` (rd = x10, rs1 = x11) -/

/-! ### 0x80004700 — `jr t0` = `jalr x0,t0,0` (rs1 = x5) -/

/-! ## `neg` helper (`neg rd,rs = sub rd,x0,rs`, RTYPE with rs1 = x0)

`neg a0,a0` = `RTYPE(rs2 = x10, rs1 = x0, rd = x10, SUB)`: `x10 := 0 - a0`.
`neg a1,a1` similarly on x11. The `rs1 = x0` read uses `rX_bits_zero`. -/

/-! ## `__divdi3` entry sites (0x800046a4 / 0x800046a8) — the two sign tests

```
a4 bltz a0,4704   ; BLT a0,x0 : if a0 < 0 (signed) → 0x80004704
a8 bltz a1,4714   ; BLT a1,x0 : if a1 < 0 (signed) → 0x80004714
```
Both fall through into the shared core at 0x800046ac. -/

/-! ### 0x800046a4 — `bltz a0` = `blt a0,x0` (rs1 = x10, rs2 = x0), imm 0x0060 → 0x80004704 -/

/-! ### 0x80004710 — `j 0x800046ac` = `jal x0, imm 0x1fff9c` (unconditional) -/

end Vsa.Sim
