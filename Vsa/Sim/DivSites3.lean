import Vsa.Sim.DivSites2
import Vsa.Sim.DecodeTable.Batch16Part09
import Vsa.Sim.DecodeTable.Batch15Part28
import Vsa.Sim.DecodeTable.Batch15Part25
import Vsa.Sim.DecodeTable.Batch15Part23
import Vsa.Sim.DecodeTable.Batch11Part21
import Vsa.Sim.DecodeTable.Batch11Part19
import Vsa.Sim.DecodeTable.Batch08Part12
import Vsa.Sim.DecodeTable.Batch04Part02
import Vsa.Sim.DecodeTable.Batch01Part21
import Vsa.Sim.DecodeTable.Batch01Part19
import Vsa.Sim.DecodeTable.Batch01Part10
import Vsa.Sim.DecodeTable.Batch01Part04

/-!
# Layer 3 — remaining wrapper site step lemmas (`__moddi3` body + `__divdi3` fixup arms)

Per-instruction observational-step `Triple`s for the `__moddi3` entry
(`0x80004728`) body `[0x4728, 0x4754]` and the `__divdi3` sign-fixup arms
(`[0x4704, 0x4724]`, physically stored in the `__umoddi3` code region) that were
not yet covered by `Vsa/Sim/DivSites2.lean`. Mechanical instances of the DivSites2
site templates: `stepObs_alu` / `stepObs_branch_{taken,nottaken}` / `stepObs_jal`
/ `stepObs_jr`, threaded through the reused `exec_*` execute helpers.

`neg`/`mv` execute helpers (`exec_mv_t0_ra`, `exec_mv_a0_a1`, `exec_neg_a0`,
`exec_neg_a1`, `exec_neg_a0_a1`) are spec-independent (`DivSites2.lean`) and reused
directly. The branch execute helpers here are parametric in the immediate /
source register, generalising DivSites2's `exec_bltz_a0_*`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Parametric signed-branch execute helpers

`bltz rsX` = `blt rsX,x0` (`BTYPE(imm, rs2 = x0, rs1 = rsX, BLT)`), guard
`zopz0zI_s v 0`. `bgez rsX` = `bge rsX,x0` (`BTYPE(imm, rs2 = x0, rs1 = rsX, BGE)`),
guard `zopz0zKzJ_s v 0`. Both read `rsX` and `x0`, and on the taken side produce
`sigma3_branch_taken σ pc imm`. -/

/-! ## `__moddi3` body sites (0x80004728 – 0x80004754) -/

/-! ### 0x80004728 — `mv t0,ra` = `addi t0,ra,0` (rd = x5, rs1 = x1) -/

/-! ### 0x8000472c — `bltz a1` = `blt a1,x0` (imm 0x0014 → 0x80004740) -/

/-! ### 0x80004730 — `bltz a0` = `blt a0,x0` (imm 0x0018 → 0x80004748) -/

/-! ### 0x80004734 — `jal 0x800046ac` (rd = x1, imm 0x1fff78 → 0x800046ac) -/

/-! ### 0x80004738 — `mv a0,a1` = `addi a0,a1,0` (rd = x10, rs1 = x11) -/

/-! ### 0x8000473c — `jr t0` = `jalr x0,t0,0` (rs1 = x5) -/

/-! ### 0x80004740 — `neg a1,a1` = `sub a1,x0,a1` (rd = x11, rs1 = x0, rs2 = x11) -/

/-! ### 0x80004744 — `bgez a0` = `bge a0,x0` (imm 0x1ff0 → 0x80004734) -/

/-! ### 0x80004748 — `neg a0,a0` = `sub a0,x0,a0` (rd = x10, rs1 = x0, rs2 = x10) -/

/-! ### 0x8000474c — `jal 0x800046ac` (rd = x1, imm 0x1fff60 → 0x800046ac) -/

/-! ### 0x80004750 — `neg a0,a1` = `sub a0,x0,a1` (rd = x10, rs1 = x0, rs2 = x11) -/

/-! ### 0x80004754 — `jr t0` = `jalr x0,t0,0` (rs1 = x5) -/

/-! ## `__divdi3` sign-fixup arm sites (0x800046a8 entry + 0x80004704 – 0x80004724)

The second entry test `0x800046a8` lives in `__divdi3Loaded`; the fixup arms
`[0x4704, 0x4724]` are stored in the `__umoddi3` code region (`__umoddi3Loaded`,
`__umoddi3_at_*`). `bgtz a1` = `blt x0,a1` (`BTYPE(imm, rs2 = x11, rs1 = x0, BLT)`),
guard `zopz0zI_s 0 a1`. -/

/-! ### 0x800046a8 — `bltz a1` = `blt a1,x0` (imm 0x006c → 0x80004714) -/

/-! ### 0x80004704 — `neg a0,a0` = `sub a0,x0,a0` (rd = x10, rs1 = x0, rs2 = x10) -/

/-! ### 0x80004708 — `bgtz a1` = `blt x0,a1` (imm 0x0010 → 0x80004718) -/

/-! ### 0x8000470c — `neg a1,a1` = `sub a1,x0,a1` (rd = x11, rs1 = x0, rs2 = x11) -/

/-! ### 0x80004714 — `neg a1,a1` = `sub a1,x0,a1` (rd = x11, rs1 = x0, rs2 = x11) -/

/-! ### 0x80004718 — `mv t0,ra` = `addi t0,ra,0` (rd = x5, rs1 = x1) -/

/-! ### 0x8000471c — `jal 0x800046ac` (rd = x1, imm 0x1fff90 → 0x800046ac) -/

/-! ### 0x80004720 — `neg a0,a0` = `sub a0,x0,a0` (rd = x10, rs1 = x0, rs2 = x10) -/

/-! ### 0x80004724 — `jr t0` = `jalr x0,t0,0` (rs1 = x5) -/

end Vsa.Sim
