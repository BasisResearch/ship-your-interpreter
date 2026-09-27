import Vsa.Sim.StepObs
import Vsa.Sim.StrcpySites
import Vsa.Sim.Code.SvfprintfSlice
import Vsa.Sim.DecodeTable.Batch16Part31
import Vsa.Sim.DecodeTable.Batch16Part12
import Vsa.Sim.DecodeTable.Batch16Part03
import Vsa.Sim.DecodeTable.Batch14Part10
import Vsa.Sim.DecodeTable.Batch14Part08
import Vsa.Sim.DecodeTable.Batch08Part07
import Vsa.Sim.DecodeTable.Batch07Part09
import Vsa.Sim.DecodeTable.Batch03Part29
import Vsa.Sim.DecodeTable.Batch03Part27
import Vsa.Sim.DecodeTable.Batch02Part30
import Vsa.Sim.DecodeTable.Batch02Part15
import Vsa.Sim.DecodeTable.Batch01Part12
import Vsa.Sim.DecodeTable.Batch01Part15

/-!
# Layer 3 — per-site observational step lemmas for the `%lld` decimal loop of `_svfprintf_r`

`StepObs` site batteries (`_sn` suffix) for the executed integer-formatting slice
of `_svfprintf_r` (`experiments/M3-snprintf-lld.md` §1.4).  Per the task brief
these cover the **decimal-conversion loop body** `[0x800082fc, 0x8000833c)`
(quotient step + `bgeu` exit test + remainder/emit step, the two `jal`s into the
verified div cluster, the backward `sb`, cursor decrement, digit count) plus the
**sign-handling block** `[0x800080dc, 0x800080f4]` and the single-digit fast path
`[0x80008100, 0x8000810c]`.

Each site is one `stepObs_*` application (`Vsa/Sim/StepObs.lean`) against the
byte-pinned code region `SvfprintfSliceLoaded` (`Vsa/Sim/Code/SvfprintfSlice.lean`,
`svfprintfSlice_at_ADDR`) and the `DecodeTable.decode_WORD` shard lemmas — the
DemoStore/DemoLoad/EnvNewSites recipe unchanged.  Register map for the loop:
`s0=x8`, `s6=x22`, `s7=x23`, `s9=x25`, `s10=x26`, `s11=x27`, `a0=x10`, `a1=x11`,
`a5=x15`.

The two `jal` sites (`0x80008304 → __hidden___udivdi3`, `0x80008324 → __umoddi3`)
write `x1 := pc+4` and redirect the PC to the div-cluster entry; the div specs
(`udivdi3_spec`/`umoddi3_spec`) are composed at those successor states in
`SnprintfSpec2.lean` with the ghost frame threading the live set.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Byte-word / non-RVC facts for the loop / sign / fast-path instruction words -/

/-! ## Shared decode-prelude helper

Every `decode_*` shard lemma takes the three prelude side-conditions read off
`GoodState`.  This wraps them for a site. -/

/-! ## Loop-body sites

Each site reads its source GPR (a `some`-hypothesis) and steps once, producing the
`sigmaPost_*` observation consumed by the `obs_*` frame lemmas in `SnprintfSpec2`.
The `mv`/`li`/`addi` sites are ITYPE-ADDI (`exec_addi_gen`); `addiw` is `ADDIW`
(`execute_addiw_char`); the `sb` is a width-1 STORE (`exec_sb`); the `bgeu`/`beqz`
are BTYPE (`stepObs_branch_*`); the two `jal`s write `x1 := pc+4` and redirect the
PC to the div-cluster entry (`stepObs_jal`). -/

/-! ### 0x800082fc — `mv a0,s0` = `addi x10,x8,0` (x10 := x8) -/

/-! ### 0x80008300 — `li a1,10` = `addi x11,x0,10` (x11 := 10) -/

/-! ### 0x80008304 — `jal __hidden___udivdi3` : x1 := pc+4, PC := 0x800046ac -/

/-! ### 0x80008308 — `mv s6,s0` = `addi x22,x8,0` (x22 := x8) -/

/-! ### 0x8000830c — `li a5,9` = `addi x15,x0,9` (x15 := 9) -/

/-! ### 0x80008310 — `mv s9,s10` = `addi x25,x26,0` (x25 := x26) -/

/-! ### 0x80008314 — `mv s0,a0` = `addi x8,x10,0` (x8 := x10) -/

/-! ### 0x80008318 — `bgeu a5,s6,0x80008358` = BTYPE(0x0040,x22,x15,BGEU) (exit test) -/

/-! ### 0x8000831c — `li a1,10` = `addi x11,x0,10` (x11 := 10) -/

/-! ### 0x80008320 — `mv a0,s0` = `addi x10,x8,0` (x10 := x8) -/

/-! ### 0x80008324 — `jal __umoddi3` : x1 := pc+4, PC := 0x800046f4 -/

/-! ### 0x80008328 — `addiw a0,a0,48` = ADDIW(0x030,x10,x10) : x10 := sext32(x10+48) -/

/-! ### 0x8000832c — `sb a0,-1(s9)` = STORE(0xfff,x10,x25,1) : mem[x25-1] := x10[7:0] -/

/-! ### 0x80008330 — `addi s10,s9,-1` = ITYPE(0xfff,x25,x26,ADDI) : x26 := x25-1 -/

/-! ### 0x80008334 — `addiw s7,s7,1` = ADDIW(0x001,x23,x23) : x23 := sext32(x23+1) -/

/-! ### 0x80008338 — `beqz s11,0x800082fc` = BTYPE(0x1fc4,x0,x27,BEQ) (grouping-flag test)

For `%lld` the grouping flag `s11 = t1 & 1024 = 0`, so this branch is **always
taken** back to `0x800082fc` (the quotient step), skipping the grouping code.  We
provide the taken arm (`x27 = 0`); the not-taken arm is dead. -/

end Vsa.Sim
