import Vsa.Sim.EvalGtBlocks
import Vsa.Sim.EvalGtBlk1Pilot
import Vsa.Sim.EvalBinSim4
import Vsa.Sim.BlockTerm
import Vsa.Sim.BlockTactics
import Vsa.Sim.BlockTactics2
import Vsa.Sim.InterpEntry

/-!
# `EvalGtChain` — chain `evalGtBlk1` + `evalGtBlk2` across two terminators

Re-lands `evalGtChain_run`: EvalGtRow's opening 16-instruction run
`0x8000351c … (bltu@0x3534 not-taken) … (jr@0x3558) → 0x80003628`.

## Why two `bblock_sound_bt`s, not one `bblocks_sound_bt`

A single multi-block `bblocks_sound_bt` phrases block 2's terminator obligations
over `runGM evalGtBlk2 (runGM evalGtBlk1 …) …` — a **nested** 14-instruction
symbolic reduction.  `decide`/`rfl` on that overruns the whnf recursion budget
(and cranking `maxRecDepth` only trades the confusing "free variables" error for a
native stack overflow — the reduction is genuinely too deep).

The compounding fix: apply `bblock_sound_bt` **once per block**, threading block 1's
clean register outputs (`x14 = 12`, `x15 = 11`, `x2 = v2`) into block 2's pin list.
Every guard / jr-target / address reduction is then only 6–8 instructions deep and
completes at the DEFAULT recursion depth — no ceiling needed.

* `gtChainB1` = `evalGtBlk1` (lw/li/lw/addiw/lw/ld) + `bltu a4,a5` NOT taken
  (`x14 = 12`, `x15 = 22 - 11 = 11`, `12 <u 11` false → fall to 0x3538).
* `gtChainB2` = `evalGtBlk2` (slli/srli/auipc/addi/add/lw/ld/add) + `jr a5`
  (slot @0x80019fb0 = `sext[a4 96 fe ff]` + `0x80019f84`; `x15` = 0x80003628).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.  NO `maxRecDepth` override.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)

namespace Vsa.Sim

/-! ## The branch ladder `0x80003628 → 0x8000364c` (kind-dispatch, first two blocks)

`evalGtChain_run` lands at the shared comparison arm `0x80003628` with the right
operand's kind in `x10 = 2` (int) and the op token in `x12 = 22` (.gt).  The kind
ladder then routes int-vs-int through a taken `bnez` and a not-taken `beq`:

* **LB1** `addi x15,x10,-3` (`x15 = 2 - 3 = -1`), `bnez x15 → 0x3638` TAKEN.
* **LB2** `addiw x15,x12,-20` (`x15 = 22 - 20 = 2`), `li x14,3`, `auipc/addi x13`
  (dead), `beq x15,x14 → 0x3648+…` NOT taken (`2 ≠ 3`), fall to `0x364c`.

Same compounding discipline: one `bblock_sound_bt` per block, guards discharged by
peeling the 1-4-instr wrapper to the clean form then `decide`. -/

/-! ## The store block `0x8000364c → 0x8000367c` (LB3: CSWTCH slot compute + dead
loads + two scratch stores + `bne` NOT-taken).

`evalGtLadderAB` lands at `0x364c` with `x15 = 2` (the reloaded kind).  LB3 is the
second jump-table dispatch computing the CSWTCH.25 slot pointer, three dead loads,
and two scratch stores to `sp-848`/`sp-832`, then `bne x16,x11` NOT taken (2≠2 false).

Split into LB3a (pure ALU, computes `x15 = 0x80019ff0`, `x14 = 0x80019fe0`;
fall-through) and LB3b (three `ld`, `li`, two `sd`, `bne`).  The first `ld` reads the
block-computed slot `0x80019ff0`, which is LB3b's INPUT `x15` (input-relative =
shallow).  The memory outcome is exposed existentially as a `writeMap8²` image, so
the assembler bridges downstream (disjoint) loads with `getElem_writeMap8_disjoint`. -/

/-! ## LB4 `0x8000367c → 0x80003698` (`evalGtBlkLdSt` body + `bne x10,x16` NOT taken).

Reuses the already-green `evalGtBlkLdSt` straight-line body (three `ld` @ v2+0x90/
0x98/0xa0, three `sd` @ v2+0xf0/0xf8/0x100) as one `bblock_sound_bt` with a `bne`
terminator (`x10 = x16 = 2` → false, fall to 0x3698).  Load pins are supplied over
`σ.mem` (the assembler bridges them past LB3's stores with disjointness); the three
scratch stores overwrite, so the memory outcome is a `writeMap8³` image. -/

/-! ## LB5 + LB6 `0x80003698 → 0x80003ae4` (comparison tail + `beq` ladder).

The memory is fixed from here (no stores), so these are pure ALU/branch blocks.

* **LB5** = `evalGtBlkCmp` body (`slt/slt/subw/li`; `x11 = cmpScalar Wl Wr`,
  `x15 = 21`) + `beq x12,x15` NOT taken (22≠21) → 0x36ac.
* **LB6** = `li x15,22` + `beq x12,x15` TAKEN (22=22) → 0x80003ae4.

`x11 = cmpScalar Wl Wr` (the signed comparison scalar) and `x9 = sret` survive the
`beq` ladder into the `sgtz` fixup. -/

/-! ## LB7 `0x80003ae4 → 0x80003aec` (`sgtz`/`mv` — the `gt` fixup + arg setup).

The last straight-line block before the `jal value_bool` seam (the `jal` is NOT a
block terminator — only `jr` is — so the seam is hand-threaded by the assembler).

* `sgtz x11,x11` (`slt x11,x0,x11`) → `x11 = zext(bool(0 < cmp))` (the `gt` fixup).
* `mv x10,x9` (`addi x10,x9,0`) → `x10 = sret` (the `value_bool` self-pointer arg). -/

end Vsa.Sim
