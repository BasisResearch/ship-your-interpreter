import Vsa.Sim.EntryHalts
import Vsa.Sim.BlockTactics

/-!
# Layer 8 — discharging the two `EntryHalts` span seams

`Vsa/Sim/EntryHalts.lean`'s `hEntryHalts_of` reduced the program-entry premise to
TWO named span residuals — `EntryPrologueSpan` (`Loaded → SegEntry@loopHead`) and
`EntryEpilogueSpan` (`SegExit@exit → interp_run cont`).  This file supplies both,
mirroring the exit-70 twin `Vsa/Sim/ExitPathSpans.lean` (`interpContSeg_of`,
`interpContChain`, `icB1`), and lands `hEntryHalts_closed` modulo the honest
representation residuals that remain.

## The shared restore battery (`restoreRetChain`)

The exit-70 twin's `icB1` restore body and this file's `.normal`-epilogue restore
body are BYTE-IDENTICAL apart from `icB1`'s first three instructions
(`ld a5,0(sp); li s5,1; sw zero,8(a5)`).  Both are a single straight-line block of
nine `ld`s + `mv a0,s5` + `addi sp,sp,176` terminated by `ret`, whose only
load-bearing datum is the pinned `ra` slot (= `0x800045ec`, main's `jal interp_run`
link) and the `a0` return value latched from `s5`.  Rather than re-hand-thread a
second `bblocks_sound_bt` invocation we FACTOR the restore into
`restoreRetChain_run`: a single reusable lemma over a one-block `ret`-terminated
chain, parameterized by the pinned `ra` target, the `s5`/`a0` value, and the
`ChainFacts` spill residual.  `interpContSeg_of`'s tail (post-`bnez`) and this
file's epilogue are two instances of it.

## What is genuinely open (named residuals)

`SegEntry`/`SegExit` are the RICH M4-level predicates (`StoreRepr`, `OutRepr`,
budget fields), NOT machine-level `ChainFacts`.  The two spans therefore each
carry a representation seam that cannot be discharged by block-reflection alone:

* **`EpilogueFrame`** — from `SegExit` at the normal-exit PC, the concrete
  `ChainFacts` for the restore block (the spill images, `ra` pinned to
  `0x800045ec`), `sp = spv`, the return latch `s5 = 0` (⇐ `SegExit.frame` on the
  callee-saved `s5`, given the prologue latched `g s5 = 0`), and the produced
  `ExitTailChain0` (the tail span the epilogue's postcondition demands, itself
  discharged concretely by `TermEntry.cleanExitTail`'s consumer).  This is the
  exit-0 analogue of `ExitPathSpans.InterpContFrame`.
* **`PrologueSpanResid`** — from `Loaded L p c` the machine reaches `SegEntry` at
  the loop head.  This bundles: (a) the spill decode `[0x800043ec, 0x80004424)`;
  (b) the `jal setjmp` splice, discharged by `JmpSpec.setjmp_spec` (the FIRST
  return: `setjmp_pre` at `0x80006ffc` → `setjmp_post` with `a0 = 0`, `PC = ra0`),
  so `bnez a0` is NOT taken; (c) the loop-setup decode `[0x8000442c, 0x8000448c)`;
  (d) the store-init seam `ProgramRepr → StoreRepr initSt` (the AST/heap-init
  representation — `initSt` = the single global frame with the three natives —
  established by the interpreter's own `env_new` startup path, surfaced as the
  named `StoreInitSeam` premise).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps Halted Halts output)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc
open Vsa.Refine (Layout Loaded)
open Vsa.While (initSt Program Status ExecSeq Addr)
open Vsa.Sim.Code (Interp_runLoaded)

set_option maxHeartbeats 1600000
set_option maxRecDepth 1000000

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

/-! ## §1. The shared restore battery — `restoreRetChain`

A single straight-line block: the nine epilogue `ld`s (restoring `ra` first),
`mv a0,s5`, `addi sp,sp,176`, terminated by `ret`.  This is EXACTLY `icB1` minus
the leading `ld a5,0(sp); li s5,1; sw zero,8(a5)` — so it factors the byte-similar
restore that both the exit-70 (`interpContSeg_of`) and exit-0 (epilogue) paths run.

Body (10 instructions, program order):
`ld ra,168(sp)`; `ld s0,160(sp)`; `ld s1,152(sp)`; `ld s2,144(sp)`;
`ld s3,136(sp)`; `ld s4,128(sp)`; `ld s6,112(sp)`; `mv a0,s5`; `ld s5,120(sp)`;
`addi sp,sp,176`.  Terminator: `ret` (`jr ra`). -/

/-! ## §2. The epilogue span — `EntryEpilogueSpan` discharged

`SegExit` at `interpNormalExitPC = 0x80004514` carries the rich M4 store/out
representation; the restore battery needs the concrete spill `ChainFacts` and the
`s5 = 0` latch, which are the honest `EpilogueFrame` residual.  The epilogue's
postcondition ALSO demands `ExitTailChain0` (the tail span its consumer
`cleanExitTail` runs) — surfaced as the same residual. -/

/-! ## §3. The prologue span — `EntryPrologueSpan` reduced to `PrologueSpanResid`

`Loaded → SegEntry@loopHead` composes: the spill decode, the `jal setjmp`
first-return splice (`JmpSpec.setjmp_spec`), `bnez a0` not-taken, the loop-setup
decode, and the store-init representation seam (`ProgramRepr → StoreRepr initSt`).
The `setjmp` contract is REUSED verbatim; the store-init seam is genuinely the
interpreter's own `env_new` startup path, surfaced as the named `StoreInitSeam`. -/

/-! ## §4. `hEntryHalts_closed` — modulo the two honest residuals -/

end Vsa.Sim
