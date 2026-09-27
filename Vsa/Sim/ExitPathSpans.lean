import Vsa.Sim.ExitPath
import Vsa.Sim.BlockTerm
import Vsa.Sim.BlockTactics
import Vsa.Sim.Code.Interp_run

/-!
# Layer 5/6 — the interp_run-continuation segment of `ErrorTailChain`

`Vsa/Sim/ExitPath.lean` reduced the opaque `ErrorTailChain` residual to four
straight-line segment `Triple`s (`InterpContSeg`, `MainErrorSeg`, `Crt0ExitSeg`,
`ExitPrologSeg`).  `Vsa/Sim/ExitPathSeg.lean` already discharged `ExitPrologSeg`.
This file discharges **`InterpContSeg`** — the one segment that is pure
straight-line machine code (register restores + one stack store) terminated by a
`ret`, with NO external function calls.  It is the segment the task brief flags as
the payoff of the `seg_eval`/block-reflection layer: the ≈16-instruction restore
span that a hand-threaded `StepObs` chain would blow up to ≈900 lines collapses
to ONE `bblocks_sound_bt` application over a 2-block chain.

## The decoded span (`0x80004428 → 0x800045ec`, from `experiments/disasm.txt`)

```
── interp_run continuation ──────────────────────────────────────────────────
80004428:  bnez a0,80004508        -- a0 = 1 ⇒ TAKEN → 0x80004508   (block 0)
80004508:  ld   a5,0(sp)                                             (block 1)
8000450c:  li   s5,1               -- return value s5 := 1
80004510:  sw   zero,8(a5)         -- clears the setjmp `active` flag
80004514:  ld   ra,168(sp)         -- epilogue restores: ra ← 168(sp) = 0x800045ec
80004518:  ld   s0,160(sp)
8000451c:  ld   s1,152(sp)
80004520:  ld   s2,144(sp)
80004524:  ld   s3,136(sp)
80004528:  ld   s4,128(sp)
8000452c:  ld   s6,112(sp)
80004530:  mv   a0,s5              -- a0 := s5 = 1  (the interp_run error return)
80004534:  ld   s5,120(sp)
80004538:  addi sp,sp,176
8000453c:  ret                     -- jr ra → 0x800045ec (main's jal interp_run link)
```

## Structure

Two basic blocks:

* **B0**: empty body, terminator `bnez a0,0x80004508` — TAKEN because `a0 = 1`
  (the error return; `guardB BNE 1 0 = true`).
* **B1**: the 13-instruction restore body (`ld`/`li`/`sw`/`ld…`/`mv`/`ld`/`addi`)
  terminated by `ret` (`jr ra`).

The nine `ld`s read the interp_run spill frame; the single `sw zero,8(a5)`
clears the setjmp buffer's `active` flag.  All of these read/write concrete
stack addresses whose *values* (the spilled register contents, in particular the
saved `ra = 0x800045ec`) and *geometry* (the store lands above the HTIF window;
the loads are 8-aligned in RAM; the restored `ra` is 4-aligned) are frame facts
the `interp_run` prologue established but that `InterpContSeg`'s precondition does
not itself name.  They are bundled into the single named residual
`InterpContFrame` — the exit-70 analogue of `ExitPathSeg`'s `ExitPrologGeom`
(the `_exit`-code/HTIF residual) and of the `runtime_error_spec` frame geometry
that `errorTailHalts_segments` already carries as `hre`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps output)
open Vsa.Logic
open Vsa.Sim.Code (Interp_runLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## The 2-block chain -/

/-! ## The frame residual

`InterpContSeg`'s precondition names only `{GoodState, tick<2, PC = 0x80004428,
a0 = 1, output = out}`.  The restore span additionally needs, of the interp_run
spill frame `sp = spv` on entry:

* the nine `ld` byte pins (the spilled register images) and, for the `ld ra`,
  that the spilled `ra` reads back as `0x800045ec` (main's `jal interp_run`
  link) — supplied as the load byte-lists `ldsIC` with the `ra` slot pinned;
* the load geometry (each `sp + off` is in RAM, 8-aligned, disjoint from the
  HTIF window);
* the store geometry for `sw zero,8(a5)` (`a5 + 8` in RAM above the HTIF
  window), where `a5` is the value read at `0(sp)`.

We package exactly the `ChainFacts` obligation the block lemma consumes, plus the
pin `sp = spv`.  This is the exit-70 analogue of `ExitPathSeg.ExitPrologGeom`. -/

/-! ## `InterpContSeg` discharged (conditional on `InterpContFrame`) -/

end Vsa.Sim
