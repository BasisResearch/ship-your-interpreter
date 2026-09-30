import Vsa.Sim.MemcpySpec2
import Vsa.Sim.MemcpySites3
import Vsa.Sim.DivSpec
import Vsa.Triple
import Vsa.Sim.ObsAvoid

/-!
# Layer 3 — `memcpy` small-word-loop rule, epilogue, dispatch, and unified spec

Builds on `Vsa/Sim/MemcpySpec2.lean` (the word-loop body `iterW`, `StW`/`StW18`,
`meminv_store8`, the pointer identities) and `Vsa/Sim/MemcpySites2.lean` (the
per-site steps for the small word loop `[0x80006bfc, 0x80006c38]`).

## Task 1: the word-loop rule

The small word loop copies `p` full words (`8p ≤ n`, `p > 0` and small enough to
avoid the unrolled ×8 path).  Control flow:

* `c04 : bgeu a4,a2` — entry guard.  `a4 = dst`, `a2 = dst + 8p`.  Not-taken
  (`dst <u dst+8p`, i.e. `p > 0`) falls to the loop head `c08`; taken skips the
  loop entirely (`p = 0`).
* `c08 … c14` — one iteration (`iterW`, `c08 → c18`).
* `c18 : bltu a5,a2` — back-edge.  `a5 = dst + 8(j+1)`, `a2 = dst + 8p`.  Taken
  (`8(j+1) < 8p`, i.e. `j+1 < p`) loops back to `c08`; not-taken (`j+1 = p`)
  falls through to the epilogue at `c1c` with `MemInv … (8p)`.

Encoded for `Triple.loop` (DivLoops bottom-tested pattern): a PC-guarded measure
`LoopMuW = a2.toNat - a5.toNat` (= `8(p-j)` at the head, `0` elsewhere), invariant
`LoopIW = AtHeadW ∨ AtDoneW`, guard `LoopBW = AtHeadW`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (MemcpyLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Word-path branch frame helpers (over `NotWrittenW`) -/

/-! ## Word-loop epilogue-entry state (`StWDone`, at `0x80006c1c`)

When the word loop exits (`c18` not-taken, `j+1 = p`), the machine is at `c1c`
with all `p` words copied (`MemInv … (8p)`) and the pointers at their loop-final
values: `a2 = dst + 8p`, `a4 = dst`, `a5 = dst + 8p`, `a3 = src + 8p`.  The `a1`
still holds `src` (the small word loop never touches `a1`). -/

/-! ## The `bltu a5,a2` back-edge (`0x80006c18`)

`a5 = dst + 8(j+1)`, `a2 = dst + 8p`.  Taken iff `dst+8(j+1) <u dst+8p` iff
`j+1 < p` (no wrap); loops back to `c08` iteration `j+1`.  Not-taken iff
`j+1 = p`; falls through to `c1c` with `MemInv … (8p)`. -/

/-! ## Loop invariant, guard, measure (`Triple.loop`, DivLoops PC-guarded pattern) -/

/-! ## The `c04` bgeu entry into the word loop

`bgeu a4,a2` at `c04` with `a4 = dst`, `a2 = dst + 8p`, `a3 = src`, `a5 = dst`.
For `p > 0` the branch is not-taken (`dst <u dst+8p`), falling to the loop head
`c08` at iteration `0` (`AtHeadW`).  `MemInv … 0` (nothing copied yet). -/

/-! ## Task 2: the word-loop epilogue (`0x80006c1c … 0x80006c38`)

Straight-line pointer recomputation, then `bltu a4,a7` at `c38`.  From `StWDone`
(`a2 = dst+8p`, `a4 = dst`, `a1 = src`), the seven ALU steps compute (using
`dst%8 = 0`, `p ≥ 1`):

* `a2 := (((dst+8p) - 1) - dst) & ~7 = 8(p-1)`  (`epilogue_a2`, `mask_low3`);
* `a1 := (src + 8) + 8(p-1) = src + 8p`;
* `a4 := (dst + 8) + 8(p-1) = dst + 8p`.

`c38 : bltu a4,a7` then tests `dst+8p <u dst+n`: taken (`8p < n`, tail bytes remain)
enters the byte loop at `c48` with the byte-loop head state `StB` at iteration
`8p`; not-taken (`8p = n`, whole copy word-aligned) rets at `c3c` (the ret site
there is a documented follow-up — see the return note).

The byte loop uses the `NotWrittenB` frame predicate, disjoint from the word
loop's `NotWrittenW` (the epilogue writes `x11, x12, x14`, and `x12 ∉ NotWrittenB`).
So the epilogue instantiates a **fresh** byte-loop ghost `g' := c'.σ.regs.get?`
(making the byte-loop `hframe` trivially `rfl` at entry) — the DivLoops
callee-ghost-at-call-site pattern.  The original `g` connection is not needed
inside the byte path (whose own post re-exposes every untouched register). -/

end Vsa.Sim
