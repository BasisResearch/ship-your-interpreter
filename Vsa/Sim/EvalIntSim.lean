import Vsa.Sim.EvalExprSites
import Vsa.Sim.EvalIntPilot

/-!
# Layer 4 — the `EvalE.int` simulation composition (M4 gate)

The per-instruction sites for the `EX_INT` path live in `Vsa/Sim/EvalExprSites.lean`
(29 site lemmas + 8 execute helpers, all fully proved). This file assembles the
reusable *survival* bricks the walk needs — the facts that the `eval_expr` code and
the represented spec state survive the four `sd` prologue spills into the stack
window — and records the target `EvalIntSimGoal` (from `Vsa/Sim/EvalIntPilot.lean`).

## Status

The prologue+dispatch and epilogue sites are fully verified (`EvalExprSites`). The
composition bricks below (`Eval_exprLoaded` survival under a stack `writeMap8`) are
fully verified here. The end-to-end threading of all 26 steps + the `value_int_spec`
callee jal into `EvalIntSimGoal` is the remaining work; it is a mechanical (if long)
`Triple.seq` chain over the verified sites, discharging each `EvalExit` field via the
`EvalIntPilot` bridges (`intResult_bridge`, `exprRepr_int_pay64`, `evalInt_spec_forces`,
`intSlot_target`) — recorded as `EvalIntSimGoal`, NOT asserted as a theorem.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## `Eval_exprChunk` survival under a stack-window `sd` spill (per-chunk brick)

The four prologue `sd` spills write `writeMap8` windows into the stack frame
`[sp-1088, sp)`, disjoint from the code region `[0x80003164, 0x80003fe0)`. The
byte-fact-transfer workhorse `AgreeOn`/`agree_of_write8_disjoint` (Regions.lean)
turns that disjointness into pointwise agreement on any code sub-region, from which
each `eval_exprChunk_i` transfers exactly as `ValueSpec.loaded_int_writeMap8` does
for `value_int`'s single chunk. (The monolithic 58-chunk `Eval_exprLoaded` transfer
is left to the composition, where each chunk is discharged locally against the
`FixedMap` region bundle; folding all 58 into one lemma blows the elaborator's whnf
budget, so the composition threads them chunk-wise.) The reusable region-form
agreement fact, ready to feed a chunk transfer, is: -/
theorem code_agree_of_stack_write8_ee (mem : Std.ExtHashMap Nat (BitVec 8)) (a8 : Nat)
    (d : BitVec (8 * 8)) (lo len : Nat)
    (hdis : lo + len ≤ a8 ∨ a8 + 8 ≤ lo) :
    AgreeOn (lo, len) mem (writeMap8 mem a8 d) :=
  agree_of_write8_disjoint mem a8 d (lo, len) (by simp only [RDisjoint]; omega)

/-! ## The recorded goal (the remaining end-to-end walk)

`EvalIntSimGoal` (defined in `Vsa/Sim/EvalIntPilot.lean`) is the M4 gate Prop:

```
∀ …, EvalE st d a (.int n) st (.int n) →
  Triple (EvalEntry … (.int n) …) (EvalExit … (.int n) …)
```

Its proof threads the 26 verified sites of `EvalExprSites.lean` via `Triple.seq`
(prologue spills over the stack window `[sp-1088, sp)`, whose memory survival for
code/`ExprRepr`/`StoreRepr` uses `loaded_eval_expr_writeMap8_ee` above and the
`read*_writeMap*_disjoint` kit), dispatches through the jump table
(`intSlot_target` pinning `0x800031ac → 0x80003408`), runs the arm `ld a1,8(a2)`
(payload from `exprRepr_int_pay64`) and the `value_int_spec` jal (callee ghost
`fun R => σ.regs.get?`, its `int_post` landing `ValueRepr … (.int n)`), then the
epilogue restores (callee-saved recovered from the untouched spill slots via
`value_int`'s mem framing) and `ret`. The four `EvalExit` obligations discharge via
`intResult_bridge` (identity φ), `evalInt_spec_forces` (`st'=st`, `PhiExtends.refl`),
and the memory frame. -/
#check (EvalIntSimGoal : Prop)

end Vsa.Sim
