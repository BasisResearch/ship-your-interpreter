import Vsa.Sim.ExecWhile

/-!
# Layer 4 — M4 `whileStmt` recursive constructor: `whileLoop`

The three NON-recursive `whileStmt` constructors (`whileFalse`/`whileBreak`/
`whileRet`) are landed in `Vsa/Sim/ExecWhile.lean` via `execWhileExit`: each
EXITS the loop in one `ExecWhileStep` iteration.

`whileLoop` is the genuinely RECURSIVE constructor: the condition is truthy, the
body completes `.normal`/`.cont`, and the loop RE-ENTERS the head — the machine's
`bne a0,1` (body ≠ brk) then `beq a0,3` (body ≠ ret) both fall through to the loop
head `0x8000403c`. In the spec:

```
ExecS.whileLoop:  EvalE st … c st' v → v.truthy = true →
  ExecS st' … b st'' status → (status = .normal ∨ status = .cont) →
  ExecS st'' … (.whileStmt c b) st''' status'  ⇒  ExecS st … (.whileStmt c b) st''' status'
```

Like EVERY recursive case in this project (neg/binary/logical/block/seq all take
their sub-derivation's IH as a HYPOTHESIS, and the Layer-4 mutual recursor supplies
it), `whileLoop` is a CONDITIONAL lemma taking the recursive sub-`while` IH as a
hypothesis — NO self-recursion, NO `termination_by`. (`ExecS` is a mutual inductive
with the non-variable index `.whileStmt c b`, so `structural`/`sizeOf`/`measure`
termination all fail; the recursion is discharged by the mutual recursor at
assembly, exactly as for `hWhileIH` here.)

`execWhileLoopSim` = ONE iteration (`ExecWhileStep`, its loop-back branch) ≫ the
recursive IH on the strictly-smaller `while` derivation (`hWhileIH`), composing the
per-iteration φ-extensions (`PhiExtends.trans`) and re-basing the recursive exit's
memory frame back to the original `m0` via the step's memory-agreement clause
(`execExit_extend`). This is the `execSeqLoop` loop-back composition, but with the
recursion supplied as a hypothesis rather than by list induction.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
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

/-! ## `execExit_extend` — re-base an `ExecExit` to earlier φ-maps AND an earlier `m0`

`ExecExit`'s only φ-dependent fields are `store` and `retval` (existentials
`∃ φf'' φc'', PhiExtends φf' φf'' … ∧ …`); its only `m0`-dependent field is
`memFrame` (`∀ a, ¬stk → ¬arena → retslot-range ∨ c.σ.mem[a]? = m0[a]?`). Every
other field is independent of both. So an exit stated for extended maps
`φf'`/`φc'` and a later memory baseline `mNow` is also an exit for earlier maps
`φf`/`φc` and an earlier baseline `m0`, whenever:

* `φf'`/`φc'` extend `φf`/`φc` over the post-state's store sizes (compose the two
  `PhiExtends`), and
* `mNow` agrees with `m0` outside the stack window `[SL.lo, sp)` AND the arena
  `[A.lo, A.hi)` (the regions the loop's earlier iterations may have scribbled) —
  rebase the second `memFrame` disjunct through this agreement.

This is `execSeqExit_extend` extended with the memory rebase; it threads the
per-iteration φ-extensions AND the per-iteration store-growth memory drift through
`execWhileLoopSim`'s recursion. -/

/-! ## `execWhileLoopSim` — the recursive `whileStmt` constructor (`ExecS.whileLoop`)

The IH-taking loop-back lemma. From `ExecEntry` at `st` (the `while` arm head):

* `hstep` (one `ExecWhileStep` iteration) runs the cond eval (`v.truthy = true`)
  and the body (`.normal`/`.cont`), taking the LOOP-BACK branch: it re-enters the
  head at the intermediate spec state `stMid` with EXTENDED φ-maps `φf'`/`φc'`, its
  own memory baseline `c₁.σ.mem`, and a memory-agreement clause (`c₁.σ.mem` agrees
  with `m0` outside the stack window and the arena).
* `hWhileIH` (the recursive sub-`while` IH — the derivation on the strictly-smaller
  `whileLoop` premise `ExecS stMid … (.whileStmt c b) st''' status'`, supplied by
  the Layer-4 mutual recursor) then runs the REST of the loop from that re-entry to
  the final `ExecExit` at `st'''`/`status'`, against baseline `c₁.σ.mem`.

Composing: apply `hstep`, take the loop-back disjunct, feed the re-entry `ExecEntry`
to `hWhileIH`, then re-base its exit (extended maps `φf'`/`φc'`, baseline
`c₁.σ.mem`) back to the entry maps `φf`/`φc` and baseline `m0` via `execExit_extend`
— using the step's φ-extensions and its memory-agreement clause. Exactly the
`execSeqLoop` loop-back composition, with the recursion as a hypothesis.

The exit disjunct of `hstep` is impossible here: `whileLoop` fires precisely when
the body status is `.normal`/`.cont` (`hloop`), so `bodyStatus` = that status makes
the exit disjunct's `¬ (bodyStatus = .normal ∨ .cont)` contradictory. -/

/-! ## `execWhileSim` — all four `whileStmt` constructors, unified

Dispatches on the `ExecS` derivation of `.whileStmt c b`: the three non-recursive
constructors (`whileFalse`/`whileBreak`/`whileRet`) go to `execWhileExit`; the
recursive `whileLoop` goes to `execWhileLoopSim`. The per-iteration `ExecWhileStep`
(`hstep`) is supplied abstractly, parametric in the intermediate state / maps /
statuses / memory, so a single hypothesis covers the one iteration each constructor
needs; the recursive sub-`while` IH (`hWhileIH`) is the mutual-recursor IH the
`whileLoop` premise consumes.

Each constructor determines its own iteration witness locally (no caller-side
`bodyStatus` argument): the three non-recursive exits pass any exit-shaped body
status (`.brk`) to `execWhileExit` — `hstep` is parametric over the body status and
its EXIT disjunct delivers the loop-exit `ExecExit` regardless of which exit-shaped
status is chosen; `whileLoop` passes its body's `.normal`/`.cont` status
(loop-shaped) to `execWhileLoopSim`.

(The `cases hExec` binders are ONLY the non-index constructor arguments — the
indices `st`/`d`/`env`/`c`/`b`, the result state, and the result status are pinned
by the goal's `.whileStmt c b` index and so are not re-introduced: `whileFalse`
introduces 3, `whileBreak`/`whileRet` 5, `whileLoop` 9.)

This packages the entire `while` family as ONE `Triple (ExecEntry) (ExecExit)`,
ready to fill the `whileStmt` slot of the Layer-4 `motive_ExecS`. -/

end Vsa.Sim
