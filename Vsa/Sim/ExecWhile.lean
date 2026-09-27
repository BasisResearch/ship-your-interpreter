import Vsa.Sim.ExecBrkCont
import Vsa.Sim.ExecExprRet
import Vsa.Sim.ExecWhileSites
import Vsa.Sim.ExecDispatch
import Vsa.Sim.EvalRecCommon
import Vsa.Sim.ObsAvoid

/-!
# Layer 4 — M4 `whileStmt` cases: the loop with a re-evaluated condition

The `exec_stmt` `whileStmt` arm (kind 4, `0x8000403c`) is a genuine machine loop:

```
-- loop head 0x8000403c:
8000403c:  ld   a2,8(s0)       -- a2 := stmt->cond   (offset 8)
80004040:  mv   a3,s3          -- a3 := env
80004044:  addi a0,sp,80       -- cond eval sret buffer (sp'+80)
80004048:  mv   a1,s1          -- a1 := interp*
8000404c:  jal  eval_expr      -- link 0x80004050; the cond sub-derivation (EvalIH)
80004050:  ld   a3,80(sp)      -- reload the 24-byte cond result …
80004054:  ld   a4,88(sp)
80004058:  ld   a5,96(sp)
8000405c:  addi a0,sp,16       -- value_truthy arg buffer
80004060:  sd   a3,16(sp)      -- copy result into it
80004064:  sd   a4,24(sp)
80004068:  sd   a5,32(sp)
8000406c:  jal  value_truthy   -- link 0x80004070; a0 := (v.truthy ? 1 : 0)
80004070:  beqz a0,0x80004090  -- v.truthy == 0 (FALSY) → normal exit (whileFalse)
                               -- else (TRUTHY): run the body via a REAL jal exec_stmt
80004074:  ld   a1,16(s0)      -- a1 := stmt->body  (offset 16)
80004078:  mv   a3,s2          -- a3 := retslot
8000407c:  mv   a2,s3          -- a2 := env
80004080:  mv   a0,s1          -- a0 := interp*
80004084:  jal  exec_stmt      -- link 0x80004088; the body sub-derivation (ExecIH)
80004088:  li   a5,1
8000408c:  bne  a0,a5,0x80004034 -- body status ≠ 1 (≠ brk) → back-edge check 0x80004034
                               --   (else body status == 1 (brk) → fall through to normal exit)
-- normal exit:
80004090:  li   a0,0           -- x10 := 0 = StatusCode .normal
80004094:  j    0x8000409c     -- shared epilogue (execBlockD, status .normal)
-- back-edge check 0x80004034 (reached after body status ≠ brk):
80004034:  li   a5,3
80004038:  beq  a0,a5,0x80004150 -- body status == 3 (ret) → propagate (whileRet, 0x80004150 ret epilogue)
                               --   else (normal/cont) → fall through to loop head 0x8000403c (whileLoop)
```

So the whole thing is: eval cond; falsy → normal exit; truthy → run the body via
a genuine `jal exec_stmt` (the ordinary `ExecIH`, NOT re-dispatch); then dispatch
on the body's status — `.brk` → normal exit, `.ret v` → propagate (ret epilogue at
`0x80004150`), `.normal`/`.cont` → loop back to the cond head.

## `whileFalse` (this file)

`whileFalse` is the bounded first case: the condition evaluates falsy and NO body
runs, completing `.normal` with the condition's output store `st'`. It is
STRUCTURALLY IDENTICAL to `execIfNoneSim` — cond eval + `value_truthy` (falsy) +
`beqz a0` taken to `0x80004090` + `li a0,0` + `j 0x8000409c` + `execBlockD .normal`
— only the arm PC (`0x8000403c` kind 4) and the sret-buffer offset (`sp'+80` vs
`sp'+56`) differ. The cond-eval + `value_truthy` + falsy branch (`0x8000403c →
0x80004090`, landing in a `SubExecReturn` state) is delivered as the named glue
residual `hGlue`, exactly as in `execIfNoneSim`.

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

/-! ## `ExecWhileFalseSimGoal` — the `ExecS.whileFalse` simulation Triple (packaged) -/

/-! ## `execWhileFalseSim` — `ExecS.whileFalse`: `execBlockA ≫ hGlue ≫ (li a0,0 ; j ; execBlockD)`

The head (`execBlockA`, prologue+dispatch to the `whileStmt` arm `0x8000403c`) and
the tail (`li a0,0` at `0x80004090`, `j 0x8000409c`, then `execBlockD` with status
`.normal`) are threaded UNCONDITIONALLY around the arm-body glue `hGlue`, which
consumes the `EvalIH` for the condition, evaluates `value_truthy` (result `0`,
since `v.truthy = false`), takes the falsy branch (`beqz a0` → `0x80004090`), and
lands at `0x80004090` in a `SubExecReturn` state. Identical skeleton to
`execIfNoneSim`, for the `while`-with-falsy-cond arm. -/

/-! ## `ExecWhileStep` — one machine loop iteration (the per-iteration hypothesis)

From `ExecEntry` at the loop head (the `whileStmt` arm entry `0x8000403c`, reached
per-iteration with a fresh cond eval), one iteration runs the cond eval (`EvalIH`),
`value_truthy`, and — on the truthy path — the body via a genuine `jal exec_stmt`
(`ExecIH`), then dispatches on the body's status (mirroring the machine branches
`beqz a0` at the cond, `bne a0,1` after the body, and `beq a0,3` at `0x80004034`):

* **loop-back** (body `.normal`/`.cont`, `whileLoop`) → re-enter the head at `stMid`
  with EXTENDED φ-maps; the post carries the next-iteration `ExecEntry` (its own
  baseline `cfg.σ.mem`) PLUS a memory-agreement clause: `cfg.σ.mem` agrees with the
  original `m0` outside the stack window `[SL.lo, sp)` and the arena `[A.lo, A.hi)`
  (arena = where the store-growth writes land) — this re-bases the recursive exit's
  `memFrame` back to `m0`.
* **exit** (cond falsy `whileFalse`, body `.brk` `whileBreak`, body `.ret v`
  `whileRet`) → the loop is done; land the `ExecExit` for `stMid`/`loopStatus`
  against the original `m0` directly.

`stFin` is the loop's final post-state; the loop-back φ-extension is stated over
`stFin`'s store sizes so the loop rule composes the per-iteration extensions to the
final exit (like `ExecSeqStep`). -/

/-! ## `execWhileExit` — the three non-recursive `whileStmt` constructors

`whileFalse` (cond falsy → `.normal`), `whileBreak` (truthy, body `.brk` → `.normal`
with the body's output store `st'`), and `whileRet` (truthy, body `.ret v` →
propagate `.ret v`) all EXIT the loop in one iteration — they do not recurse. Each
is discharged directly by the `ExecWhileStep` iteration's EXIT branch (the machine's
`beqz a0` cond-falsy exit, the `bne a0,1` NOT-taken brk-fall-through, and the
`0x80004034 beq a0,3` ret-propagation). The `.brk`/`.ret v` body statuses are
`≠ .normal, .cont`, so the exit disjunct fires; the loop-back disjunct is
contradictory (impossible for these statuses). -/

end Vsa.Sim
