import Vsa.Sim.ExecBrkCont
import Vsa.Sim.ExecExprRet
import Vsa.Sim.ExecIfSites
import Vsa.Sim.EvalRecCommon
import Vsa.Sim.ObsAvoid

/-!
# Layer 4 — M4 `ifStmt` bounded case: `ExecS.ifNone`

The `ExecS.ifNone` constructor: the condition evaluates FALSY and there is NO
`else` branch, so the `if` statement runs no sub-statement and completes
`.normal` with the condition's output store `st'`. This is the tractable `if`
sub-case — it sidesteps the re-dispatch problem entirely (ifTrue/ifFalse re-enter
the dispatch at `0x80004014` with `s0 := then/else`; ifNone never re-dispatches).
It is a clean bounded case exactly like `ExecS.expr` (`ExecExprRet.lean`): the
condition eval discards its value like `expr`, but here we additionally observe
its truthiness is falsy and there is no `else` node.

## The `ifStmt` arm (kind 3, `0x800041e8`) — the `ifNone` falsy path

```
800041e8:  ld   a2,8(s0)       -- a2 := stmt->cond   (offset 8, the condition node)
800041ec:  mv   a3,s3          -- a3 := env
800041f0:  mv   a1,s1          -- a1 := interp*
800041f4:  addi a0,sp,56       -- a0 := sp'+56 (cond eval sret buffer)
800041f8:  jal  eval_expr      -- link 0x800041fc; the cond sub-derivation (EvalIH)
800041fc:  ld   a2,56(sp)      -- reload the 24-byte cond result …
80004200:  ld   a3,64(sp)
80004204:  ld   a5,72(sp)
80004208:  addi a0,sp,16       -- a0 := sp'+16 (value_truthy arg buffer)
8000420c:  sd   a2,16(sp)      -- copy the result into the value_truthy arg buffer
80004210:  sd   a3,24(sp)
80004214:  sd   a5,32(sp)
80004218:  jal  value_truthy   -- link 0x8000421c; a0 := (v.truthy ? 1 : 0)
8000421c:  li   a6,8           -- (dispatch-bound reload; noise on this path)
80004220:  auipc a4,0x16       -- a4 := table base …
80004224:  addi a4,a4,-616     -- a4 := 0x80019fb8
80004228:  beqz a0,0x800042cc  -- v.truthy == 0 (FALSY) → 0x800042cc (else-check)
                               --   (the truthy path `s0:=then; j 0x80004014` is the re-dispatch)
800042cc:  ld   s0,24(s0)      -- s0 := stmt->else  (offset 24; = 0 here, no else)
800042d0:  bnez s0,0x80004014  -- else present → re-dispatch; NOT taken (else absent)
800042d4:  li   a0,0           -- x10 := 0 = StatusCode .normal
800042d8:  j    0x8000409c     -- into the shared epilogue (execBlockD, status .normal)
```

## Structure of `execIfNoneSim`

`execIfNoneSim = execBlockA (kind 3, arm 0x800041e8) ≫ hGlue ≫ (li a0,0 ; j ; execBlockD)`.

Exactly like `execExprSim`, the head (`execBlockA`) and the tail (`li a0,0` at
`0x800042d4`, `j 0x8000409c`, then `execBlockD` with status `.normal`) are
threaded UNCONDITIONALLY around the arm-body glue `hGlue`, which reaches
`0x800042d4` in a `SubExecReturn` state (the same post-recursive-call state the
`expr` arm holds at `0x80004184`, only at a different link PC). `hGlue` bundles:

* the cond eval (`armTail_rec_es`, `EvalIH` for the condition `c`);
* the reload/copy of the 24-byte cond result into the `value_truthy` arg buffer;
* `value_truthy` (`value_truthy_spec`), yielding `a0 = 0` since `v.truthy = false`;
* the falsy branch `beqz a0` TAKEN (`0x800042cc`) and the no-else branch `bnez s0`
  NOT-taken (`stmt->else = 0`), reading the `else`-absence from the `Stmt` node.

The falsy hypothesis `v.truthy = false` and the else-absence are the genuine
`ifNone`-spec / AST-transport premises; here they are named residuals inside
`hGlue`, exactly as `execExprSim` carries its recursion glue as `hGlue`.

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

/-! ## `ExecIfNoneSimGoal` — the `ExecS.ifNone` simulation Triple (packaged) -/

/-! ## `execIfNoneSim` — `ExecS.ifNone`: `execBlockA ≫ (arm body ≫ IH ≫ value_truthy) ≫ tail`

The head (`execBlockA`, prologue+dispatch to `0x800041e8`) and the tail (`li a0,0`
at `0x800042d4`, `j 0x8000409c`, then `execBlockD` with status `.normal`) are
threaded UNCONDITIONALLY around the arm-body glue `hGlue`, which consumes the
`EvalIH` for the condition and lands at `0x800042d4` in a `SubExecReturn` state.
This validates the same `execBlockA ≫ … ≫ execBlockD` skeleton as `execExprSim`,
for the `if`-with-falsy-cond-no-else arm. -/

end Vsa.Sim
