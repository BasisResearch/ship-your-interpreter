import Vsa.Sim.ExecBrkCont
import Vsa.Sim.Exec_stmtSites2
import Vsa.Sim.EvalRecCommon
import Vsa.Sim.ReprCopy
import Vsa.Sim.ObsAvoid

/-!
# Layer 4 — M4 first RECURSIVE statement cases: `ExecS.expr` (+ scaffolding for `ExecS.ret`)

The first statement cases that recurse into `eval_expr`. They validate the
recursive-statement pattern

    execBlockA  ≫  (arm sets up + jal eval_expr, consuming an EvalIH)  ≫  execBlockD

for the `exec_stmt` frame (176-byte, five callee-saved spills), the statement-side
analog of the expression-side recursive cases (`EvalNegSim`/`EvalBinSim`, which
use `armTail_rec` for the eval_expr frame).

## `ExecS.expr` — the `expr` arm (kind 0, `0x80004170`)

```
80004170:  ld   a2,8(s0)      -- a2 := stmt->expr  (the operand node, ExprRepr of e)
80004174:  addi a0,sp,16      -- a0 := sp' + 16    (the sub-call sret buffer, in-frame)
80004178:  mv   a3,s3         -- a3 := env         (unused by eval_expr's ABI; noise)
8000417c:  mv   a1,s1         -- a1 := interp*     (eval_expr ABI arg 1)
80004180:  jal  eval_expr     -- link 0x80004184; the recursive sub-derivation (EvalIH)
80004184:  li   a0,0          -- x10 := 0 = StatusCode .normal  (value discarded)
80004188:  j    0x8000409c    -- into the shared epilogue  (execBlockD, status .normal)
```

`ExecS.expr` evaluates `e` (store may change to `st'`), discards the value, and
completes `.normal`. So the machine sub-call is a full `eval_expr` on the operand
node; its returned value is thrown away (`li a0,0` clobbers the sret pointer in
`a0`), and only the store/output changes survive to the exit.

## `ExecS.ret` — the `ret` arm (kind 6, `0x80004120`, value-present path)

```
80004120:  ld   a2,8(s0)      -- a2 := stmt->expr
80004124:  beqz a2,…          -- (not taken: value present)
80004128:  mv   a3,s3         -- a3 := env
8000412c:  mv   a1,s1         -- a1 := interp*
80004130:  addi a0,sp,16      -- a0 := sp'+16 (local sret buffer)
80004134:  jal  eval_expr     -- the sub-derivation (EvalIH)
80004138:  ld   a3,16(sp) ; ld a4,24(sp) ; ld a5,32(sp)   -- reload the 24-byte result
80004144:  sd   a3,0(s2) ; sd a4,8(s2) ; sd a5,16(s2)     -- *retslot := v  (s2 = aRet)
80004150:  ld   ra,168(sp) … ld s3,136(sp) ; li a0,3 ; addi sp,176 ; ret
```

`ExecS.ret` evaluates `e` to `v`, copies `v` into the caller `retslot`, and
completes `.ret v` (exercising `ExecExit.retval`, the `retslot` disjunct).

## Status of this file

The straight-line arm SETUP + the epilogue TAIL are threaded here around the
recursion; the `jal eval_expr ≫ IH` glue is packaged as `SubExecReturn` (the
statement-frame analog of `SubEvalReturn`) — a NAMED RESIDUAL delivered as a
premise, exactly as `execBrkSim`/`blockB_unary` land conditional on their
`*Extras`/geometry residuals. `execExprSim` proves the full
`Triple (ExecEntry (.expr e)…) (ExecExit … st' .normal …)` conditional on:

* `hslot`/`htableStk` — the jump-table slot pin + stack-disjointness (`execBlockA`);
* `hGlue` — the recursion-glue residual: from the arm-entry state at `0x80004170`
  the setup + `jal eval_expr` + the sub-call (the `EvalIH`) reaches `0x80004184`
  in a `SubExecReturn` state (store `st'` re-represented, spills intact, output
  `st'.out`, callee-saved restored, memory framed).

`execExprSim`'s own contribution — the `execBlockA` head and the `li a0,0`/`j`/
`execBlockD` tail wrapped UNCONDITIONALLY around `hGlue` — is what validates the
`execBlockA ≫ … ≫ execBlockD` recursive-statement skeleton.

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

/-! ## `SubExecReturn` — the post-sub-call machine state (exec_stmt frame)

The statement-frame analog of `SubEvalReturn` (`EvalRecCommon.lean`). What the
`expr`/`ret` arm knows after its `jal eval_expr` returns (link PC `retPC`), for a
sub-derivation with post spec state `st'` and returned value `vsub` in the buffer
`subsret`:

* control back at `retPC`, `sp` still lowered (`sp - 176`), `s2 = aRet` (retslot),
  the four exec_stmt spill slots (`sp-{8,16,24,32,40}`) intact for the epilogue;
* callee-saved registers restored to the arm-frame ghost `garm`;
* the sub-result `ValueRepr` at `subsret` (extended `φc'`) — used by `ret` for the
  24-byte copy (`expr` discards it);
* `st'.store` re-represented at ONE coherent extended pair, WITH the stack-region
  survival clause;
* console output `= st'.out`; `exec_stmt`'s code still loaded;
* memory framed to the pre-call memory `mcall` outside
  (stack-window ∪ arena ∪ subsret-window), presence-extended.

`garm` is the arm-entry register frame (post-`execBlockA`): `x8 = aStmt`,
`x9 = aInterp`, `x18 = aRet`, `x19 = aEnv`, `x2 = sp`. -/

/-! ## `ExecExprSimGoal` — the `ExecS.expr` simulation Triple (packaged) -/

/-! ## `execExprSim` — `ExecS.expr`: `execBlockA ≫ (jal eval_expr ≫ IH) ≫ execBlockD`

The head (`execBlockA`, prologue+dispatch to `0x80004170`) and the tail
(`li a0,0` at `0x80004184`, `j 0x8000409c`, then `execBlockD` with status
`.normal`) are threaded UNCONDITIONALLY around the recursion glue `hGlue` (which
consumes the `EvalIH` for the sub-expression). This validates the
`execBlockA ≫ EvalIH ≫ execBlockD` skeleton for every recursive statement case. -/

end Vsa.Sim
