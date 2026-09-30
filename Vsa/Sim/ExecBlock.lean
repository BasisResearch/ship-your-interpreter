import Vsa.Sim.ExecRecCommon
import Vsa.Sim.ExecSeqLoop
import Vsa.Sim.ExecBlockSites

/-!
# Layer 4 — M4 statement family: the `block` case (`ExecS.block`)

This module opens the `ExecS.block` statement case. Its centrepiece — and the
priority deliverable — is **`armExec_rec`**, the statement-recursion multiplier:
the `jal exec_stmt` recursion glue at the block do-while's recursive call
(`0x800041c4`). Where `armTail_rec_es` (`ExecRecCommon.lean`) threads a
`jal eval_expr` ⋈ an *expression* IH into a `SubExecReturn`, `armExec_rec`
threads a `jal exec_stmt` ⋈ a *statement* IH (`ExecIH`, one `exec_stmt` run)
into a `SubStmtReturn` — the state the block loop body holds right after the
recursive `exec_stmt` returns (at the link PC `0x800041c8`), from which it runs
the `bnez a0` status check.

`armExec_rec` is reused by every recursive *statement* case whose body
re-enters `exec_stmt` (block-loop, and — later — if/while/for bodies), exactly
as `armTail_rec_es` is the reusable `jal eval_expr` multiplier for the recursive
*expression*-in-statement cases.

## The recursive call site (block do-while, `0x800041c4`)

At `0x800041c4` the block loop has already staged the recursive call's ABI args
(`a0 = interp*`, `a1 = stmts[i]`, `a2 = innerEnv`, `a3 = retslot`, `sp` lowered
by 176, `i` spilled at `sp+8`), and executes `jal exec_stmt` (link
`0x800041c8`). The callee is `exec_stmt` itself (entry `0x80003fe0`), so this is
a genuine recursion; the induction hypothesis it consumes is an `ExecIH` (one
sub-`exec_stmt` run producing an `ExecExitD`). Its result is a `Status` in `a0`
and — on the `ret` sub-status — a write of the returned `Value` into the sub-retslot.

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

/-! ## `ExecExitD` — the presence/survival-widened `exec_stmt` exit

`ExecExit` strengthened with the two clauses every recursive CALLER needs from
its sub-`exec_stmt`:
1. presence monotonicity (`MemExtends m0 mem`) — the post-call reloads of the
   spill slots and the (possibly written) retslot need presence;
2. an exit-side `StoreRepr` survival clause: the re-represented `st'.store` (at
   ONE coherent extended map pair) tolerates arbitrary further memory changes
   inside the stack region `[SL.lo, SL.hi)` — where the caller's remaining loop
   writes land. Instantiating `m' := c.σ.mem` recovers the plain exit
   `StoreRepr`.

This is the statement-frame analog of `EvalExitD` (`EvalRecCommon.lean`); it is
the shape the real `ExecS` recursor motive must produce. -/

/-! ## `ExecIH` — the recursive statement-case motive shape

The induction hypothesis a recursive `ExecS` case receives for a
sub-derivation `ExecS st d env s st' status`: the ∀-closed simulation Triple at
the widened exit. This is `InductionScaffold.motive_ExecS` with `ExecExit`
upgraded to `ExecExitD` (RESIDUAL: re-land the leaf/base statement minor
premises at `ExecExitD`). -/

/-! ## `SubStmtReturn` — the post-`jal exec_stmt` machine state

What the block loop body knows at the instruction after its recursive
`jal exec_stmt` (link PC `retPC = 0x800041c8`), for a sub-derivation with post
spec state `st'` and produced abrupt-completion `status`:

* control back at `retPC`, `a0 = StatusCode status` (the `bnez a0` reads this),
  `sp` still lowered (`sp - 176`), the four `s0/s1/s2/s3` slots + ra slot
  (`sp-{8,16,24,32,40}`) intact for the loop control and the epilogue;
* the outer callee-saved regs (`s0..s3`, `sp`) restored to the arm frame `garm`
  (`x8 = aStmt` the block node, `x9 = aInterp`, `x18 = aRet` the outer retslot,
  `x19 = aEnv` the inner scope), so the loop can reload `stmts`, `count`, etc.;
* `st'.store` re-represented at ONE coherent extended pair;
* console output `= st'.out`; `exec_stmt`'s code still loaded;
* memory framed to the pre-call memory `mcall` outside
  (stack-window ∪ arena ∪ sub-retslot-window), presence-extended;
* on the `ret v` sub-status, the sub-retslot buffer `[aRetSub, aRetSub+24)`
  holds `ValueRepr v` — the honest fact the enclosing statement (`ret`/return
  propagation) later consumes; other statuses leave it unconstrained.

`garm` is the arm-entry register frame (post-`execBlockA`): `x8 = aStmt`,
`x9 = aInterp`, `x18 = aRet`, `x19 = aEnv`, `x2 = sp`. -/

/-! ## `armExec_rec` — `jal exec_stmt` ≫ `ExecIH` ⇒ `SubStmtReturn`

The statement-recursion multiplier. From the machine state at the recursive
`jal exec_stmt` PC (`callPC`), with the sub-call's ABI arguments staged
(`a0 = aInterp`, `a1 = aStmtSub` the current `stmts[i]`, `a2 = aEnvSub` the inner
scope, `a3 = aRetSub` the retslot forwarded, `sp` lowered by 176), one `jal`
step lands at `exec_stmt`'s entry with link `retPC = callPC + 4`; the sub-call's
`ExecEntry` is assembled from the loop-body state, the `ExecIH` is applied, and
its `ExecExitD` is repackaged into `SubStmtReturn`.

`garm` is the arm-entry register frame (post-`execBlockA`, before the loop-body
`mv`s of `a0/a1/a2/a3`): `x8 = aStmt`, `x9 = aInterp`, `x18 = aRet`,
`x19 = aEnv`, `x2 = sp`. The loop-body setup only clobbers caller-saved `a*`
registers, so every callee-saved register still reads `garm R`.

The sub-derivation is `ExecS st d envSub sSub st' status` (the current statement
`stmts[i]` in the inner scope `envSub`); `aStmtSub`/`aEnvSub`/`aRetSub` are its
node/scope/retslot machine addresses.  The sub-retslot geometry (an 8-aligned
24-byte RAM slot above HTIF, disjoint from stack/arena/code) is threaded so the
`ret`-sub-status `ValueRepr` survives — it is exactly the shape `ExecEntry`
demands of a `ret`'s retslot. -/

end Vsa.Sim
