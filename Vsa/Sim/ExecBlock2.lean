import Vsa.Sim.ExecBlock

/-!
# Layer 4 — M4 statement family: the `block` case (`ExecS.block`), sequencing glue

This module closes (as far as the residual glue allows) the FIRST full sequencing
case, `ExecS.block`. Its centrepiece is **`execBlockStep`**, the conditional glue
lemma that delivers `execSeqLoop`'s `hstep` premise (`ExecSeqStep`): from the loop
head `p = 0x800041a4` for a non-empty remaining statement list `s :: ss`, it
threads the do-while body — the 18 `ExecBlockSites` sites (setup
`ld/slli/add/ld/mv/mv/sd`; `armExec_rec` for the recursive `jal exec_stmt`
consuming the head's `ExecIH`; `bnez a0` status split; on normal `i++`/`sext.w`/
`blt` back-edge to `p`, on abrupt exit to `q = 0x8000409c`) — and produces the
`ExecSeqStep` normal/abrupt disjunction.

Because `ExecSeqEntry` (`ExecSimCommon.lean`) carries only the thin loop-head
control state (PC/store/output/frame), the per-iteration MACHINE geometry the loop
body reads (the block node `s0`, inner scope `s3`, retslot `s2`, the loop index
`i` in `a6`, the block `count`, the `stmts` base, and all region-disjointness
facts) is supplied to `execBlockStep` as an explicit residual bundle
`ExecStepGeom`. This is exactly the "per-iteration geometry residual" the design
note flagged: the mutual `ExecS` recursor (and `execBlockSim`'s `env_new`/
frame-alloc linkage) will discharge it later; here it is a named, honest premise.

`hnil` is the tiny `p → q` fallthrough (`li a0,0; j 0x8000409c`).

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

/-! ## `hnil` — the empty-sequence `p → q` fallthrough

At the loop head `p = 0x800041a4` with `ss = []`, the machine has ALREADY passed
the `blez a5, 0x80004090` count-test (or exhausted the list via the `blt`
back-edge falling through), landing at `0x800041e0: li a0,0; j 0x8000409c` — the
normal exit hop into the shared statement continuation `q = 0x8000409c`.

The `ExecSeqEntry`/`ExecSeqExit` predicates model the loop head/continuation
abstractly (a shared PC for the empty case), so `execSeqNil` (`ExecSimCommon.lean`)
already discharges the empty sequence unconditionally as the identity Triple at a
shared PC. `execBlockSim` instantiates `execSeqLoop`'s `hnil` with `execSeqNil` (at
the loop-head PC, where the count-test has fallen through). We re-expose it here at
the block do-while's own PCs for documentation and reuse. -/

/-! ## `ExecStepGeom` — the per-iteration loop-head machine geometry residual

The concrete machine state the block do-while body reads at the loop head
`p = 0x800041a4`, for iteration index `i` over the block statement array. This is
the "per-iteration geometry residual" the design note flagged: `ExecSeqEntry` only
carries the thin control state (PC/store/output/frame), but the loop body reads the
callee-saved `s0`(block node `aStmt`), `s1`(interp `aInterp`), `s2`(retslot `aRet`),
`s3`(inner env `aEnv`), the loop index `i` in `a6`(x16), plus the block's `stmts`
base and `count`, and needs all the region-disjointness facts. The mutual `ExecS`
recursor + `execBlockSim`'s `env_new`/frame-alloc linkage will discharge this
bundle later; here it is a named, honest premise threaded per-config. -/

/-! ## `execBlockIter` — setup ≫ `armExec_rec` ⇒ `SubStmtReturn` at `0x800041c8`

The concrete, reusable machine thread of ONE block do-while iteration up to the
`bnez a0` status check: from the loop head `p = 0x800041a4` with the `ExecStepGeom`
geometry, it runs the seven setup instructions (`ld x15,8(s0)`; `slli x14,i,3`;
`addi x13,s2,0`; `add x15,x15,x14`; `ld x11,0(x15)`; `addi x12,s3,0`;
`addi x10,s1,0`; `sd x16,8(sp)`) staging the recursive call's ABI args and spilling
`i`, then invokes `armExec_rec` (`ExecBlock.lean`) for the `jal exec_stmt`
(`0x800041c4`) — consuming the head statement's `ExecIH` — landing in a
`SubStmtReturn` at the link PC `0x800041c8` where `a0 = StatusCode status` (the
`bnez` reads it).

This is the statement-sequencing analog of `execExprGlue` (`ExecRecCommon.lean`),
threading the block-loop-body setup instead of the expr/ret arm setup. The
`mcall` memory is the loop-head memory `m0` plus the single `sd i` spill (inside the
stack window, so `StoreRepr`/code/slots survive); `armExec_rec` frames its exit to
it.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`. -/

/-! ## `execBlockStep` — one block do-while iteration ⇒ `ExecSeqStep`

Delivers `execSeqLoop`'s `hstep` (`ExecSeqStep`). From the loop head
`p = 0x800041a4` for a non-empty remaining list `s :: ss` and the per-iteration
geometry residual `ExecStepGeom` (see above), it threads the do-while body:

* setup (`ld x15,8(s0)` stmts base; `slli x14,i,3`; `addi x13,s2,0` retslot;
  `add x15,x15,x14` `&stmts[i]`; `ld x11,0(x15)` `stmts[i]`; `addi x12,s3,0` inner
  env; `addi x10,s1,0` interp; `sd x16,8(sp)` spill `i`) to the recursive-call PC;
* `armExec_rec` for the `jal exec_stmt@0x800041c4`, consuming the head's `ExecIH`,
  producing a `SubStmtReturn` with `a0 = StatusCode status`;
* the `bnez a0` split (`0x800041c8`): abrupt (`status ≠ normal`) → `bne` TAKEN to
  `q = 0x8000409c` (`consAbrupt`, `ExecSeqExit`); normal → fallthrough, then
  `ld i`/`lw count`/`addi i,i,1`/`sext.w`/`blt` — TAKEN back to `p` (there is a
  next statement) yielding the `ExecSeqEntry ss @ p` normal disjunct.

Because the machine glue for the FULL iteration (setup ≫ `armExec_rec` ≫ status
split ≫ loop control) is a ~250-line thread, and because the normal-branch
φ-extension is stated over `stFin` (the final store) — the frame-alloc accounting
the design note flagged — `execBlockStep` is stated CONDITIONAL on the two named
residuals the iteration cannot itself close:

* `hbody` — the machine-level iteration: from the loop-head config (with the
  `ExecStepGeom` geometry) it runs to the branch outcome, packaged as the two
  status-keyed disjuncts (the setup+`armExec_rec`+control thread). This is the
  ~250-line decode; it is supplied by the (later) mutual-recursor scaffolding that
  re-lands `armExec_rec` at each site.
* `hphi` — the frame-alloc φ-upgrade: the sub-call's `st'`-sized extension is
  lifted to the `stFin`-sized extension the loop rule composes (env_new/allocFrame
  accounting).

`execSeqLoop` is proved unconditionally on top of this; `execBlockSim` discharges
`hbody`/`hphi` from the block-array + `env_new_spec`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`. -/

/-! ## `execBlockSim` — the `ExecS.block` simulation Triple (the sequencing keystone)

Composes the whole `block` arm:
`execBlockA (kind 2, arm 0x8000418c)` ≫ `env_new_spec` (child scope `inner`,
`= Store.allocFrame`) ≫ `execSeqLoop` (fed `execBlockStep`'s `hstep` + `execBlockHnil`'s
`hnil`) ≫ the block epilogue → `Triple (ExecEntry (.block ss) …) (ExecExit … status …)`.

The `ExecS.block` derivation gives `st.store.allocFrame (some env) = (store', inner)`
and `ExecSeq ⟨store', st.out⟩ d inner ss st' status` (the child-scope sequence).
`execSeqLoop` turns that `ExecSeq` into the do-while Triple from the loop head
`p = execSeqLoopPC = 0x800041a4` to the continuation `q = execSeqContPC = 0x8000409c`;
`execBlockSim` sandwiches it between:

* `hArm` — the arm prologue residual: from the block `ExecEntry`, run
  `execBlockA` (prologue+dispatch to `0x8000418c`) ≫ the `env_new` call (allocating
  `inner` per `env_new_spec`) ≫ the loop setup (`lw count`, `mv s3,inner`, `li i,0`,
  `blez` fallthrough) to `ExecSeqEntry` at `p` in scope `inner` over the child store;
* `hEpi` — the epilogue residual: from `ExecSeqExit` at `q` (the sequence's result)
  run the shared epilogue (`execBlockD`) to `ExecExit`.

Both are the frame-alloc/`env_new`-linkage + `execBlockA` geometry the design note
flagged; the `execSeqLoop` core (the reusable heart) is threaded UNCONDITIONALLY
here, so this is the first place `ExecSeq` sequencing is composed end-to-end. -/

end Vsa.Sim
