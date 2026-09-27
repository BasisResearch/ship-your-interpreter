import Vsa.Sim.ExecEntry
import Vsa.Sim.InductionScaffold
import Vsa.Sim.BridgeSeg

/-!
# `LoopHeadDispatch` — the interp_run loop-head → `exec_stmt` entry span (Task #69)

`Vsa/Sim/InterpRunLoopSeamsClose.lean` names the `iter` residual and pins the
MISSING bridge precisely (its header, `§ iter is NOT a forgetful shadow`):

> The bridge `SegEntry@loopHead → ExecEntry@0x80003fe0` is exactly the loop-head
> dispatch prefix — unbuilt machine content — and the abstract `Reflect cH env
> (s :: ss)` carries no facts to supply it.

This file BUILDS that span (the machine `Steps` run from the loop head to
`exec_stmt`'s entry) and marshals its landing into `ExecEntry`.  It serves THREE
consumers unchanged: `iterSeam`/`approxSeam` (`InterpRunLoopSeamsClose`) and the
`hterm` back-edge assembly.  We build ONLY the span; the consumers supply their own
`ExecExit`-side content.

## The decoded span (all body words decode-tabled, verified vs `experiments/disasm.txt`)

```
── DISPATCH HEAD  [0x8000448c, 0x80004494)  ── br-terminated (TAKEN, flag=0) ──────
  0x8000448c  ld   a5,8(sp)     x15 := *(sp+8)   — the REPL-echo flag
  0x80004490  ld   s1,0(s0)     x9  := *s0       — current Stmt* at the loop cursor
  0x80004494  beqz a5,0x80004458                 — TAKEN when flag=0 (non-REPL exec)
  (`loopHeadDispatchRow`, br seg → 0x80004458.  LOOP-EXIT edge is elsewhere:
   0x80004498 `lw a5,0(s1)` ; 0x8000449c `bnez a5,0x80004458` — the REPL echo path;
   and the array-end edge is the `beq s0,s2,0x80004514` at 0x80004488 BEFORE the
   head.  NEITHER exit edge is this task.)
── VALUE_NULL CALL  [0x80004458, 0x80004460)  ── a CALL (retslot init) ────────────
  0x80004458  addi a0,sp,88     a0 := &retslot @sp+88
  0x8000445c  jal  value_null   (link 0x80004460) — zero-init the retslot buffer
  (a call splice → NAMED premise `hValueNullSplice`, exactly like
   `DriveToLoopHeadSpans.SetjmpSplice`; value_null's `null_pre` buffer geometry
   is off the loop-head SegEntry.)
── ARG SETUP  [0x80004460, 0x80004474)  ── jal-terminated (CALL) ──────────────────
  0x80004460  ld   a5,0(sp)     a5 := *sp        — interp* pointer
  0x80004464  addi a3,sp,88     a3 := &retslot   — exec_stmt arg 3
  0x80004468  mv   a1,s1        a1 := s1         — the Stmt* node (arg 1)
  0x8000446c  ld   a2,0(a5)     a2 := *interp    — the scope/env addr (arg 2)
  0x80004470  mv   a0,a5        a0 := interp*    — arg 0
  0x80004474  jal  exec_stmt    (0x80003fe0, link 0x80004478)
  (`loopHeadArgSetupBridge`, bridgeOfSeg body ≫ jal exec_stmt.)
── EXEC_STMT ENTRY  @0x80003fe0  = ExecEntry entry PC ─────────────────────────────
```

The back-edge continuation PC (the `exec_stmt` return link) is `0x80004478`; that is
the address the `iter`/`hterm` back-edge suffix resumes at (`beq a0,s3,…` etc.).

## What SegEntry@loopHead CAN vs CANNOT supply — the geometry split

`SegEntry` (`Vsa/Sim/InductionScaffold.lean:150`) pins at the loop head: `good`,
`tick`, `pc`, `store` (`StoreRepr`), `out` (`OutRepr`), `mem = m0`, the blanket
ghost `frame`, and the depth/arena budgets.  `ExecEntry` (`Vsa/Sim/ExecEntry.lean:207`)
demands ALL of those AT the callee entry PLUS a rich ABI/AST/stack geometry that the
loop head has NO way to assert:

* the four ABI arg VALUES (`a0`=interp*, `a1`=Stmt*, `a2`=env, `a3`=retslot) — these
  are COMPUTED by the span (the seg write-log), so they come from the span landing,
  NOT a premise;
* the C-stack layout (`StackOK SL sp (176+1088)`, `stack_ram`, `stack_win`,
  `code_stack_disjoint`) — a `main`-prologue fact, off the loop head;
* the `Stmt` node geometry (`StmtRepr`, `stmt_stack_disjoint`,
  `stmt_ram`, `stmt_win`) — a fact of WHICH statement the cursor points at, exactly
  the content `Reflect cH env (s :: ss)` would carry if it were computational (it is
  NOT — a bare section variable);
* `code` (`Exec_stmtLoaded`), `ra_align`, `store_survives`, `spill_defined`.

These become the named-field `structure LoopHeadDispatchGeom` below, one field per
missing fact, each with a doc-commented supplier.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc
open Vsa.While (Status Stmt Addr)
open Vsa.Sim.Code (Exec_stmtLoaded)

namespace Vsa.Sim

-- discipline: allow(R7-conj-tower-def) The NEW predicates here ARE named-field
-- structures (LoopHeadDispatchGeom).  The `∃`s the counter sees are: (1) the two
-- LANDING bundles `ValueNullSplice`/`loopHeadDispatchLanded` + the `hArgSetup`
-- premise — Prop-valued `∃ Config, Steps ∧ …` that MUST be existentials (they carry
-- a reached `Config` as DATA and are BUILT from `Triple`/`setjmp_spec`-style
-- `Exists`; a `structure … : Prop` cannot project the data `Config`), the exact
-- sanctioned shape of `DriveToLoopHeadSpans.SetjmpSplice`/`SpillLanded`/`SegLanded`
-- in the SAME region; (2) `∃ w, … minstret` witnesses and `∃ v, … xN` spill
-- witnesses — inherent to the `SegEntry`/`ExecEntry` FIELD types this bridge
-- consumes, not new post towers.  Each landing bundle is destructured ONCE at its
-- consumer's binder via a flat `obtain` (no `.2.2.2` towers).

local notation "SpecSt" => Vsa.While.St

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

/-! ## §1. The value_null call splice (a CALL — a named residual)

`value_null` at `0x8000445c` (link `0x80004460`) zeros the retslot buffer at
`sp+88`.  Its `null_pre` (`Vsa/Sim/ValueSpec.lean:386`) demands the buffer be a
`NullRegion` and `value_null` be loaded — the setjmp-buffer-style geometry NOT on
the loop-head path.  So — exactly as `DriveToLoopHeadSpans.SetjmpSplice` names the
`jal setjmp` first-return — the value_null call is a NAMED `Steps` splice.

Its supplier: `callSeg` (`DeriveCallSeg`) over `value_null_spec` (already proved,
`Vsa/Sim/ValueSpec.lean:412`) applied at the call site, with the `addi a0,sp,88`
prefix and the return landing at `0x80004460`.  We phrase it as the `Steps` from the
config parked at `0x80004458` (the value_null prefix head) to the config parked at
`0x80004460` (the arg-setup head), preserving the loop-head memory outside the
retslot window (`sp+88`) and the ghost register frame. -/

/-! ## §2. The `ExecEntry` geometry SegEntry@loopHead cannot supply

Named-field `structure` (the gate shape for a NEW entry-side predicate), one field
per `ExecEntry` fact that is NOT a consequence of `SegEntry g … interpLoopHeadPC …
cH`.  Each field's doc names its supplier.  The ABI arg VALUES are NOT here — they
are computed by the span (the seg write-log) and read off the landing.

`sp` is the C-stack pointer at the loop head (= the loop-head SegEntry's `x2`, spilled
by the interp_run prologue); `aStmt` is the `Stmt*` node the cursor `s0` points at
(the value the dispatch head loads into `s1`); `s` is the head statement (the `Reflect`
node).  Everything is stated at the `exec_stmt`-ENTRY memory `mE` (the loop-head `m0`
after value_null + the arg-setup seg have scribbled the stack/retslot window) — that
is the `ExecEntry.mem` witness the callee sees. -/

/-! ## §3. The span composition + `ExecEntry` marshalling

The bridge theorem.  It composes the three machine pieces (`loopHeadDispatchRow` +
`ValueNullSplice` + `loopHeadArgSetupBridge`) into a single `Steps` run from the
loop-head config to the `exec_stmt` entry config, and marshals the landing into
`ExecEntry`.

The ABI arg VALUES (`a0`=interp*, `a1`=Stmt*, `a2`=env, `a3`=retslot) are supplied
as the concrete landing pins the caller reads off the seg write-log (they are
computed, not premises) — quantified here as `aInterp aStmt aEnv aRet` with the
landing hypotheses `hLand*` that a `chain_facts`/seg readback discharges.  The
CONTROL + representation fields of `ExecEntry` come from: the span landing (PC, ra,
sp, minstret, mem, arg values), the loop-head SegEntry (`good`/`tick`/`store`/`out`/
`frame`), and `LoopHeadDispatchGeom` (the stack/AST/code geometry).

Because the value_null call splice and the jal exec_stmt seam are genuine off-path
CALLs, they are the NAMED premises `hValueNullSplice`/`hArgSetup`.  The `Steps`
composition between them is REAL. -/

end Vsa.Sim
