import Vsa.Sim.ExecWhile2
import Vsa.Sim.EnvNewSpec
import Vsa.Sim.ExecBlock

/-!
# Layer 4 — M4 `forStmt` case: the last control-flow loop (mirror of `whileStmt`)

`ExecS.forStart` allocates a child scope (`store.allocFrame` = `env_new`), runs the
optional `init` (`ExecInit`), then the `ForLoop` proper. `ForLoop` has the SAME
four-constructor loop shape as `whileStmt` — only the sub-relations differ
(`ForCond` = optional cond eval + truthy; `ExecStep` = optional step eval):

* `condFalse` (cond `some c` evals falsy → `.normal`), mirrors `whileFalse`;
* `bodyBreak` (`ForCond` passes, body `.brk` → `.normal`), mirrors `whileBreak`;
* `bodyRet` (`ForCond` passes, body `.ret rv` → propagate), mirrors `whileRet`;
* `loop` (`ForCond` passes, body `.normal`/`.cont`, `ExecStep`, RECURSE), mirrors
  `whileLoop` — the genuinely recursive constructor.

## Machine path (arm `0x80004234`, kind 5)

```
-- forStart prologue:
80004234:  mv   a0,s3            -- a0 := env
80004238:  jal  env_new          -- child scope (Store.allocFrame); a0 := new env
8000423c:  ld   a1,8(s0)         -- a1 := stmt->init   (offset 8)
80004240:  mv   s3,a0            -- s3 := inner (outer) env
80004244:  beqz a1,0x8000426c    -- no init → skip to cond head
80004248:  mv   a2,a0            -- (init present) a2 := env
8000424c:  mv   a3,s2            -- a3 := retslot
80004250:  mv   a0,s1            -- a0 := interp*
80004254:  jal  exec_stmt        -- init (ExecIH), link 0x80004258
80004258:  j    0x8000426c       -- → cond head (init's status discarded; ExecInit demands .normal)
-- back-edge status check (after body, reached via bne a0,1 at 0x800042c0):
8000425c:  li   a5,3
80004260:  beq  a0,a5,0x80004150 -- body status == 3 (ret) → propagate (bodyRet, ret epilogue)
80004264:  ld   a2,24(s0)        -- a2 := stmt->step   (offset 24)
80004268:  bnez a2,0x800042dc    -- step present → eval step, else fall to cond head
-- cond head 0x8000426c (loop head; init/step/no-cond fall here):
8000426c:  ld   a2,16(s0)        -- a2 := stmt->cond   (offset 16)
80004270:  beqz a2,0x800042a8    -- no cond (=truthy) → skip to body
80004274:  mv   a3,s3            -- a3 := env
80004278:  addi a0,sp,104        -- cond eval sret buffer (sp'+104)
8000427c:  mv   a1,s1
80004280:  jal  eval_expr        -- cond EvalIH, link 0x80004284
80004284..8000429c:  reload 24B + copy to value_truthy buf sp'+16
800042a0:  jal  value_truthy     -- a0 := (v.truthy ? 1 : 0)
800042a4:  beqz a0,0x80004090    -- FALSY → normal exit (condFalse)
-- body 0x800042a8 (no-cond falls here):
800042a8:  ld   a1,32(s0)        -- a1 := stmt->body   (offset 32)
800042ac:  mv   a3,s2            -- a3 := retslot
800042b0:  mv   a2,s3            -- a2 := env
800042b4:  mv   a0,s1            -- a0 := interp*
800042b8:  jal  exec_stmt        -- body (ExecIH), link 0x800042bc; status in a0
800042bc:  li   a5,1
800042c0:  bne  a0,a5,0x8000425c -- body status ≠ 1 (≠ brk) → back-edge check 0x8000425c
                                 --   else body status == 1 (brk) → fall to normal exit
800042c4:  li   a0,0             -- x10 := 0 = .normal (bodyBreak)
800042c8:  j    0x8000409c       -- shared epilogue
-- step eval 0x800042dc (step present, from 0x80004268):
800042dc:  mv   a3,s3
800042e0:  mv   a1,s1
800042e4:  addi a0,sp,16         -- step eval sret buffer (sp'+16)
800042e8:  jal  eval_expr        -- step EvalIH, link 0x800042ec
800042ec:  j    0x8000426c       -- → loop head (cond)
```

So (after the `forStart` prologue lands at the cond head `0x8000426c`) the loop
proper is: eval cond (or skip if none = truthy); falsy → normal exit; truthy → body
via a genuine `jal exec_stmt` (ordinary `ExecIH`, like `whileStmt` — NOT re-dispatch);
dispatch on the body's status — `.brk` → normal exit, `.ret v` → propagate (ret
epilogue `0x80004150`), `.normal`/`.cont` → eval the step (or skip) and loop back to
the cond head. IDENTICAL 4-way branch structure to `whileStmt`, plus the optional
`ForCond`/`ExecStep`.

The normal-exit tail (`0x80004090 li a0,0` / `0x80004094 j 0x8000409c`) is SHARED
with `whileStmt` (`condFalse` and `bodyBreak` both land there) — reuse
`site_80004090_es` / `site_80004094_es`.

Following the while family, the per-iteration machine work (`forStart` prologue,
cond/step eval, body recursion, loop control) is delivered as named residuals; the
loop rule (`ExecForStep` / `execForExit` / `execForLoopSim`) is proven UNCONDITIONALLY
on top of them, and the recursion is supplied as a hypothesis (NO `termination_by`).

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

/-! ## `ForEntry` — the `ForLoop` loop-head machine state (at the child scope)

`ForLoop st d outer cnd step b st'' status` operates in the child scope `outer`
starting at the machine cond head `0x8000426c`. `forStart` bridges the outer
`ExecEntry (.forStmt …)` to this state (via `env_new` + `ExecInit`); the loop rule
runs from here. The loop-head machine state is exactly an `ExecEntry` for the
`.forStmt` node re-entered at `outer` — the ordinary `exec_stmt` entry contract, but
with the scope being the freshly allocated child frame. We keep it as a plain
`ExecEntry (.forStmt oinit ocond ostep b)` (the abstract per-iteration and exit
contracts absorb the "resume at the cond head" machine detail as they do for
`whileStmt`). -/

/-! ## `ExecForStep` — one machine loop iteration (per-iteration hypothesis)

Mirror of `ExecWhileStep`. From `ExecEntry` at the for-loop head (child scope
`outer`), one iteration runs `ForCond` (cond eval + `value_truthy`, or none = truthy),
and — on the truthy path — the body via a genuine `jal exec_stmt` (`ExecIH`), then the
status dispatch and (on loop-back) the `ExecStep`:

* **loop-back** (body `.normal`/`.cont`, `ForLoop.loop`) → after `ExecStep` re-enter
  the head at `stMid` with EXTENDED φ-maps, own memory baseline `cfg.σ.mem`, and a
  memory-agreement clause vs the original `m0` (outside stack `[SL.lo, sp)` and arena
  `[A.lo, A.hi)`);
* **exit** (cond falsy `condFalse`, body `.brk` `bodyBreak`, body `.ret v` `bodyRet`)
  → land the `ExecExit` for `stMid`/`loopStatus` against `m0` directly.

Statement identical to `ExecWhileStep` but over `.forStmt oinit ocond ostep b` at the
child scope `outer`. `stFin` is the loop's final post-state; the loop-back
φ-extension is stated over `stFin`'s store sizes so the loop rule composes. -/
def ExecForStep
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (outer : Addr)
    (oinit : Option Stmt) (ocond ostep : Option Expr) (b : Stmt)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) (out0 : Array String)
    (stMid stFin : Vsa.While.St) (bodyStatus loopStatus : Status) : Prop :=
  Triple
    (fun cfg => ExecEntry g N A SL φf φc st d outer (.forStmt oinit ocond ostep b)
      sp r aInterp aStmt aEnv aRet m0 cfg ∧ cfg.σ.sailOutput = out0)
    (fun cfg =>
      -- loop-back branch: body normal/cont → step → re-enter the head at `stMid`
      (((bodyStatus = .normal ∨ bodyStatus = .cont) ∧
        ∃ (φf' φc' : Addr → Nat),
          PhiExtends φf φf' stFin.store.frames.size ∧
          PhiExtends φc φc' stFin.store.closures.size ∧
          ExecEntry g N A SL φf' φc' stMid d outer (.forStmt oinit ocond ostep b)
            sp r aInterp aStmt aEnv aRet cfg.σ.mem cfg ∧ cfg.σ.sailOutput = out0 ∧
          (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
            cfg.σ.mem[a]? = m0[a]?))
      ) ∨
      -- exit branch: falsy / brk / ret → land the exit against `m0`
      (¬ (bodyStatus = .normal ∨ bodyStatus = .cont) ∧
        ExecExit g N A SL φf φc stMid loopStatus sp r aRet m0 cfg))

/-! ## `execForExit` — the three non-recursive `ForLoop` constructors

`condFalse` (cond falsy → `.normal`), `bodyBreak` (body `.brk` → `.normal`), and
`bodyRet` (body `.ret v` → propagate) all EXIT the loop in one iteration. Each is
discharged directly by the `ExecForStep` iteration's EXIT branch (the machine's
`beqz a0` cond-falsy exit at `0x800042a4`, the `bne a0,1` NOT-taken brk-fall-through
to `0x800042c4`, and the `0x80004260 beq a0,3` ret-propagation). The `.brk`/`.ret v`
body statuses are `≠ .normal, .cont`, so the exit disjunct fires; the loop-back
disjunct is contradictory for these statuses.

Structurally IDENTICAL to `execWhileExit`. -/
theorem execForExit
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (d : Nat) (outer : Addr)
    (oinit : Option Stmt) (ocond ostep : Option Expr) (b : Stmt)
    (sp r aInterp aStmt aEnv aRet : BitVec 64)
    (hstep : ∀ (φf φc : Addr → Nat) (st stMid stFin : Vsa.While.St)
        (bodyStatus loopStatus : Status) (m0 : Mem) (out0 : Array String),
        ExecForStep g N A SL φf φc st d outer oinit ocond ostep b
          sp r aInterp aStmt aEnv aRet m0 out0 stMid stFin bodyStatus loopStatus)
    (φf φc : Addr → Nat) (st st' : Vsa.While.St) (status : Status) (m0 : Mem)
    (out0 : Array String)
    -- the loop's SINGLE-ITERATION exit witness: the body (if any) completes with a
    -- status that is NOT `.normal`/`.cont` (falsy = no body / `.brk` / `.ret v`).
    (bodyStatus : Status) (hexit : ¬ (bodyStatus = .normal ∨ bodyStatus = .cont)) :
    Triple
      (fun cfg => ExecEntry g N A SL φf φc st d outer (.forStmt oinit ocond ostep b)
        sp r aInterp aStmt aEnv aRet m0 cfg ∧ cfg.σ.sailOutput = out0)
      (ExecExit g N A SL φf φc st' status sp r aRet m0) := by
  intro cfg hpre
  obtain ⟨cE, hs, hpost⟩ := hstep φf φc st st' st' bodyStatus status m0 out0 cfg hpre
  rcases hpost with ⟨hlb, _⟩ | ⟨_, hE⟩
  · exact absurd hlb hexit
  · exact ⟨cE, hs, hE⟩

/-! ## `execForLoopSim` — the recursive `ForLoop` constructor (`ForLoop.loop`)

The IH-taking loop-back lemma, mirror of `execWhileLoopSim`. From `ExecEntry` at
`st` (the for-loop head at child scope `outer`):

* `hstep` (one `ExecForStep` iteration) runs `ForCond` (truthy), the body
  (`.normal`/`.cont`), and `ExecStep`, taking the LOOP-BACK branch: it re-enters the
  head at the intermediate state `stMid` with EXTENDED φ-maps `φf'`/`φc'`, own memory
  baseline `c₁.σ.mem`, and a memory-agreement clause vs `m0`.
* `hForIH` (the recursive sub-`for` IH — the derivation on the strictly-smaller
  `ForLoop.loop` premise `ForLoop stMid … st''' status'`, supplied by the Layer-4
  mutual recursor) runs the REST of the loop from that re-entry to the final
  `ExecExit`, against baseline `c₁.σ.mem`.

Composing: apply `hstep`, take the loop-back disjunct, feed the re-entry `ExecEntry`
to `hForIH`, then re-base its exit back to the entry maps `φf`/`φc` and baseline `m0`
via `execExit_extend`. Exactly the `execWhileLoopSim` composition, with the recursion
as a hypothesis (NO `termination_by`; `ForLoop` is a mutual inductive with the
non-variable index `.forStmt …`).

The exit disjunct of `hstep` is impossible here: `ForLoop.loop` fires precisely when
the body status is `.normal`/`.cont` (`hloop`). -/
theorem execForLoopSim
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc : Addr → Nat)
    (st stMid stFin : Vsa.While.St) (d : Nat) (outer : Addr)
    (oinit : Option Stmt) (ocond ostep : Option Expr) (b : Stmt)
    (bodyStatus status' : Status)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) (out0 : Array String)
    -- the loop-back side-condition: the body completed `.normal`/`.cont`.
    (hloop : bodyStatus = .normal ∨ bodyStatus = .cont)
    -- ONE machine iteration from `st` (its loop-back branch re-enters at `stMid`).
    (hstep : ExecForStep g N A SL φf φc st d outer oinit ocond ostep b
      sp r aInterp aStmt aEnv aRet m0 out0 stMid stFin bodyStatus status')
    -- the RECURSIVE sub-`for` IH (`ForLoop stMid … st''' status'`), supplied by the
    -- Layer-4 mutual recursor — quantified over the extended maps and the re-entry
    -- memory baseline the iteration hands it. NO self-recursion.
    (hForIH : ∀ (φf' φc' : Addr → Nat) (m0' : Mem),
      Triple
        (fun cfg => ExecEntry g N A SL φf' φc' stMid d outer (.forStmt oinit ocond ostep b)
          sp r aInterp aStmt aEnv aRet m0' cfg ∧ cfg.σ.sailOutput = out0)
        (ExecExit g N A SL φf' φc' stFin status' sp r aRet m0')) :
    Triple
      (fun cfg => ExecEntry g N A SL φf φc st d outer (.forStmt oinit ocond ostep b)
        sp r aInterp aStmt aEnv aRet m0 cfg ∧ cfg.σ.sailOutput = out0)
      (ExecExit g N A SL φf φc stFin status' sp r aRet m0) := by
  intro cfg hpre
  -- one iteration → the loop-back re-entry (extended φ, rebased-to-`m0` memory).
  obtain ⟨c₁, hs₁, hpost⟩ := hstep cfg hpre
  rcases hpost with ⟨_, φf', φc', hpf, hpc, hEntry', hout', hmem'⟩ | ⟨hne, _⟩
  · -- run the REST of the loop from `stMid` via the recursive IH …
    obtain ⟨c₂, hs₂, hexit⟩ :=
      hForIH φf' φc' c₁.σ.mem c₁ ⟨hEntry', hout'⟩
    -- … then re-base its exit to the entry maps `φf`/`φc` and baseline `m0`.
    refine ⟨c₂, hs₁.trans hs₂, ?_⟩
    exact execExit_extend g N A SL φf φc φf' φc' stFin status' sp r aRet m0 c₁.σ.mem
      c₂ hpf hpc hmem' hexit
  · -- exit disjunct: impossible — the body status is `.normal`/`.cont` (`hloop`).
    exact absurd hloop hne

/-! ## `execForLoopBody` — the `ForLoop` sub-relation, all four constructors unified

Dispatches on the `ForLoop` derivation: the three non-recursive constructors
(`condFalse`/`bodyBreak`/`bodyRet`) go to `execForExit`; the recursive `loop` goes to
`execForLoopSim`. The per-iteration `ExecForStep` (`hstep`) is supplied abstractly,
parametric in the intermediate state / maps / statuses / memory; the recursive
sub-`for` IH (`hForIH`) is the mutual-recursor IH the `loop` premise consumes.

This is the `ForLoop` analog of `execWhileSim`, over the child scope `outer` (the
`forStart` prologue's `env_new` + `ExecInit` bridge from the outer `ExecEntry
(.forStmt …)` to this loop head is delivered separately).

(The `cases hFor` binders are ONLY the non-index constructor arguments — the indices
`st`/`d`/`outer`/`cnd`/`step`/`b`, the result state, and the result status are pinned
by the goal's index and so are not re-introduced, exactly as for `execWhileSim`.) -/
theorem execForLoopBody
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (d : Nat) (outer : Addr)
    (oinit : Option Stmt) (ocond ostep : Option Expr) (b : Stmt)
    (sp r aInterp aStmt aEnv aRet : BitVec 64)
    -- one machine iteration, parametric in intermediate state / maps / statuses:
    (hstep : ∀ (φf φc : Addr → Nat) (st stMid stFin : Vsa.While.St)
        (bodyStatus loopStatus : Status) (m0 : Mem) (out0 : Array String),
        ExecForStep g N A SL φf φc st d outer oinit ocond ostep b
          sp r aInterp aStmt aEnv aRet m0 out0 stMid stFin bodyStatus loopStatus)
    -- the recursive sub-`for` IH (mutual recursor) — only the `loop` case consumes it.
    (hForIH : ∀ (φf' φc' : Addr → Nat) (st'' st''' : Vsa.While.St)
        (status' : Status) (m0' : Mem) (out0' : Array String),
        ForLoop st'' d outer ocond ostep b st''' status' →
        Triple
          (fun cfg => ExecEntry g N A SL φf' φc' st'' d outer (.forStmt oinit ocond ostep b)
            sp r aInterp aStmt aEnv aRet m0' cfg ∧ cfg.σ.sailOutput = out0')
          (ExecExit g N A SL φf' φc' st''' status' sp r aRet m0'))
    (φf φc : Addr → Nat) (st st' : Vsa.While.St) (status : Status) (m0 : Mem)
    (out0 : Array String)
    (hFor : ForLoop st d outer ocond ostep b st' status) :
    Triple
      (fun cfg => ExecEntry g N A SL φf φc st d outer (.forStmt oinit ocond ostep b)
        sp r aInterp aStmt aEnv aRet m0 cfg ∧ cfg.σ.sailOutput = out0)
      (ExecExit g N A SL φf φc st' status sp r aRet m0) := by
  cases hFor
  case condFalse c v hEval hfalsy =>
    -- cond falsy → no body: single-iteration exit (any exit-shaped body status).
    exact execForExit g N A SL d outer oinit (some c) ostep b
      sp r aInterp aStmt aEnv aRet hstep φf φc st st' .normal m0 out0
      .brk (by rintro (h | h) <;> cases h)
  case bodyBreak stInt hCond hBody =>
    -- body `.brk` → single-iteration exit (any exit-shaped body status).
    exact execForExit g N A SL d outer oinit ocond ostep b
      sp r aInterp aStmt aEnv aRet hstep φf φc st st' .normal m0 out0
      .brk (by rintro (h | h) <;> cases h)
  case bodyRet stInt rv hCond hBody =>
    -- body `.ret rv` → single-iteration exit (any exit-shaped body status).
    exact execForExit g N A SL d outer oinit ocond ostep b
      sp r aInterp aStmt aEnv aRet hstep φf φc st st' (.ret rv) m0 out0
      .brk (by rintro (h | h) <;> cases h)
  case loop stI1 stI2 stI3 bs hloopcond hCond hStep hBody hRest =>
    -- recursive: one iteration (loop-back, body status `bs = .normal/.cont`) ≫
    -- the recursive sub-`for` IH on the strictly-smaller `loop` premise.
    exact execForLoopSim g N A SL φf φc st stI3 st' d outer oinit ocond ostep b
      bs status sp r aInterp aStmt aEnv aRet m0 out0
      hloopcond
      (hstep φf φc st stI3 st' bs status m0 out0)
      (fun φf' φc' m0' => hForIH φf' φc' stI3 st' status m0' out0 hRest)

end Vsa.Sim
