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
theorem execExit_extend
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc φf' φc' : Addr → Nat)
    (nf nc nf' nc' : Nat)
    (st' : Vsa.While.St) (status : Status) (sp r aRet : BitVec 64) (m0 mNow : Mem) (c : Config)
    (hpf : PhiExtends φf φf' nf)
    (hpc : PhiExtends φc φc' nc)
    (hle : nf ≤ nf' ∧ nc ≤ nc')
    (hmem : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      mNow[a]? = m0[a]?)
    (hexit : ExecExit g N A SL φf' φc' nf' nc' st' status sp r aRet mNow c) :
    ExecExit g N A SL φf φc nf nc st' status sp r aRet m0 c := by
  obtain ⟨φf'', φc'', hpf'', hpc'', hstore⟩ := hexit.store
  exact
    { good := hexit.good
      tick := hexit.tick
      pc := hexit.pc
      a0 := hexit.a0
      ra := hexit.ra
      spReg := hexit.spReg
      minstret := hexit.minstret
      store := ⟨φf'', φc'', hpf.trans (PhiExtends.mono hle.1 hpf''),
        hpc.trans (PhiExtends.mono hle.2 hpc''), hstore⟩
      out := hexit.out
      retval := by
        intro v hv
        obtain ⟨φcr, hpcr, hval⟩ := hexit.retval v hv
        exact ⟨φcr, hpc.trans (PhiExtends.mono hle.2 hpcr), hval⟩
      frame := hexit.frame
      memFrame := by
        intro a hstk harena
        rcases hexit.memFrame a hstk harena with hret | heq
        · exact Or.inl hret
        · exact Or.inr (heq.trans (hmem a hstk harena)) }

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
theorem execWhileLoopSim
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc : Addr → Nat)
    (st st' st'' st''' : Vsa.While.St) (d : Nat) (env : Addr) (c : Expr) (b : Stmt)
    (v : Value) (bodyStatus status' : Status)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) (out0 : Array String)
    -- the loop's spec derivation via `whileLoop` (bundles `EvalE`, truthy, body,
    -- the loop-back status side-condition, and the recursive sub-`while`):
    (_hExec : ExecS st d env (.whileStmt c b) st''' status')
    -- store counts only grow: the entry `st` is no larger than the re-entry `st''`
    -- (one body iteration) nor the final `st'''` (supplied from the `whileLoop`
    -- constructor's sub-derivations at the caller).
    (hSizeMid : st.store.frames.size ≤ st''.store.frames.size ∧
      st.store.closures.size ≤ st''.store.closures.size)
    (hSizeFin : st.store.frames.size ≤ st'''.store.frames.size ∧
      st.store.closures.size ≤ st'''.store.closures.size)
    -- the loop-back side-condition: the body completed `.normal`/`.cont`.
    (hloop : bodyStatus = .normal ∨ bodyStatus = .cont)
    -- ONE machine iteration from `st` (its loop-back branch re-enters at `st''`).
    (hstep : ExecWhileStep g N A SL φf φc st d env c b sp r aInterp aStmt aEnv aRet
      m0 out0 st'' st''' bodyStatus status')
    -- the RECURSIVE sub-`while` IH (`ExecS st'' … (.whileStmt c b) st''' status'`),
    -- supplied by the Layer-4 mutual recursor — quantified over the extended maps
    -- and the re-entry memory baseline the iteration hands it. NO self-recursion.
    (hWhileIH : ∀ (φf' φc' : Addr → Nat) (m0' : Mem),
      Triple
        (fun cfg => ExecEntry g N A SL φf' φc' st'' d env (.whileStmt c b)
          sp r aInterp aStmt aEnv aRet m0' cfg ∧ cfg.σ.sailOutput = out0)
        (ExecExit g N A SL φf' φc' st''.store.frames.size st''.store.closures.size
          st''' status' sp r aRet m0')) :
    Triple
      (fun cfg => ExecEntry g N A SL φf φc st d env (.whileStmt c b)
        sp r aInterp aStmt aEnv aRet m0 cfg ∧ cfg.σ.sailOutput = out0)
      (ExecExit g N A SL φf φc st.store.frames.size st.store.closures.size
        st''' status' sp r aRet m0) := by
  intro cfg hpre
  -- one iteration → the loop-back re-entry (extended φ, rebased-to-`m0` memory).
  obtain ⟨c₁, hs₁, hpost⟩ := hstep cfg hpre
  rcases hpost with ⟨_, φf', φc', hpf, hpc, hEntry', hout', hmem'⟩ | ⟨hne, _⟩
  · -- run the REST of the loop from `st''` via the recursive IH …
    obtain ⟨c₂, hs₂, hexit⟩ :=
      hWhileIH φf' φc' c₁.σ.mem c₁ ⟨hEntry', hout'⟩
    -- … then re-base its exit (maps `φf'`/`φc'`, baseline `c₁.σ.mem`) to the entry
    -- maps `φf`/`φc` and baseline `m0` via the step's φ-extensions + mem-agreement.
    refine ⟨c₂, hs₁.trans hs₂, ?_⟩
    exact execExit_extend g N A SL φf φc φf' φc'
      st.store.frames.size st.store.closures.size
      st''.store.frames.size st''.store.closures.size
      st''' status' sp r aRet m0 c₁.σ.mem c₂
      (PhiExtends.mono hSizeFin.1 hpf) (PhiExtends.mono hSizeFin.2 hpc) hSizeMid hmem' hexit
  · -- exit disjunct: impossible — the body status is `.normal`/`.cont` (`hloop`).
    exact absurd hloop hne

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
theorem execWhileSim
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (d : Nat) (env : Addr) (c : Expr) (b : Stmt)
    (sp r aInterp aStmt aEnv aRet : BitVec 64)
    -- one machine iteration, parametric in intermediate state / maps / statuses
    -- (covers the loop-back re-entry AND the single-iteration exits):
    (hstep : ∀ (φf φc : Addr → Nat) (st stMid stFin : Vsa.While.St)
        (bodyStatus loopStatus : Status) (m0 : Mem) (out0 : Array String),
        ExecWhileStep g N A SL φf φc st d env c b sp r aInterp aStmt aEnv aRet m0 out0
          stMid stFin bodyStatus loopStatus)
    -- the recursive sub-`while` IH (mutual recursor) — only the `whileLoop` case
    -- consumes it, at its intermediate state; supplied over the extended maps and
    -- the re-entry baseline the iteration hands it.
    (hWhileIH : ∀ (φf' φc' : Addr → Nat) (st'' st''' : Vsa.While.St)
        (status' : Status) (m0' : Mem) (out0' : Array String),
        ExecS st'' d env (.whileStmt c b) st''' status' →
        Triple
          (fun cfg => ExecEntry g N A SL φf' φc' st'' d env (.whileStmt c b)
            sp r aInterp aStmt aEnv aRet m0' cfg ∧ cfg.σ.sailOutput = out0')
          (ExecExit g N A SL φf' φc' st''.store.frames.size st''.store.closures.size
            st''' status' sp r aRet m0'))
    (φf φc : Addr → Nat) (st st' : Vsa.While.St) (status : Status) (m0 : Mem)
    (out0 : Array String)
    (hExec : ExecS st d env (.whileStmt c b) st' status) :
    Triple
      (fun cfg => ExecEntry g N A SL φf φc st d env (.whileStmt c b)
        sp r aInterp aStmt aEnv aRet m0 cfg ∧ cfg.σ.sailOutput = out0)
      (ExecExit g N A SL φf φc st.store.frames.size st.store.closures.size
        st' status sp r aRet m0) := by
  cases hExec
  case whileFalse v hfalsy hEval =>
    -- cond falsy → no body: single-iteration exit (any exit-shaped body status).
    exact execWhileExit g N A SL d env c b sp r aInterp aStmt aEnv aRet hstep
      φf φc st st' .normal m0 out0
      (.whileFalse st d env c b st' v hEval hfalsy) .brk (by rintro (h | h) <;> cases h)
  case whileBreak stInt v htruthy hEval hBody =>
    -- body `.brk` → single-iteration exit (any exit-shaped body status).
    exact execWhileExit g N A SL d env c b sp r aInterp aStmt aEnv aRet hstep
      φf φc st st' .normal m0 out0
      (.whileBreak st d env c b stInt st' v hEval htruthy hBody) .brk
      (by rintro (h | h) <;> cases h)
  case whileRet v rv htruthy hEval hBody =>
    -- body `.ret rv` → single-iteration exit (any exit-shaped body status).
    exact execWhileExit g N A SL d env c b sp r aInterp aStmt aEnv aRet hstep
      φf φc st st' (.ret rv) m0 out0
      (.whileRet st d env c b _ st' v rv hEval htruthy hBody) .brk
      (by rintro (h | h) <;> cases h)
  case whileLoop stI1 stI2 v bs htruthy hloop hEval hBody hRest =>
    -- recursive: one iteration (loop-back, body status `bs = .normal/.cont`) ≫
    -- the recursive sub-`while` IH on the strictly-smaller `whileLoop` premise.
    have hmMid : st.store.frames.size ≤ stI2.store.frames.size ∧
        st.store.closures.size ≤ stI2.store.closures.size :=
      ⟨Nat.le_trans (evalE_store_mono hEval).1 (execS_store_mono hBody).1,
       Nat.le_trans (evalE_store_mono hEval).2 (execS_store_mono hBody).2⟩
    have hmFin : st.store.frames.size ≤ st'.store.frames.size ∧
        st.store.closures.size ≤ st'.store.closures.size :=
      ⟨Nat.le_trans hmMid.1 (execS_store_mono hRest).1,
       Nat.le_trans hmMid.2 (execS_store_mono hRest).2⟩
    exact execWhileLoopSim g N A SL φf φc st stI1 stI2 st' d env c b v bs status
      sp r aInterp aStmt aEnv aRet m0 out0
      (.whileLoop st d env c b stI1 stI2 st' v bs status hEval htruthy hBody hloop hRest)
      hmMid hmFin
      hloop
      (hstep φf φc st stI2 st' bs status m0 out0)
      (fun φf' φc' m0' => hWhileIH φf' φc' stI2 st' status m0' out0 hRest)

end Vsa.Sim
