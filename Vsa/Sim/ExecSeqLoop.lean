import Vsa.Sim.ExecSimCommon
import Vsa.While.Cost

/-!
# Layer 4 — M4 statement family: the `ExecSeq` loop rule (the reusable heart)

This module builds the **`ExecSeq` loop rule** — the machinery that composes the
`block` arm's do-while over a statement array (and, later, `interp_run`'s
top-level loop) out of per-statement `exec_stmt` runs. It is the reusable heart
of the statement-sequencing keystone.

## The machine loop (block arm, decoded from `while-riscv-htif.elf`)

The `block` arm at `0x8000418c` first calls `env_new` (allocate a child scope
frame), then runs the do-while at `0x800041a4` over the block's `Stmt*` array:

```
8000418c:  mv   a0,s3            -- a0 = env (parent for env_new)
80004190:  jal  env_new          -- a0 := inner frame ptr
80004194:  lw   a5,16(s0)        -- a5 := block.count
80004198:  mv   s3,a0            -- s3 := inner (child scope)
8000419c:  li   a6,0            -- i := 0
800041a0:  blez a5,0x80004090    -- count ≤ 0 → normal exit (li a0,0)
-- loop head 0x800041a4 (ExecSeqEntry with remaining `ss`, `p = 0x800041a4`):
800041a4:  ld   a5,8(s0)         -- a5 := block.stmts (Stmt** base)
800041a8:  slli a4,a6,0x3        -- a4 := i*8
800041ac:  mv   a3,s2            -- a3 := retslot
800041b0:  add  a5,a5,a4         -- a5 := &stmts[i]
800041b4:  ld   a1,0(a5)         -- a1 := stmts[i]  (Stmt*)
800041b8:  mv   a2,s3            -- a2 := inner env
800041bc:  mv   a0,s1            -- a0 := interp*
800041c0:  sd   a6,8(sp)         -- spill i
800041c4:  jal  exec_stmt        -- RECURSIVE — a0 := status  (consumes an ExecIH)
800041c8:  bnez a0,0x8000409c    -- status ≠ 0 (abrupt) → exit (consAbrupt)
800041cc:  ld   a6,8(sp)         -- reload i
800041d0:  lw   a4,16(s0)        -- a4 := count
800041d4:  addi a6,a6,1          -- i := i+1
800041d8:  sext.w a5,a6
800041dc:  blt  a5,a4,0x800041a4 -- i < count → loop (consNormal, back-edge)
800041e0:  li   a0,0            -- all stmts done
800041e4:  j    0x8000409c       -- normal exit
```

Both the abrupt exit (`0x800041c8`) and the normal fallthrough (`0x800041e0`)
join the shared statement epilogue at `0x8000409c` (`ExecSeqExit`, `contPC`).

## The reusable heart

`ExecSeqStep p q` packages ONE machine loop iteration: from `ExecSeqEntry` at the
loop head `p` for a non-empty remaining list `s :: ss`, run the per-iteration
glue (load `stmts[i]`, set up args, `jal exec_stmt`, check status, increment,
back-edge) — which recursively consumes an `exec_stmt` run (an `ExecIH`) — landing
either back at `p` (status `.normal`, `consNormal`) with the intermediate state
threaded, or at the continuation `q` (status abrupt, `consAbrupt`).

`execSeqLoop` then composes these steps by **list induction on the remaining
statement list** (the measure = `ss.length`, strictly decreasing per normal
iteration), yielding the whole-sequence Triple
`ExecSeqEntry (all ss) @ p → ExecSeqExit status @ q`. This is exactly the
do-while's total-correctness statement, and it is the piece every consumer
(`block`, `interp_run`) reuses.

The per-iteration `ExecSeqStep` (the machine glue + the recursive `exec_stmt`) is
the residual: it needs the block-arm loop-body decode threaded onto
`ExecEntry`/`ExecExit`. `execSeqLoop` is proved unconditionally on top of it.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1
open Register
open Vsa.Machine (MState Config)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

/-! ## Loop-head / continuation PCs of the block do-while -/

/-- The block do-while loop head (`0x800041a4`), where `ExecSeqEntry` is stated
for the remaining statement list. -/
def execSeqLoopPC : Nat := 0x800041a4

/-- The shared statement epilogue entry (`0x8000409c`), where both the abrupt
exit and the normal fallthrough land — the `ExecSeqExit` continuation PC. -/
def execSeqContPC : Nat := 0x8000409c

/-! ## `ExecSeqStep` — one machine loop iteration (the per-statement hypothesis)

From `ExecSeqEntry` at the loop head `p` for a NON-empty remaining list `s :: ss`
(the machine is about to dispatch `s` = `stmts[i]`), the iteration runs one
`exec_stmt` (recursively — this is where an `ExecIH` is consumed) and checks the
returned status:

* **normal** → the machine loops back to `p` (`consNormal`): the intermediate
  state `st'` (after `s`) is now the entry state for the remaining list `ss`, at
  the SAME loop-head PC `p`, with EXTENDED φ-maps (`exec_stmt` may allocate). The
  post is `∃ st' φf' φc', ExecS-consistent ∧ ExecSeqEntry ss @ p` for `st'`.

* **abrupt** (`status ≠ .normal`) → the machine jumps to `q` (`consAbrupt`): the
  post is `ExecSeqExit status @ q` for the state `st'` after `s`.

Both are packaged as ONE `Triple` whose post is the DISJUNCTION keyed on the
status the executed statement `s` produced (this mirrors the machine's
`bnez a0` branch). The spec-side `ExecS st d env s st' status` derivation for `s`
is threaded so the caller (`execSeqLoop`) can invoke the right `ExecSeq`
constructor.

`p`/`q` are the loop-head/continuation PCs; the remaining ghost/layout params
match `ExecSeqEntry`/`ExecSeqExit`.

The `stFin` parameter is the state at which the sequence as a whole terminates
(the final `ExecSeq` post-state). On the normal branch the φ-extension is stated
over `stFin`'s store sizes (not just the intermediate `st'`'s) so that the loop
rule can compose the per-iteration extensions all the way to the final exit
without a per-statement size-stability trick (statements grow the frame store, so
the expression-side `hSizeF ▸` idiom does not apply). Discharging this stronger
extension is part of the residual loop-body glue — it is where the block arm's
frame-allocation accounting lands. -/
def ExecSeqStep
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc : Addr → Nat)
    (st : St) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt)
    (sp r : BitVec 64) (p q : Nat) (m0 : Mem)
    (st' stFin : St) (status : Status) : Prop :=
  ExecS st d env s st' status →
    Triple
      (ExecSeqEntry g N A SL φf φc st d env (s :: ss) sp r p m0)
      (fun c =>
        (status = .normal ∧
          ∃ (φf' φc' : Addr → Nat),
            PhiExtends φf φf' stFin.store.frames.size ∧
            PhiExtends φc φc' stFin.store.closures.size ∧
            ExecSeqEntry g N A SL φf' φc' st' d env ss sp r p c.σ.mem c)
        ∨ (status ≠ .normal ∧
          ExecSeqExit g N A SL φf φc st.store.frames.size st.store.closures.size
            st' status sp r q m0 c))

/-! ## `execSeqExit_extend` — re-base an `ExecSeqExit` to earlier φ-maps

The only φ-dependent field of `ExecSeqExit` is `store` (an existential
`∃ φf'' φc'', PhiExtends φf' φf'' … ∧ StoreRepr … φf'' …`); every other field is
φ-independent. So an exit stated for extended maps `φf'`/`φc'` (fixed at the
sizes `nf'`/`nc'` of a LATER entry state) is also an exit for the earlier maps
`φf`/`φc` (fixed at the sizes `nf`/`nc` of an EARLIER entry state, `nf ≤ nf'`/
`nc ≤ nc'`) whenever `φf'`/`φc'` extend `φf`/`φc` over the later prefix —
compose the `PhiExtends` legs and weaken the bound with `PhiExtends.mono`. This
is what threads the per-iteration φ-extensions through `execSeqLoop`'s tail
recursion. -/
theorem execSeqExit_extend
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc φf' φc' : Addr → Nat)
    (nf nc nf' nc' : Nat)
    (st' : St) (status : Status) (sp r : BitVec 64) (q : Nat) (m0 : Mem)
    (mNow : Mem) (c : Config)
    (hmf : nf ≤ nf') (hmc : nc ≤ nc')
    (hpf : PhiExtends φf φf' nf')
    (hpc : PhiExtends φc φc' nc')
    (hexit : ExecSeqExit g N A SL φf' φc' nf' nc' st' status sp r q mNow c) :
    ExecSeqExit g N A SL φf φc nf nc st' status sp r q m0 c := by
  obtain ⟨φf'', φc'', hpf'', hpc'', hstore⟩ := hexit.store
  exact
    { good := hexit.good
      tick := hexit.tick
      pc := hexit.pc
      store := ⟨φf'', φc'',
        PhiExtends.mono hmf (hpf.trans hpf''),
        PhiExtends.mono hmc (hpc.trans hpc''), hstore⟩
      out := hexit.out
      frame := hexit.frame
      minstret := hexit.minstret }

/-! ## `execSeqLoop` — the loop rule (the reusable heart)

By list induction on the statement sequence `ss`, composing `ExecSeqStep`
iterations. The hypothesis `hstep` supplies, for EVERY suffix of the sequence and
every consistent intermediate state, one loop iteration; `execSeqLoop` folds them
into the whole-sequence Triple.

The measure is `ss.length` (each `consNormal` iteration drops the head, so it
strictly decreases; `consAbrupt`/`nil` terminate). The φ-maps thread through the
normal iterations (each `exec_stmt` may allocate, extending them); the final exit
re-exposes the composed extension as `ExecSeqExit`'s existential.

`hstep` is the abstract form of "the block-arm loop body simulates one statement
plus the loop control". It is stated for the FIXED loop-head/continuation PCs
`p = execSeqLoopPC`, `q = execSeqContPC`, quantified over the remaining suffix and
intermediate state, so a single hypothesis covers every iteration. -/
theorem execSeqLoop
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (d : Nat) (env : Addr)
    (sp r : BitVec 64) (p q : Nat)
    -- The whole-sequence spec derivation, and its per-suffix packaging via
    -- `hstep`, are provided abstractly. `hstep` is parametric in the suffix and
    -- the intermediate maps/state, so it applies at every iteration.
    (hstep : ∀ (φf φc : Addr → Nat) (st : St) (s : Stmt) (ss : List Stmt)
        (st' stFin : St) (status : Status) (m0 : Mem),
        ExecSeqStep g N A SL φf φc st d env s ss sp r p q m0 st' stFin status)
    -- The empty-sequence fallthrough hop `p → q` (`li a0,0; j 0x8000409c`), which
    -- also terminates every finished `consNormal` chain. A one-instruction
    -- straight-line Triple; the residual loop-tail glue.
    (hnil : ∀ (φf φc : Addr → Nat) (st : St) (m0 : Mem),
        Triple
          (ExecSeqEntry g N A SL φf φc st d env [] sp r p m0)
          (ExecSeqExit g N A SL φf φc st.store.frames.size st.store.closures.size
            st .normal sp r q m0)) :
    ∀ (ss : List Stmt) (φf φc : Addr → Nat) (st st' : St) (status : Status)
      (m0 : Mem),
      ExecSeq st d env ss st' status →
      Triple
        (ExecSeqEntry g N A SL φf φc st d env ss sp r p m0)
        (ExecSeqExit g N A SL φf φc st.store.frames.size st.store.closures.size
          st' status sp r q m0) := by
  -- `ExecSeq` is mutually inductive, so we cannot `induction` on the derivation
  -- directly. Instead we induct on the statement list `ss` (the measure), and
  -- `cases` the `ExecSeq` derivation to peel `nil`/`consNormal`/`consAbrupt` at
  -- each length. `st`/`st'`/`status`/maps/`m0` are all generalized (re-introduced
  -- after the induction) so the tail recursion can re-instantiate them.
  intro ss
  induction ss with
  | nil =>
    intro φf φc st st' status m0 hSeq
    cases hSeq with
    | nil =>
      -- Empty sequence: the machine falls through to its normal exit
      -- (`li a0,0; j 0x8000409c`). This `p → q` hop is the `hnil` residual; it
      -- also terminates every finished `consNormal` chain.
      exact hnil φf φc st m0
  | cons s ss ih =>
    intro φf φc st st' status m0 hSeq
    cases hSeq with
    | consNormal _ _ _ _ _ stMid _ _ hS hSeqTail =>
      -- Non-empty, head runs to `.normal`: one iteration loops back to `p`,
      -- then recurse on the tail from the intermediate state `stMid`.
      intro c hc
      obtain ⟨c₁, hs₁, hpost⟩ :=
        hstep φf φc st s ss stMid st' .normal m0 hS c hc
      rcases hpost with ⟨_, φf', φc', hpf, hpc, hEntry'⟩ | ⟨hne, _⟩
      · obtain ⟨c₂, hs₂, hexit⟩ :=
          ih φf' φc' stMid st' status c₁.σ.mem hSeqTail c₁ hEntry'
        -- The tail's exit is stated for the extended maps `φf'`/`φc'` (fixed at
        -- `stMid`'s entry sizes); re-expose it against the original `φf`/`φc`
        -- (fixed at `st`'s sizes) by composing the φ-extensions, weakening the
        -- agreement bounds along the store-size monotonicity of the sub-runs.
        have hSle := execS_store_mono hS
        have hTle := execSeq_store_mono hSeqTail
        refine ⟨c₂, hs₁.trans hs₂, ?_⟩
        exact execSeqExit_extend g N A SL φf φc φf' φc'
          st.store.frames.size st.store.closures.size
          stMid.store.frames.size stMid.store.closures.size
          st' status sp r q m0 c₁.σ.mem c₂
          hSle.1 hSle.2
          (PhiExtends.mono hTle.1 hpf) (PhiExtends.mono hTle.2 hpc) hexit
      · exact absurd _root_.rfl hne
    | consAbrupt _ _ _ _ _ _ _ hS hne =>
      -- Non-empty, head runs abrupt: one iteration exits to `q`.
      intro c hc
      obtain ⟨c₁, hs₁, hpost⟩ :=
        hstep φf φc st s ss st' st' status m0 hS c hc
      rcases hpost with ⟨heq, _⟩ | ⟨_, hexit⟩
      · exact absurd heq hne
      · exact ⟨c₁, hs₁, hexit⟩

end Vsa.Sim
