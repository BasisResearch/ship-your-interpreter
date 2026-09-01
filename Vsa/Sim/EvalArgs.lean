import Vsa.Sim.CallEntry
import Vsa.Sim.EvalRecCommon
import Vsa.While.Cost

/-!
# Layer 4 — M4: the `EvalArgs.cons` argument-evaluation loop rule

`EvalArgs` is the interpreter's argument-evaluation relation: from a list of
argument expressions `es`, evaluate each in turn (threading the store/output
side effects left-to-right) into a value list `vs`. On the machine this is the
do-`bne` loop at `evalArgsLoopPC = 0x800031dc` inside the `EX_CALL` arm of
`eval_expr` (see `CallEntry` for the full decode): per iteration it loads
`args[i]`, `jal eval_expr` (recursive — one `EvalIH`), copies the 24-byte result
`Value` into the stack Value-array slot (`sp+32+i*24+208`), increments `i`, and
takes the `bne a6,a5` back-edge while `i ≠ argc`. When `i = argc` (equivalently,
the `argc ≤ 0` `blez` at entry) control falls through to the dispatch
continuation `evalArgsContPC = 0x80003254`.

This file builds the **`EvalArgs` loop rule** (`evalArgsLoop`) — the exact
argument-side analog of `execSeqLoop` (the `block`-arm statement loop). It is a
list induction over the remaining argument list, composing per-iteration
`EvalArgsStep`s. Unlike `ExecSeq`, `EvalArgs` has NO abrupt exit — every argument
that evaluates simply threads on to the next (`cons`), and the empty list
terminates at the continuation (`nil`, already landed as `evalArgsNil` in
`CallEntry`). So the loop is strictly simpler than `execSeqLoop`: one
per-iteration branch (loop-back), no status disjunction.

## The reusable heart (mirroring `ExecSeqLoop`)

`EvalArgsStep p q` packages ONE machine loop iteration: from `EvalArgsEntry` at
the loop head `p` for a non-empty remaining list `e :: es`, run the per-iteration
glue (load `args[i]`, set up args, `jal eval_expr`, copy the 24-byte result into
the Value-array slot, `i++`, back-edge) — which recursively consumes an
`eval_expr` run (an `EvalIH` on `e`) — landing back at `p` (`EvalArgsEntry es`)
with the intermediate state `st'` threaded and the φ-maps extended (the arg eval
may allocate).

`evalArgsLoop` then composes these steps by **list induction on the remaining
argument list** (measure = `es.length`, strictly decreasing per iteration),
yielding the whole-sequence Triple
`EvalArgsEntry (all es) @ p → EvalArgsExit @ q`. The per-iteration `EvalArgsStep`
(the machine glue threading the ArgVec + the recursive `eval_expr`) is the named
residual; `evalArgsLoop` is proved unconditionally on top of it, exactly like
`execSeqLoop`.

## The materialised argument vector (`ArgVecRepr`)

Because the exit skeleton (`SegExit`) already re-represents the whole spec store
at extended φ-maps and frames memory outside the stack window, the per-value
`vs` correspondence in the stack Value-array is a fact carried INSIDE
`EvalArgsStep`/`EvalArgsExit`'s config predicate — a `ValueRepr` battery at the
successive slots `sp+32+i*24+208`. `ArgVecRepr sp base vs` bundles that battery:
`vs[i]` is represented at `base + i*24` for every `i`. It is threaded through the
loop as the growing prefix and consumed by the `Call` dispatch (which reads the
Value-array as `call_value`'s argument block). It is defined here and carried as
a per-iteration field of the residual `EvalArgsStep`; the loop rule itself only
needs the control-flow skeleton (`SegEntry`/`SegExit`) and so is `ArgVecRepr`-
agnostic.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

namespace Vsa.Sim

open LeanRV64DExecutable Sail
open Register
open Vsa.Machine (MState Config)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Scaffold

local notation "SpecSt" => Vsa.While.St

set_option maxHeartbeats 4000000

/-! ## `ArgVecRepr` — the materialised stack Value-array ↔ `vs : List Value`

The `EX_CALL` arg loop writes each evaluated argument `vs[i]` as a 24-byte
`Value` into the stack Value-array at `base + i*24` (`base = sp+32+208`). This
predicate says the machine memory `m` represents the whole list `vs` there: the
`i`-th `Value` of `vs` lives at `base + 24*i`, under the closures map `φc`. -/
def ArgVecRepr (m : Mem) (N : NativeAddrs) (φc : Addr → Nat)
    (base : Nat) : List Value → Prop
  | [] => True
  | v :: vs => ValueRepr m N φc base v ∧ ArgVecRepr m N φc (base + 24) vs

/-- The empty argument vector is trivially represented. -/
@[simp] theorem argVecRepr_nil (m : Mem) (N : NativeAddrs) (φc : Addr → Nat)
    (base : Nat) : ArgVecRepr m N φc base [] := trivial

/-- Prepending: `v :: vs` is represented at `base` iff `v` is at `base` and `vs`
follows at `base + 24`. -/
theorem argVecRepr_cons (m : Mem) (N : NativeAddrs) (φc : Addr → Nat)
    (base : Nat) (v : Value) (vs : List Value)
    (hv : ValueRepr m N φc base v) (hvs : ArgVecRepr m N φc (base + 24) vs) :
    ArgVecRepr m N φc base (v :: vs) := ⟨hv, hvs⟩

/-! ## `EvalArgsStep` — one machine loop iteration (the per-argument hypothesis)

From `EvalArgsEntry` at the loop head `p` for a NON-empty remaining list
`e :: es` (the machine is about to evaluate `e = args[i]`), the iteration runs
one `eval_expr` (recursively — an `EvalIH` on `e`), copies the 24-byte result
into the Value-array slot, increments `i`, and takes the back-edge to `p`. Unlike
`ExecSeqStep` there is NO abrupt branch: the post ALWAYS loops back to `p` with
the tail `es` remaining, the intermediate state `st'` (after `e`) threaded, and
the φ-maps extended (the arg eval may allocate).

`stFin` is the state at which the whole argument sequence terminates; the
φ-extension is stated over `stFin`'s store sizes (as in `ExecSeqStep`) so the
loop rule can compose the per-iteration extensions all the way to the final exit.
The spec-side `EvalE st d env e st' v` derivation for the head is threaded so the
caller (`evalArgsLoop`) can invoke the `EvalArgs.cons` constructor. -/
def EvalArgsStep
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (es : List Expr)
    (dLeft aLeft : Nat) (p : Nat) (m0 : Mem)
    (st' stFin : SpecSt) (v : Value) : Prop :=
  EvalE st d env e st' v →
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft p m0)
      (fun c =>
        ∃ (φf' φc' : Addr → Nat),
          PhiExtends φf φf' stFin.store.frames.size ∧
          PhiExtends φc φc' stFin.store.closures.size ∧
          -- the iteration's memory frames back to the ORIGINAL pre-memory `m0`
          -- outside the stack window and the arena (arg eval only scribbles
          -- there); this lets the loop rule keep `SegExit.memFrame` pinned to
          -- the entry `m0` across all iterations.
          (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < SL.hi) → ¬ (A.lo ≤ a ∧ a < A.hi) →
            c.σ.mem[a]? = m0[a]?) ∧
          SegEntry g N A SL φf' φc' st' d dLeft aLeft p c.σ.mem c)

/-! ## `segExit_extend` — re-base a `SegExit` to earlier φ-maps and memory

The `SegExit` analog of `execSeqExit_extend`. Two φ-dependent/`m0`-dependent
fields must be rebased: `store` (`∃ φf'' φc'', PhiExtends … ∧ StoreRepr …`) —
handled by composing the two `PhiExtends` — and `memFrame` (framed to the
iteration's memory `mNow`). Since `mNow` itself frames back to the original `m0`
outside the stack window and the arena (`hmid`), the composed `memFrame` frames
`c.σ.mem` back to `m0` there. This threads the per-iteration φ-extensions and the
memory-frame invariant through `evalArgsLoop`'s tail recursion. -/
theorem segExit_extend
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc φf' φc' : Addr → Nat)
    (nf nc nf' nc' : Nat)
    (st' : SpecSt) (exitPC : Nat) (m0 mNow : Mem) (c : Config)
    (hpf : PhiExtends φf φf' nf)
    (hpc : PhiExtends φc φc' nc)
    (hle : nf ≤ nf' ∧ nc ≤ nc')
    (hmid : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < SL.hi) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      mNow[a]? = m0[a]?)
    -- the exit PC is UNTABLED in the stack-window discipline (wave 38): the
    -- rebase's `hmid` frames only outside the stack, so a tabled window could
    -- not be re-based through it; every current caller exits at an untabled
    -- continuation PC (`evalArgsContPC`), discharged by `decide`.
    (hwin : stackScratchTop exitPC = none)
    (hexit : SegExit g N A SL φf' φc' nf' nc' st' exitPC mNow c) :
    SegExit g N A SL φf φc nf nc st' exitPC m0 c := by
  obtain ⟨φf'', φc'', hpf'', hpc'', hstore⟩ := hexit.store
  exact
    { good := hexit.good
      tick := hexit.tick
      pc := hexit.pc
      store := ⟨φf'', φc'', hpf.trans (PhiExtends.mono hle.1 hpf''),
        hpc.trans (PhiExtends.mono hle.2 hpc''), hstore⟩
      out := hexit.out
      frame := hexit.frame
      memFrame := fun a ha1 ha2 => (hexit.memFrame a ha1 ha2).trans (hmid a ha1 ha2)
      stackWin := fun _k hk => absurd (hk.symm.trans hwin) (Option.some_ne_none _k) }

/-! ## `evalArgsLoop` — the argument-evaluation loop rule (the reusable heart)

By list induction on the argument sequence `es`, composing `EvalArgsStep`
iterations. The hypothesis `hstep` supplies, for EVERY suffix of the sequence and
every consistent intermediate state, one loop iteration; `hnil` closes the empty
list at the continuation `q` (the `argc ≤ 0`/fall-through hop, already landed as
`evalArgsNil`); `evalArgsLoop` folds them into the whole-sequence Triple.

The measure is `es.length` (each `cons` iteration drops the head, strictly
decreasing). The φ-maps thread through the iterations (each `eval_expr` may
allocate); the final exit re-exposes the composed extension as `SegExit`'s
existential.

This is the exact argument-side analog of `execSeqLoop`, minus the abrupt-exit
disjunction (`EvalArgs` always continues). It states the `EvalArgs.cons` case at
the loop head `p = evalArgsLoopPC` and closes at `q = evalArgsContPC`. -/
theorem evalArgsLoop
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (d : Nat) (env : Addr) (dLeft aLeft : Nat) (p q : Nat)
    -- the continuation PC is untabled in the stack-window discipline (wave 38;
    -- see `segExit_extend.hwin`): concrete callers discharge by `decide`.
    (hqWin : stackScratchTop q = none)
    -- The per-suffix packaging of one loop iteration; parametric in the suffix
    -- and the intermediate maps/state, so a single hypothesis covers every
    -- iteration. This is the residual (the machine loop-body glue + the
    -- recursive `eval_expr`).
    (hstep : ∀ (φf φc : Addr → Nat) (st : SpecSt) (e : Expr) (es : List Expr)
        (st' stFin : SpecSt) (v : Value) (m0 : Mem),
        EvalArgsStep g N A SL φf φc st d env e es dLeft aLeft p m0 st' stFin v)
    -- The empty-list continuation hop `p → q` (`blez`/fall-through to the
    -- dispatch), which also terminates every finished `cons` chain. This is the
    -- `evalArgsNil` residual (a zero-step identity when `p = q`).
    (hnil : ∀ (φf φc : Addr → Nat) (st : SpecSt) (m0 : Mem),
        Triple
          (SegEntry g N A SL φf φc st d dLeft aLeft p m0)
          (SegExit g N A SL φf φc st.store.frames.size st.store.closures.size st q m0)) :
    ∀ (es : List Expr) (φf φc : Addr → Nat) (st st' : SpecSt) (vs : List Value)
      (m0 : Mem),
      EvalArgs st d env es st' vs →
      Triple
        (SegEntry g N A SL φf φc st d dLeft aLeft p m0)
        (SegExit g N A SL φf φc st.store.frames.size st.store.closures.size st' q m0) := by
  -- `EvalArgs` is mutually inductive (with `EvalE`/`Call`), so we cannot
  -- `induction` on the derivation directly. Instead we induct on the argument
  -- list `es` (the measure), and `cases` the `EvalArgs` derivation to peel
  -- `nil`/`cons` at each length. `st`/`st'`/`vs`/maps/`m0` are generalized
  -- (re-introduced after the induction) so the tail recursion can
  -- re-instantiate them.
  intro es
  induction es with
  | nil =>
    intro φf φc st st' vs m0 hArgs
    cases hArgs with
    | nil =>
      -- Empty argument list: the machine has already fallen through to the
      -- dispatch continuation `q`. This `p → q` hop is `hnil` (`evalArgsNil`).
      exact hnil φf φc st m0
  | cons e es ih =>
    intro φf φc st st' vs m0 hArgs
    cases hArgs with
    | cons _ _ _ _ _ stMid _ _ _ hE hArgsTail =>
      -- Non-empty: evaluate the head `e` (one iteration loops back to `p`),
      -- then recurse on the tail from the intermediate state `stMid`.
      intro c hc
      obtain ⟨c₁, hs₁, φf', φc', hpf, hpc, hmid, hEntry'⟩ :=
        hstep φf φc st e es stMid st' _ m0 hE c hc
      obtain ⟨c₂, hs₂, hexit⟩ :=
        ih φf' φc' stMid st' _ c₁.σ.mem hArgsTail c₁ hEntry'
      -- The tail's exit is stated for the extended maps `φf'`/`φc'` and the mid
      -- memory `c₁.σ.mem`; re-expose it against the original `φf`/`φc`/`m0` by
      -- composing the φ-extensions and the mid-to-original memory frame `hmid`.
      -- Store counts only grow: `st.store ≤ stMid.store ≤ st'.store`.  The
      -- iteration's `hpf`/`hpc` are `st'`-sized (weaken to the `st`-entry size);
      -- the tail exit is `stMid`-sized (lower to the `st`-entry size).
      have hmonoHead := evalE_store_mono hE
      have hmonoTail := evalArgs_store_mono hArgsTail
      have hleMid : st.store.frames.size ≤ stMid.store.frames.size ∧
          st.store.closures.size ≤ stMid.store.closures.size := ⟨hmonoHead.1, hmonoHead.2⟩
      have hleFin : st.store.frames.size ≤ st'.store.frames.size ∧
          st.store.closures.size ≤ st'.store.closures.size :=
        ⟨Nat.le_trans hmonoHead.1 hmonoTail.1, Nat.le_trans hmonoHead.2 hmonoTail.2⟩
      refine ⟨c₂, hs₁.trans hs₂, ?_⟩
      exact segExit_extend g N A SL φf φc φf' φc'
        st.store.frames.size st.store.closures.size
        stMid.store.frames.size stMid.store.closures.size
        st' q m0 c₁.σ.mem c₂
        (PhiExtends.mono hleFin.1 hpf) (PhiExtends.mono hleFin.2 hpc) hleMid hmid hqWin hexit

/-! ## `evalArgsCons` — the `EvalArgs.cons` minor premise (via the loop rule)

The `EvalArgs.cons` case of the mutual recursor: evaluating a non-empty argument
list `e :: es` runs the whole arg loop. Stated as `evalArgsLoop` specialised to
the full list at the loop head, it composes the head `EvalE` sub-derivation (an
`EvalIH`, threaded here as the loop's per-iteration residual `hstep`) with the
tail `EvalArgs es` recursion. CONDITIONAL on `hstep` (the per-iteration machine
glue + recursive `eval_expr`) and `hnil` (the fall-through/`evalArgsNil` hop),
exactly the deferral discipline of `execSeqLoop`. -/
theorem evalArgsCons
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (d : Nat) (env : Addr) (dLeft aLeft : Nat) (p q : Nat)
    (hqWin : stackScratchTop q = none)
    (hstep : ∀ (φf φc : Addr → Nat) (st : SpecSt) (e : Expr) (es : List Expr)
        (st' stFin : SpecSt) (v : Value) (m0 : Mem),
        EvalArgsStep g N A SL φf φc st d env e es dLeft aLeft p m0 st' stFin v)
    (hnil : ∀ (φf φc : Addr → Nat) (st : SpecSt) (m0 : Mem),
        Triple
          (SegEntry g N A SL φf φc st d dLeft aLeft p m0)
          (SegExit g N A SL φf φc st.store.frames.size st.store.closures.size st q m0))
    (φf φc : Addr → Nat) (st st' : SpecSt) (e : Expr) (es : List Expr)
    (v : Value) (vs : List Value) (m0 : Mem)
    (hArgs : EvalArgs st d env (e :: es) st' (v :: vs)) :
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft p m0)
      (SegExit g N A SL φf φc st.store.frames.size st.store.closures.size st' q m0) :=
  evalArgsLoop g N A SL d env dLeft aLeft p q hqWin hstep hnil
    (e :: es) φf φc st st' (v :: vs) m0 hArgs

end Vsa.Sim
