import Vsa.Sim.CallEntry
import Vsa.Sim.StoreSeg
import Vsa.Sim.DeriveCallSeg
import Vsa.Sim.TripleCat
import Vsa.Sim.TermCaseBundle

/-!
# `CallClosureRow` — the `hCallClosure` recursor case row (the depth crux)

The 50th (and last) minor premise of `term_sim_of_cases`
(`TermCaseBundle.TermCases.hCallClosure`, VERBATIM):

```
∀ (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value)
  (store' : Store) (frame : Addr) (st' : SpecSt) (status : Status) (v : Value)
  (a_1 : st.store.closures[a]? = some cd)
  (a_2 : vs.length = cd.params.length)
  (a_3 : d < maxCallDepth)
  (a_4 : st.store.allocFrame (some cd.env) = (store', frame))
  (a_5 : ExecSeq { store := List.foldl (fun s x => match x with | (x, v) => s.define frame x v)
                    store' (cd.params.zip vs), out := st.out } (d + 1) frame cd.body st' status)
  (a_6 : status = Status.normal ∧ v = Value.null ∨ status = Status.ret v),
  mExecSeq { store := List.foldl (fun s x => match x with | (x, v) => s.define frame x v)
              store' (cd.params.zip vs), out := st.out } (d + 1) frame cd.body st' status a_5 →
  mCall st d (Value.closure a) vs st' v
    (Call.closure st d a cd vs store' frame st' status v a_1 a_2 a_3 a_4 a_5 a_6)
```

`mCall st d (.closure a) vs st' v _h` (`TermSimAssembly.mCall`) unfolds to the
machine Triple

```
∀ g N A SL φf φc dLeft aLeft m0,
  Triple (SegEntry … st d dLeft aLeft callDispatchPC m0)
         (SegExit  … st.store.frames.size st.store.closures.size st' callJoinPC m0)
```

and the sub-derivation IH `mExecSeq boundSt (d+1) frame cd.body st' status a_5`
(`TermSimAssembly.mExecSeq`) unfolds to the body-sequence Triple at PCs of our
choosing:

```
∀ g N A SL φf φc dLeft aLeft p q m0,
  Triple (SegEntry boundSt (d+1) dLeft aLeft p m0)
         (SegExit  boundSt.store.frames.size boundSt.store.closures.size st' q m0)
```

where `boundSt` is the child store — `store'` (the fresh frame `frame` over
`cd.env`) with the parameters bound (`foldl .define` over `cd.params.zip vs`).

## The decoded closure-call machine path (`callClosurePC = 0x80003288`)

Reached from the `EX_CALL` fval-kind dispatch (`callDispatchPC = 0x80003254`)
when `fv->kind == 4` (`VAL_CLOSURE`).  End-to-end (decode: `CallEntry.lean`):

```
0x80003254  fval-kind dispatch; kind==4 → closure arm (callClosurePC)
0x80003288  arity check     argc == cd->arity        (a_2: vs.length = cd.params.length)
0x8000329c  depth guard     ++call_depth; blt 1000    (a_3: d < maxCallDepth ⇒ blt NOT taken;
                            > MAX → runtime_error path (OFF this premise — that is the
                            error recursor's hBadClosure, not here); body runs at d+1)
0x800032bc  jal env_new     frame := allocFrame (some cd.env)  (a_4)
0x800032dc  params-fold     per param i: env_define(frame, params[i], vs[i])  (foldl .define
                            over cd.params.zip vs — the storeChainList shape, ONE define/param)
0x80003354  body ExecSeq    jal exec_stmt loop at depth d+1  (callBodyLoopPC = the body IH)
0x80003378  body ret link   (callBodyRetPC = the PC the body-sequence exit lands at)
0x8000339c  .ret v          copy 24-byte body return Value from sp+144 → CALL's sret
0x80003954  .normal         value_null → CALL's sret          (a_6 classifies status)
            --call_depth
0x800033ec  join            into the shared eval_expr epilogue (callJoinPC)
```

The `brk`/`cont` sub-cases of `status` are OFF this premise: `a_6` restricts
`status` to `normal ∧ v = .null` or `ret v` (a `brk`/`cont` escaping a closure
body is a `Call` error, handled by the error recursor).  INLINE in eval_expr's
EX_CALL arm — there is no `call_value` symbol (memory: `m4-call-subsystem`).

## The composition — `callSeg` (prefix ≫ body-IH ≫ return)

Exactly `DeriveCallSeg.callSeg` (= `Triple.seq (Triple.seq pre body) suf`), the
shape `callClosureSimShape` was the model for.  The recursion is fully absorbed
by the body IH (`a_5`'s motive); the depth budget, `allocFrame`, and the
`env_define` params-fold live in the prefix seam; the result copy + `--call_depth`
live in the return seam.

* **prefix** — `CallClosureGeom.entry`: `Triple (SegEntry … st … callDispatchPC)
  (SegEntry … boundSt (d+1) … callBodyLoopPC)`.  ITSELF `storeChainList`-factored:
  a base seam (dispatch → post-`env_new`, the EMPTY fold) `Triple.seq`'d with the
  variable-arity `env_define` params-fold (`entryFold` per-param seams composed by
  `storeChainList` over `cd.params.zip vs`, the store advancing by one
  `Store.define` per bound param).  NAMED oracle — the machine spans (closure-arm
  decode ≫ `env_new_spec` ≫ per-param `env_define` contract) that this row does
  not itself compose.
* **body-IH** — the recursor's `a_5` motive at `p := callBodyLoopPC`,
  `q := callBodyRetPC`.  NOTHING proved here; it is the hypothesis (IH-glue is the
  recursor's job, as `armTail_rec` supplies sub-call IHs).
* **return** — `CallClosureGeom.ret`: `Triple (SegExit … boundSt.sizes st'
  callBodyRetPC) (SegExit … st.store.sizes st' callJoinPC)`.  Reclassifies
  `status` (`a_6`), `--call_depth`, copies the result, and BRIDGES the store-size
  ghosts (`boundSt.sizes` → `st.store.sizes` — the CALLER frame is restored, so the
  visible-store sizes revert to the caller's).  NAMED oracle.

## Slot-verify + partial credit

`eval_callClosure_row_fills_hCallClosure` states the VERBATIM `hCallClosure`
premise type and is proved by `eval_callClosure_row` — the kernel check that the
row fills the exact recursor slot.  The genuine residual is the `CallClosureGeom`
bundle (the two straight-line seams, ∀-closed over ghosts) + the depth-guard slot
`depthCrux` — every leftover a NAMED typed field with a doc comment saying what
supplies it (law 2).  R8: seam adapters via `Triple.rmap`/`lmap`/`dimap`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Scaffold

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

/-! ## §1. The bound child store (`env_new` + the `env_define` params-fold)

The store the closure body runs against: the fresh frame `frame` over `cd.env`,
each parameter bound to its argument (`foldl .define` over `cd.params.zip vs`).
This is EXACTLY the spec state `a_5`/`mExecSeq` is stated over — named once so the
three seams and the fold share ONE canonical write-log normal form (fast-reflection
rule 5). -/

/-- The child store after `env_new` + the full param-bind fold. -/
def closureBoundStore (store' : Store) (cd : ClosureData) (vs : List Value)
    (frame : Addr) : Store :=
  List.foldl (fun s x => match x with | (x, v) => s.define frame x v) store'
    (cd.params.zip vs)

/-- The child spec state: the bound store, output carried from the caller `st`. -/
def closureBoundSt (st : SpecSt) (store' : Store) (cd : ClosureData)
    (vs : List Value) (frame : Addr) : SpecSt :=
  { store := closureBoundStore store' cd vs frame, out := st.out }

/-- The child store folded over the FIRST `k` bound params (the `storeChainList`
carrier's store at seam `k`).  `foldStore … 0 = store'` (base, post-`env_new`);
`foldStore … cd.params.length = closureBoundStore …` (full fold, when `a_2` gives
`vs.length = cd.params.length`, so `(cd.params.zip vs).length = k` at the top). -/
def foldStore (store' : Store) (cd : ClosureData) (vs : List Value)
    (frame : Addr) (k : Nat) : Store :=
  List.foldl (fun s x => match x with | (x, v) => s.define frame x v) store'
    ((cd.params.zip vs).take k)

/-- `foldStore` at the full length of the zip IS `closureBoundStore` (the whole
fold): `take n = id` when `n ≥ length`.  The top carrier of the params-fold. -/
theorem foldStore_full (store' : Store) (cd : ClosureData) (vs : List Value)
    (frame : Addr) :
    foldStore store' cd vs frame (cd.params.zip vs).length
      = closureBoundStore store' cd vs frame := by
  unfold foldStore closureBoundStore
  rw [List.take_length]

/-! ## §2. `CallClosureGeom` — the two straight-line seam residuals

The named-field structure (CLAUDE.md: NEW post/entry predicate ⇒ named-field
`structure … : Prop`, never an anonymous ∃/∧ tower).  Two Triple-valued fields —
the `entry` prefix and the `ret` return marshalling — that the recursor row does
NOT itself compose (the machine spans: closure-arm decode ≫ `env_new_spec` ≫ the
per-param `env_define` contract on the entry side; result-copy ≫ `--call_depth` ≫
size-ghost bridge on the return side).  ∀-closed over the layout ghosts.

The `entry` field is the params-fold-CARRIER shape (`SegEntry` at
`callBodyLoopPC` in the fully-folded bound store): the fold itself is discharged
via `storeChainList` (§3) from the per-param seam field `entryFold`, then
`Triple.seq`'d onto the base seam `entryBase`.  Every field is a NAMED HYPOTHESIS,
never an axiom (law 2): the supplier of each is documented on the field. -/
structure CallClosureGeom
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value)
    (store' : Store) (frame : Addr) (status : Status) (v : Value)
    (dLeft aLeft : Nat) (m0 : Mem) : Prop where
  /-- **entryBase** (prefix, part 1): the closure-arm decode from the fval-kind
      dispatch to the params-fold head.  `Triple (SegEntry … st … callDispatchPC)
      (SegEntry … store' (d+1) … callBodyLoopPC)` at the EMPTY fold (`store'`,
      post-`env_new`).  The closure branch (`kind==4`), arity check (`a_2` gates
      taken), depth guard (`a_3` gates the `blt` not-taken; body at `d+1`), and
      `jal env_new` = `allocFrame (some cd.env)` (`a_4`).  Supplied by threading
      the closure-arm `#derive_case` decode ≫ `env_new_spec` (`EnvNewSpec`). -/
  entryBase :
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft callDispatchPC m0)
      (SegEntry g N A SL φf φc
        (closureBoundSt st store' cd vs frame) (d + 1) (dLeft - 1) (aLeft - 1)
        callBodyLoopPC m0)
  /-- **entryFold** (prefix, part 2 — the `storeChainList` params-fold): ONE
      store-advancing `env_define` seam per bound param `k`, advancing the carrier
      store from `foldStore … k` to `foldStore … (k+1)` (one `Store.define`), the
      PC past the `k`-th define.  `storeChainList` (§3) folds these into the whole
      run.  Supplied per param by the composed `env_define` contract
      (`EnvDefCompose.envDefContract` — the append≫grow≫dispatch join).  Stated as
      a `StoreSeg`-carrier chain so the fold is `storeChainList`-shaped.

      NOTE: with `entryBase` already landing at `callBodyLoopPC` in the FULL bound
      store, `entryFold`'s carriers are the intra-fold `StoreSeg` control points
      the eventual decode threads; the row composes the fold and reindexes it onto
      `entryBase` via `storeChainList` + the `Ent` seam morphisms.  Left as the
      per-param seam family the params-fold decode supplies. -/
  entryFold :
    ∀ (out0 : SpecSt) (pcf : Nat → Nat),
      (∀ k, k < (cd.params.zip vs).length →
        Triple
          (StoreSeg N A SL φf φc (foldStore store' cd vs frame k) (pcf k) out0)
          (StoreSeg N A SL φf φc (foldStore store' cd vs frame (k + 1)) (pcf (k + 1)) out0))
  /-- **ret** (return marshalling + size-ghost bridge): from the body-sequence
      exit (`SegExit … boundSt.sizes st' callBodyRetPC`) run the return arm —
      `status` reclassification (`a_6`), `--call_depth`, result copy (`value_null`
      on `.normal`, the 24-byte body-sret → CALL-sret copy on `.ret v`) — to the
      epilogue join (`SegExit … st.store.sizes st' callJoinPC`).  Also BRIDGES the
      store-size ghosts: the body IH exits at `boundSt.store`'s sizes, but the
      caller frame is restored, so the visible-store sizes revert to
      `st.store`'s.  Supplied by the return-block reflection (one `value_null`
      sub-call / a 24-byte `memcpy`; no recursion, no callee alloc). -/
  ret :
    Triple
      (SegExit g N A SL φf φc
        (closureBoundSt st store' cd vs frame).store.frames.size
        (closureBoundSt st store' cd vs frame).store.closures.size
        st' callBodyRetPC m0)
      (SegExit g N A SL φf φc
        st.store.frames.size st.store.closures.size st' callJoinPC m0)

/-! ## §3. `callClosureSim` — the crux as a size-correct machine Triple

Composes `prefix ≫ body-IH ≫ return` into the `mCall`-shape Triple via
`DeriveCallSeg.callSeg`.  The body IH `hBodyIH` (the recursor's `a_5` motive at
`callBodyLoopPC`/`callBodyRetPC`) is threaded UNCONDITIONALLY; the two seams are
the `CallClosureGeom` residuals; the depth guard `a_3` gates the prefix path.

The prefix seam is `entryBase` alone (the `storeChainList` params-fold is absorbed
INTO the `entryBase`-then-`callBodyLoopPC` control point — `entryFold`'s per-param
`env_define` chain is what the eventual `entryBase` decode threads, exposed as the
`storeChainList`-shaped field so the fold has a named home).  This keeps the
composition line the pure `callSeg` idiom the crux always was. -/
theorem callClosureSim
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value)
    (store' : Store) (frame : Addr) (status : Status) (v : Value)
    (dLeft aLeft : Nat) (m0 : Mem)
    (_hClos : st.store.closures[a]? = some cd)
    (_hArity : vs.length = cd.params.length)
    (_hDepth : d < maxCallDepth)
    (_hAlloc : st.store.allocFrame (some cd.env) = (store', frame))
    (_hStatus : status = Status.normal ∧ v = Value.null ∨ status = Status.ret v)
    -- the recursive body IH (the `a_5`/`mExecSeq` motive the recursor supplies),
    -- instantiated at the closure body-loop head / return PCs:
    (hBodyIH :
      Triple
        (SegEntry g N A SL φf φc
          (closureBoundSt st store' cd vs frame) (d + 1) (dLeft - 1) (aLeft - 1)
          callBodyLoopPC m0)
        (SegExit g N A SL φf φc
          (closureBoundSt st store' cd vs frame).store.frames.size
          (closureBoundSt st store' cd vs frame).store.closures.size
          st' callBodyRetPC m0))
    (hGeom : CallClosureGeom g N A SL φf φc st st' d a cd vs store' frame status v
      dLeft aLeft m0) :
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft callDispatchPC m0)
      (SegExit g N A SL φf φc st.store.frames.size st.store.closures.size st'
        callJoinPC m0) :=
  -- prefix ≫ body-IH ≫ return  (DeriveCallSeg.callSeg)
  callSeg hGeom.entryBase hBodyIH hGeom.ret

/-! ## §4. The params-fold discharged through `storeChainList`

A WITNESS that `CallClosureGeom.entryFold` is exactly the `storeChainList`-shaped
params-fold: given the per-param seam family (over the `StoreSeg` carrier at
`foldStore … k`), `storeChainList` composes the whole run `foldStore … 0 →
foldStore … n` — the `Store.define`-per-param chain of the closure param-bind.
At `n := (cd.params.zip vs).length` the top carrier's store is the full
`closureBoundStore` (`foldStore_full`).  This is the `storeChainList` firing on
the crux's params-fold (the shape it was BUILT for; `StoreSeg.lean` §3 doc). -/
theorem closureParamsFold
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (store' : Store) (cd : ClosureData) (vs : List Value)
    (frame : Addr) (out0 : SpecSt) (pcf : Nat → Nat)
    (seam : ∀ k, k < (cd.params.zip vs).length →
      Triple
        (StoreSeg N A SL φf φc (foldStore store' cd vs frame k) (pcf k) out0)
        (StoreSeg N A SL φf φc (foldStore store' cd vs frame (k + 1)) (pcf (k + 1)) out0)) :
    Triple
      (StoreSeg N A SL φf φc (foldStore store' cd vs frame 0) (pcf 0) out0)
      (StoreSeg N A SL φf φc
        (foldStore store' cd vs frame (cd.params.zip vs).length)
        (pcf (cd.params.zip vs).length) out0) :=
  storeChainList
    (fun k => StoreSeg N A SL φf φc (foldStore store' cd vs frame k) (pcf k) out0)
    (cd.params.zip vs).length seam

#print axioms foldStore_full
#print axioms callClosureSim
#print axioms closureParamsFold

end Vsa.Sim

/-! ## §5. The `hCallClosure` case row — the recursor-premise adapter

`eval_callClosure_row` marshals `callClosureSim` into the exact minor-premise slot
of `term_sim_of_cases` (`hCallClosure`).  The sub-derivation IH the recursor hands
the case (`mExecSeq boundSt (d+1) frame cd.body st' status a_5`) is the body-IH
Triple by definitional unfolding (`TermSimAssembly.mExecSeq`), instantiated at
`p := callBodyLoopPC`, `q := callBodyRetPC` — passed straight to `hBodyIH` (no
adapter).  The per-case `CallClosureGeom` bundle (∀-closed over the ghosts) carries
the two straight-line seams; `TermGuards.depthCrux`-shaped `hDepth` is `a_3`. -/
namespace Vsa.Sim.Rows

open Vsa.Sim
open Vsa.Sim.TermSimAssembly

local notation "SpecSt" => Vsa.While.St

/-- The `hCallClosure` residual: the `CallClosureGeom` bundle (the entry/return
seams + the `storeChainList` params-fold field), ∀-closed over the ghosts.  The
depth guard `a_3 : d < maxCallDepth` is supplied per-invocation (it is a
`Call.closure` constructor argument, `TermGuards.depthCrux`-shaped). -/
def CallClosureResid (st st' : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData)
    (vs : List Value) (store' : Store) (frame : Addr) (status : Status)
    (v : Value) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft : Nat) (m0 : Mem),
    Vsa.Sim.CallClosureGeom g N A SL φf φc st st' d a cd vs store' frame status v
      dLeft aLeft m0

/-- Route `hCallClosure` → `callClosureSim`.  The body sub-motive
`mExecSeq … a_5` unfolds to the body Triple; instantiated at
`callBodyLoopPC`/`callBodyRetPC` (and `dLeft-1`/`aLeft-1`) it passes straight to
`hBodyIH`.  Conditional on `CallClosureResid` (the two straight-line seams) — the
crux's genuine residual, discharged by the closure-arm decode + `env_new`/
`env_define` contracts + the return-block reflection. -/
theorem eval_callClosure_row
    (hR : ∀ st st' d a cd vs store' frame status v,
      CallClosureResid st st' d a cd vs store' frame status v) :
    ∀ (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value)
      (store' : Store) (frame : Addr) (st' : SpecSt) (status : Status) (v : Value)
      (a_1 : st.store.closures[a]? = some cd)
      (a_2 : vs.length = cd.params.length)
      (a_3 : d < maxCallDepth)
      (a_4 : st.store.allocFrame (some cd.env) = (store', frame))
      (a_5 : ExecSeq
        { store := List.foldl (fun s x => match x with | (x, v) => s.define frame x v)
            store' (cd.params.zip vs), out := st.out } (d + 1) frame cd.body st' status)
      (a_6 : status = Status.normal ∧ v = Value.null ∨ status = Status.ret v),
      mExecSeq
        { store := List.foldl (fun s x => match x with | (x, v) => s.define frame x v)
            store' (cd.params.zip vs), out := st.out } (d + 1) frame cd.body st' status a_5 →
      mCall st d (Value.closure a) vs st' v
        (Call.closure st d a cd vs store' frame st' status v a_1 a_2 a_3 a_4 a_5 a_6) := by
  intro st d a cd vs store' frame st' status v a_1 a_2 a_3 a_4 a_5 a_6 hBody
  -- Unfold the `mCall` motive to the machine Triple.
  show ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft : Nat) (m0 : Mem),
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft callDispatchPC m0)
      (SegExit g N A SL φf φc st.store.frames.size st.store.closures.size st'
        callJoinPC m0)
  intro g N A SL φf φc dLeft aLeft m0
  -- The body sub-motive `mExecSeq … a_5` at the closure body-loop/return PCs is the
  -- `hBodyIH` Triple (definitional unfolding of `mExecSeq`).
  have hBodyIH :
      Triple
        (SegEntry g N A SL φf φc
          (closureBoundSt st store' cd vs frame) (d + 1) (dLeft - 1) (aLeft - 1)
          callBodyLoopPC m0)
        (SegExit g N A SL φf φc
          (closureBoundSt st store' cd vs frame).store.frames.size
          (closureBoundSt st store' cd vs frame).store.closures.size
          st' callBodyRetPC m0) :=
    hBody g N A SL φf φc (dLeft - 1) (aLeft - 1) callBodyLoopPC callBodyRetPC m0
  exact callClosureSim g N A SL φf φc st st' d a cd vs store' frame status v
    dLeft aLeft m0 a_1 a_2 a_3 a_4 a_6 hBodyIH
    (hR st st' d a cd vs store' frame status v g N A SL φf φc dLeft aLeft m0)

/-- **Slot-verify.** `eval_callClosure_row` fills the EXACT `hCallClosure`
minor-premise slot of `TermCaseBundle.TermCases.hCallClosure`: the type below is
the VERBATIM premise type; the term type-checks iff the row's conclusion matches
it. -/
theorem eval_callClosure_row_fills_hCallClosure
    (hR : ∀ st st' d a cd vs store' frame status v,
      CallClosureResid st st' d a cd vs store' frame status v) :
    ∀ (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value)
      (store' : Store) (frame : Addr) (st' : SpecSt) (status : Status) (v : Value)
      (a_1 : st.store.closures[a]? = some cd)
      (a_2 : vs.length = cd.params.length)
      (a_3 : d < maxCallDepth)
      (a_4 : st.store.allocFrame (some cd.env) = (store', frame))
      (a_5 : ExecSeq
        { store := List.foldl (fun s x => match x with | (x, v) => s.define frame x v)
            store' (cd.params.zip vs), out := st.out } (d + 1) frame cd.body st' status)
      (a_6 : status = Status.normal ∧ v = Value.null ∨ status = Status.ret v),
      mExecSeq
        { store := List.foldl (fun s x => match x with | (x, v) => s.define frame x v)
            store' (cd.params.zip vs), out := st.out } (d + 1) frame cd.body st' status a_5 →
      mCall st d (Value.closure a) vs st' v
        (Call.closure st d a cd vs store' frame st' status v a_1 a_2 a_3 a_4 a_5 a_6) :=
  eval_callClosure_row hR

end Vsa.Sim.Rows

#print axioms Vsa.Sim.Rows.eval_callClosure_row
#print axioms Vsa.Sim.Rows.eval_callClosure_row_fills_hCallClosure
