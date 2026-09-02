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

/-! ## §2. `CallClosureGeom` — the straight-line seam residuals

The named-field structure (CLAUDE.md: NEW post/entry predicate ⇒ named-field
`structure … : Prop`, never an anonymous ∃/∧ tower).  Triple-valued fields —
the `entry` prefix, the `ret` return marshalling, and the empty-body bypass —
that the recursor row does NOT itself compose (the machine spans: closure-arm
decode ≫ `env_new_spec` ≫ the per-param `env_define` contract on the entry side;
result-copy ≫ `--call_depth` ≫ size-ghost bridge on the return side).  ∀-closed
over the layout ghosts.

**AMENDED (wave 37, ledger `callclosuregeom-entrybase-unsatisfiable`).**  The
original `entryBase` post was `SegEntry … boundSt (d+1) … callBodyLoopPC m0`
over the CALLER's `φf` and the ENTRY memory `m0` — unsatisfiable three ways:
(1) `SegEntry.mem` pinned the body-loop-head memory EQUAL to the dispatch-entry
`m0`, but the route allocates (`env_new`'s fresh Env + malloc metadata, the
`env_define` fold) and spills (`s5`/`s3` at `1032/1048(sp)`); (2) the caller's
`φf` was reused unextended while `CallClosureResid` ∀-quantifies it — the fresh
frame's machine address cannot equal `φf(frame)` for EVERY `φf`; the address
must come from an ∃-bound `PhiExtends` extension (exactly as `SegExit.store`
already does); (3) for `cd.body = []` the machine (`bgtz a5 @0x80003338` not
taken ▷ `j 0x80003954`) NEVER visits `callBodyLoopPC`/`callBodyRetPC`, so the
prefix≫IH≫suffix decomposition through those PCs has no run on the empty-body
route.  A fourth instance of the same class: the route clobbers callee-saved
`s0/s3/s5/s6/s7` before the body-loop head (spilled at `1016..1048(sp)`), so
the arm's register ghost `g` cannot tie the body entry either — the handoff
must carry the body's OWN ghost.  The amendment: the `BodyHandoff` mid ∃-binds
`(g', φf', mB)` with a stack/arena memory frame back to `m0`; `entryBase`/`ret`
are guarded `cd.body ≠ []` and `ret` is ∀-quantified over the handoff triple;
the `[]` route gets its own `emptyBypass` field.  REGRESSION GUARD: any Geom
field that reuses an entry-pinned predicate (`SegEntry` at the same
`m0`/caller-`φ`/caller-`g`) as an intermediate POST of an allocating,
callee-saved-clobbering route is wrong on arrival. -/

/-- **The body ghost tie** (wave 38): the registers the RETURN routes read that
must agree between the arm's ghost `g` and the body's own ghost `g'` — the
shared eval-frame `sp` (`x2`, anchors the spill slots and the `stackWin`
window), the CALL's sret pointer `s1 = x9` (the `.ret` copy destination), and
the interp pointer `s2 = x18` (`--call_depth` at `8(s2)`).  All three are
`AbiPreservedNoise`, never written between the dispatch entry and the body-loop
head, so the entry-route discharger proves each by chaining its frame facts. -/
structure BodyGhostTie
    (g g' : (R : Register) → Option (RegisterType R)) : Prop where
  sp : g' Register.x2 = g Register.x2
  sret : g' Register.x9 = g Register.x9
  interp : g' Register.x18 = g Register.x18

/-- **The caller spill slots at the body-loop head** (wave 38): what the entry
route knows about the handoff memory `mB` at the eval-frame slots the return
routes restore from.  `s5@1032(sp)`/`s3@1048(sp)` were spilled INSIDE the
dispatch span (`0x8000328c`/`0x800032ac`) — their bytes are the arm ghost's
values; the `s7@1016(sp)` slot predates the span (`0x800031cc`, the arg-loop
entry), so only its m0-CARRY is stated here (its g-image is the ledgered
`segentry-no-caller-spill-image` entry-side gap).  Byte-level, LE — the ret
discharger reassembles through its seg readback. -/
structure CallerSpillSlots
    (g : (R : Register) → Option (RegisterType R)) (spv : BitVec 64)
    (mB m0 : Mem) : Prop where
  /-- `1032..1039(sp)` holds the arm's `s5 = g x21` (LE bytes). -/
  s5 : ∀ w : BitVec 64, g Register.x21 = some w →
    ∀ i : Nat, i < 8 → mB[spv.toNat + 1032 + i]? = some (w.extractLsb' (8 * i) 8)
  /-- `1048..1055(sp)` holds the arm's `s3 = g x19` (LE bytes). -/
  s3 : ∀ w : BitVec 64, g Register.x19 = some w →
    ∀ i : Nat, i < 8 → mB[spv.toNat + 1048 + i]? = some (w.extractLsb' (8 * i) 8)
  /-- `1016..1023(sp)` is UNTOUCHED by the entry route (the `s7` slot's content
  is `m0`'s — see ledger `segentry-no-caller-spill-image` for the g-image). -/
  s7carry : ∀ i : Nat, i < 8 → mB[spv.toNat + 1016 + i]? = m0[spv.toNat + 1016 + i]?

-- discipline: allow(R7-conj-tower-def) `BodyHandoff` is a reached-Config
-- landing bundle carrying DATA binders (φf', mB) — the sanctioned
-- `def : Prop := ∃ …` shape (Prop structures cannot carry data fields, cf. the
-- WidenMeta gotcha); consumers destructure it exactly once, in `callClosureSim`.
/-- **The body-entry handoff** — the mid-predicate between the closure-arm entry
route and the body IH: the config is parked at `callBodyLoopPC` carrying the
bound child store at depth `d + 1` under the BODY's OWN register ghost `g'`
(the route clobbers `s0`/`s3`/`s5`/`s6`/`s7` — spilled at `1016..1048(sp)` —
so the arm's `g` cannot tie the body entry; `mExecSeq` is universal in the
ghost), an EXTENDED frame map `φf'` (`PhiExtends` over the caller's live
frames), and the ACTUAL mid-memory `mB`, whose writes are confined to the stack
window and the arena (the frame clause back to the dispatch-entry `m0`).  The
∃-bound triple is what the recursor's `mExecSeq` motive (universal in
`g`/`φf`/`m0`) is instantiated at. -/
def BodyHandoff
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (store' : Store) (cd : ClosureData) (vs : List Value)
    (frame : Addr) (d dLeft aLeft : Nat) (m0 : Mem) (c : Config) : Prop :=
  ∃ (g' : (R : Register) → Option (RegisterType R)) (φf' : Addr → Nat) (mB : Mem),
    PhiExtends φf φf' st.store.frames.size ∧
    (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < SL.hi) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      mB[a]? = m0[a]?) ∧
    BodyGhostTie g g' ∧
    (∀ spv : BitVec 64, g Register.x2 = some spv →
      CallerSpillSlots g spv mB m0) ∧
    -- ITEM ZERO (falsity #12, shape 3): the entry route also certifies the
    -- `eval_expr` image in the mid-memory `mB` — the `SeqSpanGround` feed for
    -- the guarded `mExecSeq` body IH at `(callBodyLoopPC, callBodyRetPC)`.
    Vsa.Sim.Code.Eval_exprLoaded mB ∧
    SegEntry g' N A SL φf' φc
      (closureBoundSt st store' cd vs frame) (d + 1) (dLeft - 1) (aLeft - 1)
      callBodyLoopPC mB c

structure CallClosureGeom
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value)
    (store' : Store) (frame : Addr) (status : Status) (v : Value)
    (dLeft aLeft : Nat) (m0 : Mem) : Prop where
  /-- **entryBase** (prefix): the closure-arm route from the fval-kind dispatch
      to the body-loop head — `Triple (SegEntry … st … callDispatchPC m0)
      (BodyHandoff …)`, landing the FULLY BOUND child store at `d + 1` under the
      ∃-bound extended map `φf'` and mid-memory `mB` (stack/arena-framed to
      `m0`).  The closure branch (`kind==4`), arity check (`a_2` gates taken),
      depth guard (`a_3` gates the `blt` not-taken; body at `d+1`),
      `jal env_new` = `allocFrame (some cd.env)` (`a_4`), the `env_define`
      params-fold, `value_null` into the body-return buffer, and the body-entry
      staging (`bgtz` taken — hence the `cd.body ≠ []` guard; the `[]` route is
      `emptyBypass`).  Supplied by the splice composition
      (`rows/CallClosureSplice.lean`): dispatch/head decode ≫ `env_new_spec`
      (`EnvNewSpec`) ≫ the `storeChainList` params-fold over the `env_define`
      contract ≫ `value_null` ≫ body-entry staging. -/
  entryBase :
    cd.body ≠ [] →
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft callDispatchPC m0)
      (BodyHandoff g N A SL φf φc st store' cd vs frame d dLeft aLeft m0)
  -- (The former `entryFold` field — a per-param `StoreSeg` seam family over an
  -- ARBITRARY `pcf : Nat → Nat` — was DELETED in the wave-37 amendment: the
  -- ∀-pcf quantification was the independent-PC disease (unsatisfiable for
  -- garbage `pcf`), and the field was dead plumbing (`callClosureSim` never
  -- consumed it).  Ledger `callclosuregeom-entryfold-pcf-unsatisfiable`.  The
  -- params-fold's named home is the `CallParamFoldInv` carrier +
  -- `storeChainList` composition in `rows/CallClosureSplice.lean`, absorbed
  -- into `entryBase`.
  /-- **ret** (return marshalling + size-ghost bridge): from the body-sequence
      exit — over WHICHEVER handoff pair `(φf', mB)` the entry route produced
      (`PhiExtends` + the stack/arena frame are the only facts carried across
      the body IH) — run the return arm: `status` reclassification (`a_6`),
      `--call_depth`, result copy (the `0x80003954` `.normal` path, the 24-byte
      body-sret → CALL-sret copy on `.ret v`, `rows/CallClosureRetCopyGen`) to
      the epilogue join `SegExit … st.store.sizes st' callJoinPC m0` — the
      size ghosts and the memory baseline REVERT to the caller's (`SegExit`'s
      `store`/`memFrame` are ∃-φ/framed, so the revert is satisfiable:
      `PhiExtends φf — φf' — φf''` chains by `PhiExtends.trans`, and the join
      `memFrame` to `m0` follows from `mB`'s frame + the return arm writing only
      stack).  Guarded `cd.body ≠ []` (the `[]` route never visits
      `callBodyRetPC`).  Supplied by the status-classification decode ≫ the
      result-copy row ≫ the join marshalling (`rows/CallClosureSplice.lean`). -/
  ret :
    cd.body ≠ [] →
    -- wave 40: the entry-side spill image (`s7@1016(sp)` = `g x23`, tabled at
    -- `callDispatchPC`) — the ret routes' restore source, supplied by the
    -- amended `mCall` motive (ledger `segentry-no-caller-spill-image`).
    EntryImage callDispatchPC g m0 →
    ∀ (g' : (R : Register) → Option (RegisterType R)) (φf' : Addr → Nat) (mB : Mem),
      PhiExtends φf φf' st.store.frames.size →
      (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < SL.hi) → ¬ (A.lo ≤ a ∧ a < A.hi) →
        mB[a]? = m0[a]?) →
      BodyGhostTie g g' →
      (∀ spv : BitVec 64, g Register.x2 = some spv →
        CallerSpillSlots g spv mB m0) →
      Triple
        (SegExit g' N A SL φf' φc
          (closureBoundSt st store' cd vs frame).store.frames.size
          (closureBoundSt st store' cd vs frame).store.closures.size
          st' callBodyRetPC mB)
        (SegExit g N A SL φf φc
          st.store.frames.size st.store.closures.size st' callJoinPC m0)
  /-- **emptyBypass** — the `cd.body = []` machine route: the body-count check
      (`bgtz a5 @0x80003338`) is NOT taken and the machine jumps straight to the
      `.normal` return path (`j 0x80003954`), never visiting
      `callBodyLoopPC`/`callBodyRetPC`.  `ExecSeq`'s `nil` forces
      `st' = boundSt` and `status = .normal` (the row inverts `a_5`), so the
      route is stated at that exit state.  Supplied by the same splice layer as
      `entryBase` up to the check, then the `.normal` return arm. -/
  emptyBypass :
    cd.body = [] →
    st' = closureBoundSt st store' cd vs frame →
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft callDispatchPC m0)
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
    -- wave 40: the entry-side spill image (the amended `mCall` hypothesis),
    -- threaded to the `ret` seam (its restore routes read `1016(sp)` off `m0`).
    (hImg : EntryImage callDispatchPC g m0)
    (_hClos : st.store.closures[a]? = some cd)
    (_hArity : vs.length = cd.params.length)
    (_hDepth : d < maxCallDepth)
    (_hAlloc : st.store.allocFrame (some cd.env) = (store', frame))
    (_hStatus : status = Status.normal ∧ v = Value.null ∨ status = Status.ret v)
    -- the `ExecSeq.nil` inversion link (the row inverts `a_5`): on the
    -- empty-body route the exit state IS the bound state.
    (hNilLink : cd.body = [] → st' = closureBoundSt st store' cd vs frame)
    -- the recursive body IH (the `a_5`/`mExecSeq` motive the recursor supplies),
    -- instantiated at the closure body-loop head / return PCs, universal in the
    -- handoff triple `(g', φf', mB)` — FREE from `mExecSeq`'s own `∀ g φf φc … m0`:
    (hBodyIH : ∀ (g' : (R : Register) → Option (RegisterType R))
        (φf' : Addr → Nat) (mB : Mem),
      Vsa.Sim.TermSimAssembly.SeqSpanGround callBodyLoopPC callBodyRetPC mB →
      Triple
        (SegEntry g' N A SL φf' φc
          (closureBoundSt st store' cd vs frame) (d + 1) (dLeft - 1) (aLeft - 1)
          callBodyLoopPC mB)
        (SegExit g' N A SL φf' φc
          (closureBoundSt st store' cd vs frame).store.frames.size
          (closureBoundSt st store' cd vs frame).store.closures.size
          st' callBodyRetPC mB))
    (hGeom : CallClosureGeom g N A SL φf φc st st' d a cd vs store' frame status v
      dLeft aLeft m0) :
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft callDispatchPC m0)
      (SegExit g N A SL φf φc st.store.frames.size st.store.closures.size st'
        callJoinPC m0) := by
  cases hb : cd.body with
  | nil =>
    -- the empty-body machine route: dispatch → `.normal` path → join
    -- (`emptyBypass`'s conclusion is stated at the SAME `st'`).
    exact hGeom.emptyBypass hb (hNilLink hb)
  | cons s ss =>
    have hne : cd.body ≠ [] := by rw [hb]; exact List.cons_ne_nil s ss
    -- prefix ≫ body-IH ≫ return (DeriveCallSeg.callSeg), the mid-predicates
    -- carrying the ∃-bound handoff pair through the body IH.
    refine callSeg (hGeom.entryBase hne)
      (Mid1 := BodyHandoff g N A SL φf φc st store' cd vs frame d dLeft aLeft m0)
      (Mid2 := fun c => ∃ (g' : (R : Register) → Option (RegisterType R))
          (φf' : Addr → Nat) (mB : Mem),
        PhiExtends φf φf' st.store.frames.size ∧
        (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < SL.hi) → ¬ (A.lo ≤ a ∧ a < A.hi) →
          mB[a]? = m0[a]?) ∧
        BodyGhostTie g g' ∧
        (∀ spv : BitVec 64, g Register.x2 = some spv →
          CallerSpillSlots g spv mB m0) ∧
        SegExit g' N A SL φf' φc
          (closureBoundSt st store' cd vs frame).store.frames.size
          (closureBoundSt st store' cd vs frame).store.closures.size
          st' callBodyRetPC mB c)
      ?_ ?_
    · -- body hop: run the IH at the handoff triple (guard fed from the
      -- handoff's `Eval_exprLoaded mB`), carry its facts across.
      intro c hc
      obtain ⟨g', φf', mB, hpe, hfr, htie, hslots, hLoad, hSeg⟩ := hc
      obtain ⟨c', hsteps, hExit⟩ :=
        hBodyIH g' φf' mB (Vsa.Sim.TermSimAssembly.seqSpanGround_of rfl hLoad) c hSeg
      exact ⟨c', hsteps, g', φf', mB, hpe, hfr, htie, hslots, hExit⟩
    · -- return hop: `ret` at the carried handoff facts.
      intro c hc
      obtain ⟨g', φf', mB, hpe, hfr, htie, hslots, hExit⟩ := hc
      exact hGeom.ret hne hImg g' φf' mB hpe hfr htie hslots c hExit

/-! ## §4. The params-fold discharged through `storeChainList`

A WITNESS that the closure params-fold is exactly the `storeChainList` shape:
given a per-param seam family (over any carrier at `foldStore … k` — here the
`StoreSeg` carrier; `rows/CallClosureSplice.lean` uses the machine-honest
`CallParamFoldInv` carrier), `storeChainList` composes the whole run
`foldStore … 0 → foldStore … n` — the `Store.define`-per-param chain of the
closure param-bind.  At `n := (cd.params.zip vs).length` the top carrier's
store is the full `closureBoundStore` (`foldStore_full`). -/
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

/-- The `hCallClosure` residual: the `CallClosureGeom` bundle (the entry route
to the `BodyHandoff`, the return marshalling over the handoff pair, and the
empty-body bypass), ∀-closed over the ghosts.  The depth guard
`a_3 : d < maxCallDepth` is supplied per-invocation (it is a `Call.closure`
constructor argument, `TermGuards.depthCrux`-shaped). -/
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
    EntryImage callDispatchPC g m0 →
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft callDispatchPC m0)
      (SegExit g N A SL φf φc st.store.frames.size st.store.closures.size st'
        callJoinPC m0)
  intro g N A SL φf φc dLeft aLeft m0 hImg
  -- `ExecSeq.nil` inversion: on the empty body the exit state is the bound state.
  have hNilLink : cd.body = [] → st' = closureBoundSt st store' cd vs frame := by
    intro hb
    -- a fresh copy of `a_5` (rewriting `a_5` itself would disturb `hBody`,
    -- whose type mentions it), transported to the `[]` index and inverted.
    have h5 : ExecSeq
        { store := List.foldl (fun s x => match x with | (x, v) => s.define frame x v)
            store' (cd.params.zip vs), out := st.out }
        (d + 1) frame [] st' status := hb ▸ a_5
    cases h5
    rfl
  -- The body sub-motive `mExecSeq … a_5` at the closure body-loop/return PCs is
  -- the `hBodyIH` family (definitional unfolding of `mExecSeq`; its universal
  -- `g`/`φf`/`m0` quantifiers are instantiated at the entry route's handoff
  -- triple).
  have hBodyIH : ∀ (g' : (R : Register) → Option (RegisterType R))
      (φf' : Addr → Nat) (mB : Mem),
      Vsa.Sim.TermSimAssembly.SeqSpanGround callBodyLoopPC callBodyRetPC mB →
      Triple
        (SegEntry g' N A SL φf' φc
          (closureBoundSt st store' cd vs frame) (d + 1) (dLeft - 1) (aLeft - 1)
          callBodyLoopPC mB)
        (SegExit g' N A SL φf' φc
          (closureBoundSt st store' cd vs frame).store.frames.size
          (closureBoundSt st store' cd vs frame).store.closures.size
          st' callBodyRetPC mB) :=
    fun g' φf' mB hG =>
      hBody g' N A SL φf' φc (dLeft - 1) (aLeft - 1) callBodyLoopPC callBodyRetPC mB hG
  exact callClosureSim g N A SL φf φc st st' d a cd vs store' frame status v
    dLeft aLeft m0 hImg a_1 a_2 a_3 a_4 a_6 hNilLink hBodyIH
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
