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
∀ g N A SL φf φc dLeft aLeft sp sret m0,
  EntryImage callDispatchPC g m0 →
  Triple (CallEntryI … st d (.closure a) vs dLeft aLeft sp sret m0)
         (CallExitI  … st.store.frames.size st.store.closures.size st' v sret m0)
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

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

/-! ## §1. The bound child store (`env_new` + the `env_define` params-fold)

The store the closure body runs against: the fresh frame `frame` over `cd.env`,
each parameter bound to its argument (`foldl .define` over `cd.params.zip vs`).
This is EXACTLY the spec state `a_5`/`mExecSeq` is stated over — named once so the
three seams and the fold share ONE canonical write-log normal form (fast-reflection
rule 5). -/

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

-- discipline: allow(R7-conj-tower-def) `BodyHandoff` is a reached-Config
-- landing bundle carrying DATA binders (φf', mB) — the sanctioned
-- `def : Prop := ∃ …` shape (Prop structures cannot carry data fields, cf. the
-- WidenMeta gotcha); consumers destructure it exactly once, in `callClosureSim`.

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

/-! ## §4. The params-fold discharged through `storeChainList`

A WITNESS that the closure params-fold is exactly the `storeChainList` shape:
given a per-param seam family (over any carrier at `foldStore … k` — here the
`StoreSeg` carrier; `rows/CallClosureSplice.lean` uses the machine-honest
`CallParamFoldInv` carrier), `storeChainList` composes the whole run
`foldStore … 0 → foldStore … n` — the `Store.define`-per-param chain of the
closure param-bind.  At `n := (cd.params.zip vs).length` the top carrier's
store is the full `closureBoundStore` (`foldStore_full`). -/

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

local notation "SpecSt" => Vsa.While.St

end Vsa.Sim.Rows

