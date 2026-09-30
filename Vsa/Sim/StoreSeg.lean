import Vsa.Sim.InterpInit
import Vsa.Sim.TripleCat

/-!
# `StoreSeg` / `storeChain` — the generalized store-carrier + env-call chain combinator

`Vsa/Sim/InterpInit.lean` built a bespoke `InitSeg` carrier (a `Config → Prop`
threaded between `interp_init`'s `env_new ≫ env_define×3`) and composed the four
call/epilogue seams by hand (`interpInitStore_compose = Triple.seq …×4`).  The
ledger's `interp-init-store-carrier` entry flags this as an abstraction candidate:
the SAME shape recurs anywhere a straight sequence of env calls each advances an
accumulator store by one `Store.define`/`Store.set?` — most importantly

* `ExecS.varInit` / `ExecE.assign` (one define/set seam, `hSVarInit`/`hAssign`), and
* `Call.closure`'s params-fold `((cd.params.zip vs).foldl (fun s (x,v) => s.define …))`
  — a variable-length chain of `define` seams, ONE per bound parameter.

This file GENERALIZES `InitSeg` into

* **`StoreSeg`** — a store-parametric, PC-parametric named-field carrier (`GoodState`
  + tick parity + PC pin + `StoreRepr` of the accumulator store + `OutRepr`), the
  store-generic analogue of `InitSeg` with the fixed native-address ghosts (`N/A/SL/φf/φc`)
  abstracted as parameters.  `InitSeg N A SL φf φc store pc = StoreSeg N A SL φf φc store pc out0`
  at `out0 := initSt` (the `Ent` morphism `initSeg_ent_storeSeg`).
* **`storeChain`** — the combinator that composes a LIST of env-call seams, each a named
  `Triple (StoreSeg … storeₖ pcₖ) (StoreSeg … storeₖ₊₁ pcₖ₊₁)` advancing the carried store
  by one env operation and the PC past that call's arg-setup + `jal`.  It is a fold of
  `Triple.seq` over the seam list, plus the framing prologue/epilogue seams — the honest
  generalization of `interpInitStore_compose`.

`storeChain2`/`storeChain3` are the fixed-arity specializations `varInit`/`assign` (one
seam) and `interp_init` (three seams) instantiate; `storeChainList` is the variable-arity
fold `Call.closure`'s params-fold consumes.

## The `InterpInit` demo (parallel, non-invasive)

`interpInitStore_compose_viaStoreSeg` re-expresses `interpInitStore_compose`'s exact
statement THROUGH `storeChain3`, proving the two are the same composition (`InitSeg` seams
reindexed to `StoreSeg` seams by the `Ent` morphisms `initSeg_ent_storeSeg`).  It does
NOT edit `InterpInit`; it is a witness that the general combinator subsumes the bespoke one.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic (Triple Ent)
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While (initSt Store Frame Value NativeFn Addr St)

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

/-! ## §1. `StoreSeg` — the generalized store-carrier

The store-parametric, PC-parametric, output-parametric named-field carrier threaded
between env calls.  Five fixed layout ghosts (`N/A/SL/φf/φc`), the accumulator `store`,
the resume `pc`, and the reference state `st0` whose `.out` the console must match.  A
single `structure … : Prop where` — no ∃/∧ tower (CLAUDE.md named-field law). -/

/-! ## §2. `storeChain` — the fixed-arity chain combinators

Each combinator composes framing/prologue seam `hPre : Triple P (StoreSeg … s₀ pc₀)`,
a run of per-call store-advancing seams, and an epilogue seam `hPost : Triple (StoreSeg
… sₙ pcₙ) Q`, by `Triple.seq`.  These are the honest generalization of
`interpInitStore_compose` — the store threads through the `StoreSeg` carrier one
`Store.define`/`Store.set?` per seam. -/

/-! ## §3. `storeChainList` — the variable-arity fold (`Call.closure`'s params-fold)

`Call.closure` binds `cd.params.zip vs` into the callee frame by
`(cd.params.zip vs).foldl (fun s (x,v) => s.define fa x v) s0`.  The machine mirrors
this with a variable-length run of `env_define` seams — ONE per bound `(x,v)`.  The
carrier at seam `k` holds the store folded over the first `k` params and the PC past
`k` defines.  `storeChainList` is exactly the fold of `Triple.seq` over such a seam
list; its "advance" function is any `Config`-store step (the closure fold uses
`fun s (x,v) => s.define fa x v`, matched by each seam's post store).

The seam list is given as a function `seam : (k : Fin ps.length) → Triple (carrier k)
(carrier k.succ)` over the params `ps`; the fold composes them left-to-right against a
carrier family `carrier : Nat → Config → Prop`.  This is the store-generic analogue of
`evalArgsStepOf`'s fold (`rows/LoopSteps.lean`) at the store level. -/

/-! ## §4. Demo — `interpInitStore_compose` re-expressed through `storeChain3`

A PARALLEL theorem to `InterpInit.interpInitStore_compose` (that file is NOT edited):
the EXACT same statement — the same four `InitSeg` seam premises and the same `Triple P
Q` conclusion — proved by routing through the general `storeChain3` combinator, with the
`InitSeg` seams reindexed to `StoreSeg` seams at `st0 := initSt` by the `Ent` morphisms.
This witnesses that the bespoke `interpInitStore_compose` is the `storeChain3`
specialization. -/

end Vsa.Sim
