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
open Vsa.Sim.Scaffold (SegEntry)

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

/-! ## §1. `StoreSeg` — the generalized store-carrier

The store-parametric, PC-parametric, output-parametric named-field carrier threaded
between env calls.  Five fixed layout ghosts (`N/A/SL/φf/φc`), the accumulator `store`,
the resume `pc`, and the reference state `st0` whose `.out` the console must match.  A
single `structure … : Prop where` — no ∃/∧ tower (CLAUDE.md named-field law). -/
structure StoreSeg
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (store : Store) (pc : Nat) (st0 : SpecSt) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 pc)
  store : StoreRepr c.σ.mem N A φf φc store
  out : OutRepr c.σ st0

/-- `InitSeg` entails `StoreSeg` at the reference state `initSt`: they carry the SAME
five fields (`InitSeg.out` is `OutRepr … initSt`), so this is a field copy.  The two
directions (`initSeg_ent_storeSeg` / `storeSeg_ent_initSeg`) are the `Ent` morphisms
that `dimap` an `InitSeg` seam to a `StoreSeg` seam and back — no bespoke `conseq`. -/
theorem initSeg_ent_storeSeg
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (store : Store) (pc : Nat) :
    Ent (InitSeg N A SL φf φc store pc) (StoreSeg N A SL φf φc store pc initSt) :=
  fun _ h => ⟨h.good, h.tick, h.pc, h.store, h.out⟩

/-- The reverse morphism (`StoreSeg … initSt → InitSeg …`), the `Ent` used to
`dimap` the epilogue back. -/
theorem storeSeg_ent_initSeg
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (store : Store) (pc : Nat) :
    Ent (StoreSeg N A SL φf φc store pc initSt) (InitSeg N A SL φf φc store pc) :=
  fun _ h => ⟨h.good, h.tick, h.pc, h.store, h.out⟩

/-! ## §2. `storeChain` — the fixed-arity chain combinators

Each combinator composes framing/prologue seam `hPre : Triple P (StoreSeg … s₀ pc₀)`,
a run of per-call store-advancing seams, and an epilogue seam `hPost : Triple (StoreSeg
… sₙ pcₙ) Q`, by `Triple.seq`.  These are the honest generalization of
`interpInitStore_compose` — the store threads through the `StoreSeg` carrier one
`Store.define`/`Store.set?` per seam. -/

/-- **One-seam chain** (`varInit`/`assign` shape).  A prologue seam into the entry
carrier, ONE store-advancing env-call seam (`s₀ → s₁`), and an epilogue seam out. -/
theorem storeChain1
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {P Q : Config → Prop} {st0 : SpecSt}
    {s0 s1 : Store} {pc0 pc1 : Nat}
    (hPre  : Triple P (StoreSeg N A SL φf φc s0 pc0 st0))
    (hSeam : Triple (StoreSeg N A SL φf φc s0 pc0 st0)
                    (StoreSeg N A SL φf φc s1 pc1 st0))
    (hPost : Triple (StoreSeg N A SL φf φc s1 pc1 st0) Q) :
    Triple P Q :=
  Triple.seq hPre (Triple.seq hSeam hPost)

/-- **Three-seam chain** (`interp_init` shape): prologue `≫` seam₁ `≫` seam₂ `≫` seam₃
`≫` epilogue, all `Triple.seq`.  The store advances `s₀ → s₁ → s₂ → s₃`. -/
theorem storeChain3
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {P Q : Config → Prop} {st0 : SpecSt}
    {s0 s1 s2 s3 : Store} {pc0 pc1 pc2 pc3 : Nat}
    (hPre   : Triple P (StoreSeg N A SL φf φc s0 pc0 st0))
    (hSeam1 : Triple (StoreSeg N A SL φf φc s0 pc0 st0)
                     (StoreSeg N A SL φf φc s1 pc1 st0))
    (hSeam2 : Triple (StoreSeg N A SL φf φc s1 pc1 st0)
                     (StoreSeg N A SL φf φc s2 pc2 st0))
    (hSeam3 : Triple (StoreSeg N A SL φf φc s2 pc2 st0)
                     (StoreSeg N A SL φf φc s3 pc3 st0))
    (hPost  : Triple (StoreSeg N A SL φf φc s3 pc3 st0) Q) :
    Triple P Q :=
  Triple.seq hPre
    (Triple.seq hSeam1
      (Triple.seq hSeam2
        (Triple.seq hSeam3 hPost)))

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

/-- **The variable-arity store chain.**  Given a carrier family `carrier k` (the
`StoreSeg` at the store folded over the first `k` params, PC past `k` defines) and a
per-index seam `seam k : Triple (carrier k) (carrier (k+1))`, compose the whole run
`carrier 0 → carrier n` by a left fold of `Triple.seq`.  `Call.closure` instantiates
`carrier k := StoreSeg … (foldl define over first-k params) (pc past k defines) st0`. -/
theorem storeChainList
    (carrier : Nat → Config → Prop) (n : Nat)
    (seam : ∀ k, k < n → Triple (carrier k) (carrier (k + 1))) :
    Triple (carrier 0) (carrier n) := by
  induction n with
  | zero => exact Triple.rfl
  | succ m ih =>
    exact Triple.seq
      (ih (fun k hk => seam k (Nat.lt_succ_of_lt hk)))
      (seam m (Nat.lt_succ_self m))

/-! ## §4. Demo — `interpInitStore_compose` re-expressed through `storeChain3`

A PARALLEL theorem to `InterpInit.interpInitStore_compose` (that file is NOT edited):
the EXACT same statement — the same four `InitSeg` seam premises and the same `Triple P
Q` conclusion — proved by routing through the general `storeChain3` combinator, with the
`InitSeg` seams reindexed to `StoreSeg` seams at `st0 := initSt` by the `Ent` morphisms.
This witnesses that the bespoke `interpInitStore_compose` is the `storeChain3`
specialization. -/
theorem interpInitStore_compose_viaStoreSeg
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {P Q : Config → Prop}
    (hEnvNew : Triple P (InitSeg N A SL φf φc initGlobalStore 0x80004328))
    (hDefPrint : Triple
      (InitSeg N A SL φf φc initGlobalStore 0x80004328)
      (InitSeg N A SL φf φc storeAfterPrint 0x80004368))
    (hDefPrintln : Triple
      (InitSeg N A SL φf φc storeAfterPrint 0x80004368)
      (InitSeg N A SL φf φc storeAfterPrintln 0x800043a0))
    (hDefAssert : Triple
      (InitSeg N A SL φf φc storeAfterPrintln 0x800043a0)
      (InitSeg N A SL φf φc storeAfterAssert 0x800043d8))
    (hEpilogue : Triple (InitSeg N A SL φf φc storeAfterAssert 0x800043d8) Q) :
    Triple P Q :=
  -- Reindex each `InitSeg` seam to a `StoreSeg` seam at `st0 := initSt` via the
  -- `Ent` morphisms (R8: `dimap`/`lmap`/`rmap`, never `conseq`-with-identity), then
  -- feed the general `storeChain3`.
  storeChain3 (st0 := initSt)
    (Triple.rmap (initSeg_ent_storeSeg N A SL φf φc initGlobalStore 0x80004328) hEnvNew)
    (Triple.dimap (storeSeg_ent_initSeg N A SL φf φc initGlobalStore 0x80004328)
      (initSeg_ent_storeSeg N A SL φf φc storeAfterPrint 0x80004368) hDefPrint)
    (Triple.dimap (storeSeg_ent_initSeg N A SL φf φc storeAfterPrint 0x80004368)
      (initSeg_ent_storeSeg N A SL φf φc storeAfterPrintln 0x800043a0) hDefPrintln)
    (Triple.dimap (storeSeg_ent_initSeg N A SL φf φc storeAfterPrintln 0x800043a0)
      (initSeg_ent_storeSeg N A SL φf φc storeAfterAssert 0x800043d8) hDefAssert)
    (Triple.lmap (storeSeg_ent_initSeg N A SL φf φc storeAfterAssert 0x800043d8) hEpilogue)

#print axioms StoreSeg
#print axioms initSeg_ent_storeSeg
#print axioms storeSeg_ent_initSeg
#print axioms storeChain1
#print axioms storeChain3
#print axioms storeChainList
#print axioms interpInitStore_compose_viaStoreSeg

end Vsa.Sim
