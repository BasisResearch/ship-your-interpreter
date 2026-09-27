import Vsa.Sim.AllocClosure
import Vsa.Sim.rows.CallClosureRow

/-!
# `CallClosureEnvNewMarshal` — the `StoreRepr`–`allocFrame` marshalling (wave 38)

Task Wave-38, residual span (b): the `φf'`-binding core of the `hEnvNewToFold`
bridge (`rows/CallClosureSplice.lean`, `callClosureEntrySplice`).  `env_new`
returns a fresh 32-byte `Env` at `p` representing the EMPTY frame
`⟨some cd.env, []⟩` (`env_new_post`'s `FrameRepr`); on the spec side `a_4` says
`st.store.allocFrame (some cd.env) = (store', frame)`.  This file lands:

* `allocFrame_inv` — the `a_4` inversion (`store'` is the push, `frame` is the
  old size);
* `pushFrameMap`/`pushFrameMap_extends` — the canonical one-point extension of
  the frame map at the fresh spec address, with its `PhiExtends` witness (this
  is the `φf'` the entry splice ∃-binds);
* `storeRepr_allocFrame` — the FRAME-side sibling of
  `AllocClosure.storeRepr_pushClosure` (the model, mirrored field-for-field):
  a store represented under the extended map, plus the fresh frame's
  `FrameRepr`/arena/alignment/freshness facts, represents the pushed store.

As in the model, `hOld` is stated at the EXTENDED map `φf'` — the caller
rewrites its `StoreRepr … φf` through `PhiExtends` (only addresses
`< s.frames.size` occur; the `EnvGetMarshal`/`GrowEnvEntry` discipline), and
gets freshness from malloc's `ExtDisjoint` against the old frame images.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
Axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/

open Vsa Vsa.While
open Vsa.RuntimeRepr
open Vsa.MemRepr

