import Vsa.Sim.StoreSeg
import Vsa.Sim.EnvDefMarshal
import Vsa.Sim.StoreInvariant

/-!
# `EnvCallBridge` — the ONE template for "caller arm parks at a `jal` into
env_new/env_define/env_set; the landed contract runs; the post's `FrameRepr`
marshals back into a `StoreSeg` carrier".

Roughly eight seams across the board share this exact shape (ledger entries
`envCallArmBridge`, `storeseg-storechain`, `interp-init-store-carrier`):

* the four `InterpInit` seams (`env_new(NULL) ≫ env_define×3`, `InterpInit.lean`);
* `AssignArmSpec`'s `env_set` call (`rows/EvalAssignRow.lean`, arm `0x8000347c..0x800034b8`);
* `hSVarInit`'s `hGlue` (`rows/ExecVarInitRow.lean`);
* `CallClosureGeom.entryFold`'s per-param defines (`rows/CallClosureRow.lean`).

Every instance is the SAME three-stage composition:

```
  StoreSeg … storeₖ  pcₖ                     ── the carrier the chain holds
    ≫  <arg-setup prefix seg ≫ jal callee>   ── hPre  (genseg + BridgeSeg jal seam)
    ≫  <landed callee contract>              ── hCallee (env_new/define/set Triple)
    ≫  <FrameRepr-post → StoreRepr advance>  ── the marshalling core (this file)
  StoreSeg … storeₖ₊₁ pcₖ₊₁                  ── the next carrier storeChain consumes
```

The parts ALL EXIST elsewhere and are threaded, never rebuilt:

* `hPre`   — the arm compiler (`scripts/genseg.py`) emits the arg-setup seg's
  `Triple`, and `BridgeSeg.bridgeOfSeg`/`jalStep_of_obs` is the `jal` seam.
* `hCallee`— the landed contract Triple: `EnvNewSpec.env_new_spec` (fresh frame),
  `EnvDefMarshal.env_define_append_spec` (append), or the `env_set` update
  contract (`hUpdate_wired` shape).
* the marshalling — `EnvDefMarshal`'s carriers (`AppendedFrameSt`/`UpdatedFrameSt`)
  give the `FrameRepr` of the extended/updated frame off the contract post; this
  file lifts that per-frame `FrameRepr` step to the whole-store `StoreRepr` advance
  (`StoreDefineAdvance`) that the `StoreSeg` carrier needs.

## What this file lands

* **`StoreDefineAdvance`** — the marshalling core, a NAMED-field structure (CLAUDE.md
  law, model `FrameCalc`/`FoundSt`): the honest readback obligation that turns a
  `StoreRepr storeₖ` config into a `StoreRepr (storeₖ.define a x v)` config after the
  callee's write-block ran.  It packages exactly the frame-level facts the caller reads
  off the computed memory (the `FrameRepr` of the newly-defined frame + the OTHER frames
  surviving + the injectivity/arena facts extending), so an instantiation supplies only
  its name/value/frame-index data — no machine reasoning.
* **`storeSeg_advance_define`** — the `Ent` that IS the marshalling step
  `MidPost ⊢ₑ StoreSeg … (define …) pc₁`, built from a `StoreDefineAdvance` and the
  control pins (PC/tick/good/out) the contract post carries.  All adapters via `Ent`/`rmap`.
* **`envCallArmBridge`** — the template proper: `hPre ≫ hCallee ≫ rmap hMarshal`,
  producing the `StoreSeg … storeₖ pcₖ → StoreSeg … storeₖ₊₁ pcₖ₊₁` seam that
  `StoreSeg.storeChain1/3/List` consumes.  Three thin flavor wrappers
  (`envDefineArmBridge` / `envNewArmBridge` / `envSetArmBridge`) fix the callee/advance
  shape so a caller names only its data.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic (Triple Ent)
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While (initSt Store Frame Value NativeFn Addr St)

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

set_option maxHeartbeats 800000

/-! ## §1. The marshalling core — `StoreRepr` advance from a `FrameRepr` post

`StoreDefineAdvance` is the store-level analogue of `EnvDefMarshal.frameRepr_of_appendStore`:
that lemma lands the `FrameRepr` of the ONE mutated frame off the contract post; here we
lift it to the whole `StoreRepr`.  `Store.define a x v` mutates ONLY frame `a` (it is
`s.frames.modify a …`) and leaves `s.closures` untouched, so a `StoreRepr (s.define a x v)`
of the post-memory `m` is exactly:

* the mutated frame `a` represented as `(s.frames[a]).define-mutated` — the caller's
  `FrameRepr` readback (`frameRepr_append` / `frameRepr` update analogue, the honest data);
* every OTHER frame `b ≠ a` still represented (its C `Env` bytes are outside the callee's
  write footprint — the caller's frame/footprint disjointness);
* the closures still represented (untouched);
* injectivity/arena facts, unchanged in shape (`define` does not change `.size`, so the
  same `φf`/`φc` witness the same bounds).

Rather than re-derive these from raw memory, we NAME them as the fields of a structure the
caller proves from its layout + write-log readback — exactly the `EnvDefMarshal` discipline
(the representation facts are caller data, not in the seg post).  The template then feeds
`StoreDefineAdvance` straight into the `StoreSeg` carrier's `store` field. -/

/-! ## §2. The marshalling `Ent` — contract post ⊢ₑ next `StoreSeg`

`storeSeg_advance_define` is the entailment that closes the marshalling stage: from the
callee contract's post `MidPost` — which the caller has arranged to carry the control pins
(`GoodState`/tick/PC-at-resume/`OutRepr`) AND a `StoreDefineAdvance` off the post memory —
it produces `StoreSeg … (store.define a x v) pc₁ st0`, the carrier the next chain link
holds.  It is a pure `Ent` (field assembly): the store field is `StoreDefineAdvance.toStoreRepr`,
the rest are the pins the post already carries.  Fed to the template via `Triple.rmap` (R8). -/

/-! ## §3. `envCallArmBridge` — the template

The seam `StoreSeg … storeₖ pcₖ → StoreSeg … (storeₖ.define a x v) pc₁` composed from the
three stages.  `hPre` and `hCallee` are the honest machine seams (arg-setup prefix ≫ jal,
and the landed callee contract); `hMarshal` is the marshalling `Ent` from §2.  The whole
seam is `hPre ≫ hCallee ≫ rmap hMarshal` — pure `Triple.seq`/`rmap`, no new reasoning. -/

/-! ## Resolved `env_set` result

`envSetArmBridge` above is only suitable after a caller has already selected the
frame updated by the parent-chain search.  The following carrier keeps that
selection explicit and advances to the exact store returned by `Store.set?`.
-/

end Vsa.Sim
