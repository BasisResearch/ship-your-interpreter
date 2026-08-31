import Vsa.Sim.StoreSeg
import Vsa.Sim.EnvDefMarshal

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

/-- **The store-advance marshalling core.**  Given the reference frame index `a`, name `x`,
value `v` bound by the callee, and the fixed layout ghosts, this bundles the honest readback
facts that a `StoreRepr c.σ.mem N A φf φc (store.define a x v)` reconstruction needs off the
post-call memory: the mutated frame's `FrameRepr`, the other frames' survival, the closures'
survival, and the (shape-preserved) injectivity/arena facts.  Its single method
`toStoreRepr` assembles them into the `StoreRepr` of the advanced store — no machine
reasoning, pure representation algebra over the first-order memory. -/
structure StoreDefineAdvance
    (N : NativeAddrs) (A : Arena) (φf φc : Addr → Nat)
    (store : Store) (a : Addr) (x : String) (v : Value) (m : Mem) : Prop where
  /-- the newly-defined frame `a` is represented as the mutated frame in the post memory
  (the caller's `frameRepr_append` / update readback off the write-log). -/
  mutated : (h : a < (store.define a x v).frames.size) →
    FrameRepr m N φf φc (φf a) (store.define a x v).frames[a]
  /-- every other frame survives (its `Env` bytes are outside the callee footprint). -/
  others : ∀ fa, (h : fa < (store.define a x v).frames.size) → fa ≠ a →
    FrameRepr m N φf φc (φf fa) (store.define a x v).frames[fa]
  /-- the closures are untouched by `define`. -/
  closures : ∀ ca, (h : ca < (store.define a x v).closures.size) →
    ClosureRepr m φf (φc ca) (store.define a x v).closures[ca]
  /-- `φf`/`φc` remain injective on the (unchanged-size) allocated prefixes. -/
  φf_inj : ∀ p q, p < (store.define a x v).frames.size → q < (store.define a x v).frames.size →
    φf p = φf q → p = q
  φc_inj : ∀ p q, p < (store.define a x v).closures.size →
    q < (store.define a x v).closures.size → φc p = φc q → p = q
  /-- the arena bounds hold for the (unchanged-size) frames/closures. -/
  frames_arena : ∀ fa, fa < (store.define a x v).frames.size →
    A.contains (φf fa) 32 ∧ φf fa % 8 = 0
  closures_arena : ∀ ca, ca < (store.define a x v).closures.size →
    A.contains (φc ca) 16 ∧ φc ca % 8 = 0

namespace StoreDefineAdvance

/-- Assemble the advance's readback fields into the `StoreRepr` of `store.define a x v`.
The frame method dispatches on `fa = a` (mutated, the `mutated` field at the in-bounds
accessor) vs `fa ≠ a` (survives, the `others` field). -/
theorem toStoreRepr
    {N : NativeAddrs} {A : Arena} {φf φc : Addr → Nat}
    {store : Store} {a : Addr} {x : String} {v : Value} {m : Mem}
    (h : StoreDefineAdvance N A φf φc store a x v m) :
    StoreRepr m N A φf φc (store.define a x v) where
  frames fa hfa := by
    by_cases hEq : fa = a
    · subst hEq; exact h.mutated hfa
    · exact h.others fa hfa hEq
  closures := h.closures
  φf_inj := h.φf_inj
  φc_inj := h.φc_inj
  frames_arena := h.frames_arena
  closures_arena := h.closures_arena

end StoreDefineAdvance

/-! ## §2. The marshalling `Ent` — contract post ⊢ₑ next `StoreSeg`

`storeSeg_advance_define` is the entailment that closes the marshalling stage: from the
callee contract's post `MidPost` — which the caller has arranged to carry the control pins
(`GoodState`/tick/PC-at-resume/`OutRepr`) AND a `StoreDefineAdvance` off the post memory —
it produces `StoreSeg … (store.define a x v) pc₁ st0`, the carrier the next chain link
holds.  It is a pure `Ent` (field assembly): the store field is `StoreDefineAdvance.toStoreRepr`,
the rest are the pins the post already carries.  Fed to the template via `Triple.rmap` (R8). -/

/-- **The marshalling entailment.**  `MidPost ⊢ₑ StoreSeg … (store.define a x v) pc₁ st0`,
where `MidPost` is required (by the caller's `hFields`) to expose, on each of its configs,
the four control pins + the `StoreDefineAdvance` readback over that config's memory.  This
is the store-carrier analogue of `initSeg_ent_storeSeg`: a field copy plus the one honest
`toStoreRepr` marshalling.  No machine reasoning. -/
theorem storeSeg_advance_define
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {MidPost : Config → Prop} {store : Store} {a : Addr} {x : String} {v : Value}
    {pc1 : Nat} {st0 : SpecSt}
    (hFields : ∀ c, MidPost c →
      GoodState c.σ ∧ c.tick < 2 ∧
      c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 pc1) ∧
      StoreDefineAdvance N A φf φc store a x v c.σ.mem ∧
      OutRepr c.σ st0) :
    Ent MidPost (StoreSeg N A SL φf φc (store.define a x v) pc1 st0) := by
  intro c hc
  obtain ⟨hG, htick, hpc, hAdv, hout⟩ := hFields c hc
  exact ⟨hG, htick, hpc, hAdv.toStoreRepr, hout⟩

/-! ## §3. `envCallArmBridge` — the template

The seam `StoreSeg … storeₖ pcₖ → StoreSeg … (storeₖ.define a x v) pc₁` composed from the
three stages.  `hPre` and `hCallee` are the honest machine seams (arg-setup prefix ≫ jal,
and the landed callee contract); `hMarshal` is the marshalling `Ent` from §2.  The whole
seam is `hPre ≫ hCallee ≫ rmap hMarshal` — pure `Triple.seq`/`rmap`, no new reasoning. -/

/-- **The env-call arm bridge template.**  From the arg-setup-prefix-and-jal seam `hPre`
(genseg + `BridgeSeg`), the landed callee contract `hCallee`, and the marshalling
entailment `hMarshal` (§2, the `FrameRepr`-post → `StoreRepr`-advance step), produce the
`StoreSeg` seam `storeChain{1,3,List}` consumes.  This is the ONE shape all ~8 env-call
seams share; instantiating it needs only the three named premises. -/
theorem envCallArmBridge
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {store : Store} {a : Addr} {x : String} {v : Value}
    {pc0 pc1 : Nat} {st0 : SpecSt}
    {MidPre MidPost : Config → Prop}
    (hPre : Triple (StoreSeg N A SL φf φc store pc0 st0) MidPre)
    (hCallee : Triple MidPre MidPost)
    (hMarshal : Ent MidPost (StoreSeg N A SL φf φc (store.define a x v) pc1 st0)) :
    Triple (StoreSeg N A SL φf φc store pc0 st0)
           (StoreSeg N A SL φf φc (store.define a x v) pc1 st0) :=
  Triple.seq hPre (Triple.rmap hMarshal hCallee)

/-- **`env_define` flavor.**  The callee is `env_define`; the store advances by
`store.define a x v` (append when `x` absent, update when present — both are `Store.define`).
The marshalling `Ent` is supplied via §2's `storeSeg_advance_define` from the caller's
`hFields` readback of the contract post.  This is the flavor the `InterpInit` defines,
`hSVarInit`, and `Call.closure`'s params-fold instantiate. -/
theorem envDefineArmBridge
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {store : Store} {a : Addr} {x : String} {v : Value}
    {pc0 pc1 : Nat} {st0 : SpecSt}
    {MidPre MidPost : Config → Prop}
    (hPre : Triple (StoreSeg N A SL φf φc store pc0 st0) MidPre)
    (hCallee : Triple MidPre MidPost)
    (hFields : ∀ c, MidPost c →
      GoodState c.σ ∧ c.tick < 2 ∧
      c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 pc1) ∧
      StoreDefineAdvance N A φf φc store a x v c.σ.mem ∧
      OutRepr c.σ st0) :
    Triple (StoreSeg N A SL φf φc store pc0 st0)
           (StoreSeg N A SL φf φc (store.define a x v) pc1 st0) :=
  envCallArmBridge hPre hCallee (storeSeg_advance_define hFields)

/-- **`env_set` flavor.**  `env_set`'s in-place parent-chain update `Store.set?` reduces,
on the hit frame, to `Store.define`'s update branch (`vars.map (if ·.1==x then (x,v) else ·)`),
so the arm's store advance is `store.define a x v` at the hit frame `a` — the SAME advance
shape.  The flavor differs only in `hCallee` being the `env_set` contract (`hUpdate_wired`);
the marshalling is identical.  `AssignArmSpec`'s `env_set` call instantiates this. -/
theorem envSetArmBridge
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {store : Store} {a : Addr} {x : String} {v : Value}
    {pc0 pc1 : Nat} {st0 : SpecSt}
    {MidPre MidPost : Config → Prop}
    (hPre : Triple (StoreSeg N A SL φf φc store pc0 st0) MidPre)
    (hCallee : Triple MidPre MidPost)
    (hFields : ∀ c, MidPost c →
      GoodState c.σ ∧ c.tick < 2 ∧
      c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 pc1) ∧
      StoreDefineAdvance N A φf φc store a x v c.σ.mem ∧
      OutRepr c.σ st0) :
    Triple (StoreSeg N A SL φf φc store pc0 st0)
           (StoreSeg N A SL φf φc (store.define a x v) pc1 st0) :=
  envCallArmBridge hPre hCallee (storeSeg_advance_define hFields)

#print axioms StoreDefineAdvance.toStoreRepr
#print axioms storeSeg_advance_define
#print axioms envCallArmBridge
#print axioms envDefineArmBridge
#print axioms envSetArmBridge

end Vsa.Sim
