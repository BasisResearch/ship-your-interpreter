import Vsa.Sim.EnvCallBridge
import Vsa.Sim.InterpInit

/-!
# `EnvNewInitSeam` — the `interp_init` `env_new(NULL)` `InitSeg` seam (fresh frame)

`Vsa/Sim/EnvCallBridgeDemos.lean` discharged the THREE `env_define` seams of
`InterpInit.interpInitStore_compose` via `envDefineArmBridge` (the `Store.define`
advance).  The FOURTH seam — `hEnvNew : Triple P (InitSeg … initGlobalStore
0x80004328)` — is a DIFFERENT flavor: `env_new(NULL)` does not *advance* an existing
store by `Store.define`; it *creates* the fresh single-global-frame store
`initGlobalStore = ⟨#[⟨none, []⟩], #[]⟩` from nothing.

This file supplies the missing flavor:

* **`StoreFreshAdvance`** — the fresh-frame marshalling core (the `StoreDefineAdvance`
  analogue for a store with EXACTLY ONE frame `⟨none, []⟩` and no closures): the single
  field is the `FrameRepr` of that fresh frame (which `env_new_post` hands the caller,
  with `parentSpec = none`), plus the (trivially-true, one-frame) injectivity/arena
  facts.  Its `toStoreRepr` assembles `StoreRepr initGlobalStore`.
* **`envNewArmBridge`** — the `env_new` flavor wrapper (`hPre ≫ hCallee ≫ rmap hMarshal`,
  exactly the `envCallArmBridge` template shape), producing a `StoreSeg` seam into the
  fresh store carrier.
* **`interpInitEnvNew_seam`** — the `hEnvNew` `InitSeg` seam
  `interpInitStore_compose` demands, via the flavor + the `storeSeg_ent_initSeg`
  reindex (`Triple.dimap`).

With this + the three `env_define` demos + the epilogue seam, ALL of
`interpInitStore_compose`'s premises are the SAME three named per-call inputs
(`hPre`/`hCallee`/`hFields`-readback), none is a fabricated store fact.

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

/-! ## §1. The fresh-frame marshalling core — `StoreRepr initGlobalStore` from a
single `FrameRepr`

`initGlobalStore = { frames := #[⟨none, []⟩], closures := #[] }` (`InterpInit`).  A
`StoreRepr` of it over post-memory `m` reduces to:

* frame `0` (the ONLY frame) is `FrameRepr m N φf φc (φf 0) ⟨none, []⟩` — exactly what
  `env_new_post` hands the caller (`FrameRepr … p ⟨parentSpec, []⟩` at `parentSpec = none`,
  with `φf 0 := p`);
* no other frames, no closures (both arrays have the single/zero size);
* injectivity is vacuous past index `0`/nonexistent closures;
* the arena facts for frame `0` (`A.contains (φf 0) 32 ∧ φf 0 % 8 = 0`) — the
  `env_new_post` `A.contains p 32` + alignment.

We NAME these as the fields of `StoreFreshAdvance` (the caller proves them from its
`env_new_post` readback), mirroring `StoreDefineAdvance`. -/

/-- **The fresh-store marshalling core.**  For the layout ghosts and the fresh frame's
`Addr → Nat` map value `φf 0`, this bundles the honest readback a
`StoreRepr initGlobalStore` reconstruction needs off the `env_new` post memory: the
`FrameRepr` of the single fresh frame `⟨none, []⟩` and its arena/alignment facts.
Its `toStoreRepr` assembles `StoreRepr initGlobalStore` — no machine reasoning. -/
structure StoreFreshAdvance
    (N : NativeAddrs) (A : Arena) (φf φc : Addr → Nat) (m : Mem) : Prop where
  /-- the single fresh frame `⟨none, []⟩` is represented at `φf 0` (the `env_new_post`
  `FrameRepr … p ⟨none, []⟩` readback with `φf 0 = p`). -/
  frame0 : FrameRepr m N φf φc (φf 0) (⟨none, []⟩ : Vsa.While.Frame)
  /-- the fresh frame's arena/alignment facts (`env_new_post`'s `A.contains p 32`). -/
  frame0_arena : A.contains (φf 0) 32 ∧ φf 0 % 8 = 0

namespace StoreFreshAdvance

/-- Assemble the fresh-frame readback into `StoreRepr initGlobalStore`.  Every
`∀ fa < 1` obligation reduces to `fa = 0`; there are no closures. -/
theorem toStoreRepr
    {N : NativeAddrs} {A : Arena} {φf φc : Addr → Nat} {m : Mem}
    (h : StoreFreshAdvance N A φf φc m) :
    StoreRepr m N A φf φc initGlobalStore where
  frames fa hfa := by
    -- initGlobalStore.frames = #[⟨none, []⟩], size 1, so fa = 0.
    have hsz : initGlobalStore.frames.size = 1 := by decide
    have : fa = 0 := by rw [hsz] at hfa; omega
    subst this
    exact h.frame0
  closures ca hca := by
    -- initGlobalStore.closures = #[], size 0 — vacuous.
    have hsz : initGlobalStore.closures.size = 0 := by decide
    rw [hsz] at hca; omega
  φf_inj a b ha hb _ := by
    have hsz : initGlobalStore.frames.size = 1 := by decide
    rw [hsz] at ha hb; omega
  φc_inj a b ha hb _ := by
    have hsz : initGlobalStore.closures.size = 0 := by decide
    rw [hsz] at ha; omega
  frames_arena fa hfa := by
    have hsz : initGlobalStore.frames.size = 1 := by decide
    have : fa = 0 := by rw [hsz] at hfa; omega
    subst this; exact h.frame0_arena
  closures_arena ca hca := by
    have hsz : initGlobalStore.closures.size = 0 := by decide
    rw [hsz] at hca; omega

end StoreFreshAdvance

/-! ## §2. The marshalling `Ent` — env_new post ⊢ₑ the fresh `StoreSeg` -/

/-- **The fresh-store marshalling entailment.**  `MidPost ⊢ₑ StoreSeg …
initGlobalStore pc1 st0`, where `MidPost` (the caller's `env_new_post`+`sd a0,0(s0)`
readback) exposes on each config the four control pins + the `StoreFreshAdvance` over
its memory.  Fresh-frame analogue of `storeSeg_advance_define`. -/
theorem storeSeg_fresh
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {MidPost : Config → Prop} {pc1 : Nat} {st0 : SpecSt}
    (hFields : ∀ c, MidPost c →
      GoodState c.σ ∧ c.tick < 2 ∧
      c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 pc1) ∧
      StoreFreshAdvance N A φf φc c.σ.mem ∧
      OutRepr c.σ st0) :
    Ent MidPost (StoreSeg N A SL φf φc initGlobalStore pc1 st0) :=
  fun c h =>
    let ⟨hG, htick, hpc, hAdv, hout⟩ := hFields c h
    ⟨hG, htick, hpc, hAdv.toStoreRepr, hout⟩

/-! ## §3. `envNewArmBridge` — the fresh-frame flavor wrapper -/

/-- **The env_new arm bridge.**  From the prologue-and-jal seam `hPre` (into
`env_new`'s precondition `MidPre`), the landed `env_new_spec` callee `hCallee`, and the
fresh-frame readback `hFields` (the `env_new_post`+`sd a0,0(s0)` control pins +
`StoreFreshAdvance`), build the `StoreSeg` seam into the fresh single-global-frame
store carrier.  This is `hPre ≫ hCallee ≫ rmap (storeSeg_fresh hFields)` — the
`envCallArmBridge` template shape, fresh flavor. -/
theorem envNewArmBridge
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {pc1 : Nat} {st0 : SpecSt}
    {P MidPre MidPost : Config → Prop}
    (hPre : Triple P MidPre)
    (hCallee : Triple MidPre MidPost)
    (hFields : ∀ c, MidPost c →
      GoodState c.σ ∧ c.tick < 2 ∧
      c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 pc1) ∧
      StoreFreshAdvance N A φf φc c.σ.mem ∧
      OutRepr c.σ st0) :
    Triple P (StoreSeg N A SL φf φc initGlobalStore pc1 st0) :=
  Triple.seq hPre (Triple.rmap (storeSeg_fresh hFields) hCallee)

/-! ## §4. `interpInitEnvNew_seam` — the `hEnvNew` `InitSeg` seam

`interpInitStore_compose`'s `hEnvNew : Triple P (InitSeg … initGlobalStore 0x80004328)`.
`envNewArmBridge` lands the `StoreSeg … initGlobalStore 0x80004328 initSt` seam; the
`storeSeg_ent_initSeg` `Ent` reindexes the post `StoreSeg → InitSeg`. -/

/-- **The `env_new(NULL)` `InitSeg` seam, via the fresh-frame flavor.**  From the
named prologue-and-jal seam `hPre` (`interp_init` prologue `0x80004308..0x80004320`
≫ `jal env_new` @`0x80004324`, into `env_new`'s precondition `MidPre`), the landed
`env_new_spec` callee `hCallee`, and the fresh-frame readback `hFields` (the post +
`sd a0,0(s0)` control pins + `StoreFreshAdvance`), `envNewArmBridge` builds the
`StoreSeg` seam; `storeSeg_ent_initSeg` reindexes it to the `InitSeg` seam.  This IS
`interpInitStore_compose`'s `hEnvNew` premise — discharged, not assumed. -/
theorem interpInitEnvNew_seam
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {P MidPre MidPost : Config → Prop}
    (hPre : Triple P MidPre)
    (hCallee : Triple MidPre MidPost)
    (hFields : ∀ c, MidPost c →
      GoodState c.σ ∧ c.tick < 2 ∧
      c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 0x80004328) ∧
      StoreFreshAdvance N A φf φc c.σ.mem ∧
      OutRepr c.σ initSt) :
    Triple P (InitSeg N A SL φf φc initGlobalStore 0x80004328) := by
  have hseam : Triple P (StoreSeg N A SL φf φc initGlobalStore 0x80004328 initSt) :=
    envNewArmBridge hPre hCallee hFields
  exact Triple.rmap
    (storeSeg_ent_initSeg N A SL φf φc initGlobalStore 0x80004328)
    hseam

#print axioms StoreFreshAdvance.toStoreRepr
#print axioms storeSeg_fresh
#print axioms envNewArmBridge
#print axioms interpInitEnvNew_seam

end Vsa.Sim
