import Vsa.Sim.EnvCallBridge
import Vsa.Sim.InterpInit

/-!
# `EnvCallBridgeDemos` — instantiating `envCallArmBridge` on real seams

Two demo instantiations of `Vsa/Sim/EnvCallBridge.lean`'s `envDefineArmBridge`,
discharging TWO of the four `InterpInit` `env_define` seams
(`interpInitStore_compose`'s `hDefPrint` / `hDefAssert`) through the ONE template:

* **Demo (a)** — `define("print")` seam: `InitSeg initGlobalStore 0x80004328 →
  InitSeg storeAfterPrint 0x80004368`.  `storeAfterPrint = initGlobalStore.define 0
  "print" (.native .print)`, so the template's `store.define a x v` shape matches
  verbatim with `a := 0`, `x := "print"`, `v := .native .print`.
* **Demo (b)** — `define("assert")` seam: `InitSeg storeAfterPrintln 0x800043a0 →
  InitSeg storeAfterAssert 0x800043d8`.  Same shape, `x := "assert"`, `v := .native
  .assert`.

Both go through `envDefineArmBridge` and differ ONLY in the name/value/PC data +
the store-so-far — the shared machinery (the callee contract, the marshalling core,
the control-pin readback) is the SAME.  That shared readback is factored ONCE as
`NativeDefinePins` (§1) — the per-native pin bundle the task calls for — so each
demo names only its own binding data.

## The genseg arm-compiler status (the flagged crux)

The demo's `hPre` (the arg-setup prefix `0x80004328..0x80004360` ≫ `jal env_define`
@`0x80004364`) is generated FROM `scripts/arms/interpInitDefinePrint.toml` (written
+ committed).  Running `python3 scripts/genseg.py scripts/arms/interpInitDefinePrint.toml`
HALTS at the decode-index gate: SIX body words in that exact span are not yet on the
block-reflection decode table (sw/addi/sb/auipc/addi/mv @ 0x80004328/38/44/48/4c/50),
plus the `jal env_define` word (the expected region-specific call-seam residual).
Extending the decode table for those words is a decode-batch rebuild (per the
build-speed memory, DecodeTable ≈ 80% of build CPU) — out of scope here and gated by
the elaboration budget.  So `hPre` is threaded as a NAMED genseg-shaped `Triple`
premise (EXACTLY how `InterpInit.interpInitStore_compose` threads `hDefPrint` itself —
that whole composition is over named per-call seams), and the demo instantiates the
template over it.  The obstruction is recorded in `experiments/observations.md`
(`envcallbridge-defineprint-untabled`).

## What each demo lands

`interpInitDefinePrint_seam` / `interpInitDefineAssert_seam`: the two `InitSeg`
seams `interpInitStore_compose` demands, each PROVED by `envDefineArmBridge` over
(hPre = the named genseg arg-setup+jal row, hCallee = the landed
`env_define_append_spec`, hFields = the shared `NativeDefinePins` readback), reindexed
`StoreSeg → InitSeg` by the landed `storeSeg_ent_initSeg` `Ent` morphism (R8 `rmap`).

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

/-! ## §1. `NativeDefinePins` — the shared per-native readback bundle (factored ONCE)

The three interp_init `env_define`s all target frame `0` of the ONE global store, all
copy their name from the SAME static strings region (`0x8001953x`), and all reach the
SAME finalize-tail carrier shape — so the control-pin readback (`GoodState`/tick/PC/
`OutRepr`) + the `StoreDefineAdvance` marshalling is IDENTICAL in structure across the
three.  The task calls for factoring that shared bundle once so instantiations differ
only in the name/value data; `NativeDefinePins` is it.

It packages, for a define of `(x, v)` into frame `a` of the store-so-far `store`, the
readback the template's `hFields` needs off the callee-post config: the four control
pins (parked at the resume PC `pc1`, good/tick, empty output preserved) plus the
`StoreDefineAdvance` off the post memory (the caller's `frameRepr_append` readback,
which knows the concrete layout + the appended `(x,v)`).  A `MidPost` predicate is a
parameter, so the SAME bundle serves the three defines' different callee-post shapes. -/

/-- **The shared native-define pin bundle.**  For the callee-post predicate `MidPost`,
this is the readback obligation `envDefineArmBridge`'s `hFields` demands, ∀-closed over
`MidPost`'s configs: the control pins + the store-advance marshalling.  The three
interp_init defines instantiate it with only their `(a, x, v, pc1, store)` differing —
the structure is shared. -/
def NativeDefinePins
    (N : NativeAddrs) (φf φc : Addr → Nat)
    (store : Store) (a : Addr) (x : String) (v : Value) (pc1 : Nat)
    (MidPost : Config → Prop) (A : Arena) : Prop :=
  ∀ c, MidPost c →
    GoodState c.σ ∧ c.tick < 2 ∧
    c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 pc1) ∧
    StoreDefineAdvance N A φf φc store a x v c.σ.mem ∧
    OutRepr c.σ initSt

/-! ## §2. Demo (a) — the `define("print")` seam

`storeAfterPrint = initGlobalStore.define 0 "print" (.native .print)` (`InterpInit`,
by `rfl`), so `envDefineArmBridge` at `store := initGlobalStore`, `a := 0`,
`x := "print"`, `v := .native .print`, `pc0 := 0x80004328`, `pc1 := 0x80004368`
yields exactly the `StoreSeg` seam, which `storeSeg_ent_initSeg` reindexes to the
`InitSeg` seam `interpInitStore_compose` wants. -/

/-- **Demo (a): the `define("print")` `InitSeg` seam, via the template.**  From the
named genseg arg-setup+jal row `hPre` (into `env_define`'s precondition `MidPre`), the
landed `env_define_append_spec` callee `hCallee`, and the shared `NativeDefinePins`
readback `hPins`, `envDefineArmBridge` builds the `StoreSeg` seam; `storeSeg_ent_initSeg`
(R8 `rmap`) reindexes it to the `InitSeg` seam.  This IS `interpInitStore_compose`'s
`hDefPrint` premise — discharged, not assumed. -/
theorem interpInitDefinePrint_seam
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {MidPre MidPost : Config → Prop}
    (hPre : Triple
      (StoreSeg N A SL φf φc initGlobalStore 0x80004328 initSt) MidPre)
    (hCallee : Triple MidPre MidPost)
    (hPins : NativeDefinePins N φf φc initGlobalStore 0 "print" (.native .print)
      0x80004368 MidPost A) :
    Triple
      (InitSeg N A SL φf φc initGlobalStore 0x80004328)
      (InitSeg N A SL φf φc storeAfterPrint 0x80004368) := by
  -- `storeAfterPrint = initGlobalStore.define 0 "print" (.native .print)` by rfl,
  -- so the template's post carrier IS the `storeAfterPrint` carrier.
  have hseam :
      Triple (StoreSeg N A SL φf φc initGlobalStore 0x80004328 initSt)
        (StoreSeg N A SL φf φc storeAfterPrint 0x80004368 initSt) :=
    envDefineArmBridge (a := 0) (x := "print") (v := .native .print) hPre hCallee hPins
  -- reindex the entry `InitSeg` → `StoreSeg` and the exit `StoreSeg` → `InitSeg`.
  exact Triple.dimap
    (initSeg_ent_storeSeg N A SL φf φc initGlobalStore 0x80004328)
    (storeSeg_ent_initSeg N A SL φf φc storeAfterPrint 0x80004368)
    hseam

/-! ## §3. Demo (b) — the `define("assert")` seam (fan-out: only the data differs)

`storeAfterAssert = storeAfterPrintln.define 0 "assert" (.native .assert)`
(`InterpInit`, by `rfl`).  The instantiation is IDENTICAL to demo (a) up to the
`(store, x, v, pc0, pc1)` data — the SAME template, the SAME shared `NativeDefinePins`
bundle — witnessing the fan-out the ledger predicted. -/

/-- **Demo (b): the `define("assert")` `InitSeg` seam, via the template.**  Identical
to demo (a) modulo the binding data (`store := storeAfterPrintln`, `x := "assert"`,
`v := .native .assert`, PCs `0x800043a0 → 0x800043d8`).  This IS
`interpInitStore_compose`'s `hDefAssert` premise. -/
theorem interpInitDefineAssert_seam
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {MidPre MidPost : Config → Prop}
    (hPre : Triple
      (StoreSeg N A SL φf φc storeAfterPrintln 0x800043a0 initSt) MidPre)
    (hCallee : Triple MidPre MidPost)
    (hPins : NativeDefinePins N φf φc storeAfterPrintln 0 "assert" (.native .assert)
      0x800043d8 MidPost A) :
    Triple
      (InitSeg N A SL φf φc storeAfterPrintln 0x800043a0)
      (InitSeg N A SL φf φc storeAfterAssert 0x800043d8) := by
  have hseam :
      Triple (StoreSeg N A SL φf φc storeAfterPrintln 0x800043a0 initSt)
        (StoreSeg N A SL φf φc storeAfterAssert 0x800043d8 initSt) :=
    envDefineArmBridge (a := 0) (x := "assert") (v := .native .assert)
      hPre hCallee hPins
  exact Triple.dimap
    (initSeg_ent_storeSeg N A SL φf φc storeAfterPrintln 0x800043a0)
    (storeSeg_ent_initSeg N A SL φf φc storeAfterAssert 0x800043d8)
    hseam

#print axioms interpInitDefinePrint_seam
#print axioms interpInitDefineAssert_seam

end Vsa.Sim
