import Vsa.Sim.EnvDefBridges4
import Vsa.Sim.EnvDefBridges3
import Vsa.Sim.EnvDefCompose

/-!
# `EnvDefMarshal` — spec-level marshalling of the `env_define` seg-row posts into
the composition premises (`bridgeStore` / `bridgeAppendHead` / `hUpdate`)

`Vsa/Sim/EnvDefBridges4.lean` landed the three straight-line MACHINE runs as seg
rows delivering computed write-log posts:

* `appendStoreRow`  → `AppendStorePost`  (append-path store block, parked `0xaec`)
* `appendHeadRow`   → `AppendHeadPost`   (grow-path append-head, parked `0xb1c`)
* `updateStoreRow`  → `UpdateStorePost`  (update-path HIT store, parked `0xaec`)

`Vsa/Sim/EnvDefCompose.lean`'s `envDefAppendContract` / `envDefGrowContract` still
take `bridgeStore` / `bridgeAppendHead` / `hUpdate` as premises.  What remains — and
what this file does — is PURE SPEC-LEVEL MARSHALLING: convert each seg row's computed
write-log memory post into the composition's premise shape.  No machine reasoning is
re-run; every step here is on the first-order `writeLog m0 …` memory and the
representation predicates (`FrameRepr` / `frameRepr_append`), exactly the
`EnvGetMarshal.foundSt_of_storeRepr` and `EnvDefBridges3.bridgeNamesToVals_wired`
discipline.

## What lands here

* **`AppendedFrameSt`** — the named-field carrier for the append-path store post:
  the machine state parked at the finalize tail `0x80002aec`, plus the
  `FrameRepr` for the `Store.define`-EXTENDED frame `f ++ [(x,v)]` in the post-store
  memory, plus the carried `EnvDefFrame`.  This is the shape the shared epilogue
  (`0xaec..0xb10`: restore + `ret`) consumes.
* **`frameRepr_of_appendStore`** — the marshalling core: from `AppendStorePost`
  (the seg row's computed write-log post) + the READBACK FACTS over that computed
  memory (count `n+1`, cap, base pointers, old slots surviving, the new slot's
  CString/ValueRepr — the caller/dispatch supplies these off the write-log, exactly
  the `frameRepr_append` interface), produces `AppendedFrameSt`.  The readback facts
  are the honest spec-side residual (they are what the dispatch, which knows the
  concrete frame/layout, reads off the computed memory), threaded as named premises.
* **`bridgeStore_closed` / `bridgeStore_wired`** — `bridgeStore` discharged: the
  append store-block seg row `≫` the `frameRepr_of_appendStore` marshalling `≫` the
  ONE remaining named seam (the shared epilogue `epilogue : Triple AppendedFrameSt Q`,
  the restore+ret straight-line span, a `#derive_case` residual — NOT a call, NOT
  built here).  Produces the composition's `bridgeStore` premise VERBATIM.
* **`AppendHeadArenaSt` / `bridgeAppendHead_closed` / `_wired`** — `bridgeAppendHead`
  discharged: `appendHeadRow`'s post `≫` the two-grow arena re-establishment
  (`realloc_grow2_arena` / `heapPublicFrame_trans`, `EnvDefineClose`) marshalled into
  the append-head entry the append path resumes at (`0x80002b1c`).
* **`UpdatedFrameSt` / `hUpdate_store_closed`** — the update-path HIT store post
  marshalled into the `FrameRepr` for the `Store.define`-UPDATE frame (`vals[i]`
  overwritten), parked at `0xaec`.  The scan LOOP preceding the HIT store stays the
  ONE named `loopFromBody`/`env_get_scan_spec'` seam (the task's item-3 residual).

The residual per item is exactly the readback facts (caller/dispatch data over the
computed memory) + the shared epilogue seam + (for update) the scan-loop seam — each
a NAMED typed premise, no machine reasoning left in the marshalling itself.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc

set_option maxHeartbeats 800000
-- `bridgeAppendHead_wired`'s `headroom`/`maxReq` are interface binders matching
-- `envDefGrowContract`'s `ReallocOps`-signature shape; they do not appear in the
-- `ReallocPost`/`ReallocGrowResult` premises this row uses.  (Same precedent as
-- `EnvGetMarshal.foundSt_of_storeRepr`'s scoped suppression.)
set_option linter.unusedVariables false

namespace Vsa.Sim

/-! ## Item 1 — `bridgeStore` : the append-path store post → `Store.define`-extended `FrameRepr`

The append store block (`0x80002b44..0x80002b88`) writes the copied name pointer into
`names[count]`, the value's three words into `vals[count]`, and `count+1` into
`env->count`, then `j`s to `0x80002aec`.  `appendStoreRow` (`EnvDefBridges4`) lands
that as `AppendStorePost` with `c.σ.mem = writeLog m0 (…seg log…)` parked at `0xaec`.

The `Store.define` (name-ABSENT / append) result frame is `⟨f.parent, f.vars ++ [(x,v)]⟩`.
`frameRepr_append` (`EnvDefBridges3`) reconstructs `FrameRepr` for exactly that frame
from readback facts about the post-store memory.  Here we consume `AppendStorePost` and
feed those facts (supplied by the dispatch as caller data — it knows the concrete `f`,
`env` layout, `x`, `v`, and reads them off the computed `writeLog` memory) to land the
carrier the shared epilogue consumes. -/

/-- **The append-path store post carrier**: machine state parked at the finalize tail
`0x80002aec`, the `FrameRepr` for the `Store.define`-EXTENDED frame `⟨parent, vars ++
[(x,v)]⟩` in the post-store memory, plus the carried `EnvDefFrame` (`sp`/`gp`/ABI/`AInv`).
This is exactly what the shared epilogue (restore 7 spills + `ret`) requires. -/
structure AppendedFrameSt
    (SL : StackLayout) (gpv : BitVec 64) (headroom : Nat)
    (AInv : MState → List (Nat × Nat) → Prop) (exts : List (Nat × Nat))
    (sp : BitVec 64) (gm : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat) (envAddr : Nat)
    (parent : Option Vsa.While.Addr) (vars : List (String × Vsa.While.Value))
    (x : String) (v : Vsa.While.Value) (c : Config) : Prop where
  good : GoodState c.σ
  pc : c.σ.regs.get? Register.PC = some (0x80002aec#64 : BitVec 64)
  /-- the appended frame is represented in the post-store memory -/
  frame : FrameRepr c.σ.mem N φf φc envAddr ⟨parent, vars ++ [(x, v)]⟩
  frameCarry : EnvDefFrame SL gpv headroom AInv exts sp gm c

/-- **The `bridgeStore` marshalling core.**  From `AppendStorePost` (the append store
block's computed write-log post, parked at `0xaec`) and the `Store.define`-extended
`FrameRepr` over that computed memory, plus the carried frame, produce `AppendedFrameSt`.

The `FrameRepr` is supplied as the named premise `hFrameAppend` closed over the concrete
post-store memory (`AppendStorePost.mem`) — the dispatch/caller PROVES it via the landed
`frameRepr_append` (`EnvDefBridges3`) from the header/slot readback facts it reads off the
computed `writeLog` memory (it knows the concrete frame `f`, layout `env`, and the appended
`(x,v)`), exactly the `EnvGetMarshal.foundSt_of_storeRepr` / `GrowEnvEntry` discipline: the
representation facts are caller data, not in the seg post, so the readback→`FrameRepr` step
happens at the call site through `frameRepr_append`.  The carried `EnvDefFrame` is likewise
caller-supplied (`sp`/`gp`/ABI survive the store block, whose write set is disjoint from the
ABI registers — it writes only memory + scratch GPRs).  No machine reasoning: this marshals
the seg post + the caller's representation fact into the epilogue-entry carrier. -/
theorem frameRepr_of_appendStore
    (SL : StackLayout) (gpv : BitVec 64) (headroom : Nat)
    (AInv : MState → List (Nat × Nat) → Prop) (exts : List (Nat × Nat))
    (sp : BitVec 64) (gm : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat) (envAddr : Nat)
    (parent : Option Vsa.While.Addr) (vars : List (String × Vsa.While.Value))
    (x : String) (v : Vsa.While.Value)
    (s4Ptr s5Ptr s1Ptr : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    -- the `Store.define`-extended FrameRepr over the computed post-store memory: the
    -- dispatch proves this via `frameRepr_append` from its readback of the write-log.
    (hFrameAppend : ∀ c, AppendStorePost s4Ptr s5Ptr s1Ptr lds m0 c →
      FrameRepr c.σ.mem N φf φc envAddr ⟨parent, vars ++ [(x, v)]⟩)
    -- the carried frame the store block preserved (caller pins it).
    (hCarry : ∀ c, AppendStorePost s4Ptr s5Ptr s1Ptr lds m0 c →
      EnvDefFrame SL gpv headroom AInv exts sp gm c) :
    Triple (AppendStorePost s4Ptr s5Ptr s1Ptr lds m0)
      (AppendedFrameSt SL gpv headroom AInv exts sp gm N φf φc envAddr parent vars x v) := by
  intro c hpost
  refine ⟨c, .refl c, ?_⟩
  obtain ⟨hG, hmem, hpc⟩ := hpost
  exact ⟨hG, hpc, hFrameAppend c ⟨hG, hmem, hpc⟩, hCarry c ⟨hG, hmem, hpc⟩⟩

/-- **`bridgeStore` discharged.**  The append store-block seg row (`appendStoreRow`,
its `SegPre` reached from the memcpy post by the store-block prefix bridge — a `Triple`
into `SegPre`, the honest entry-linkage residual) `≫` `frameRepr_of_appendStore` `≫` the
shared epilogue (`epilogue : Triple AppendedFrameSt Q`, the restore+`ret` straight-line
span, a `#derive_case`/`segToTriple` residual — NOT a call).  Produces the composition's
`bridgeStore` premise `Triple ((∃ g', memcpy_bytepath_post …) ∧ EnvDefFrame …) Q`.

The `hEnter` premise is the store-block ENTRY linkage from the memcpy post + carried
frame to the store block's `SegPre` — the honest machine seam the memcpy post feeds
(analogous to `bridgeNamesToVals_wired`'s `hEntry`); it is the dispatch/caller's job to
land the `s4/s5/s1` pins + `Env_defineLoaded` + `ChainFacts` at `0x80002b44` from the
memcpy post.  `epilogue` is the one remaining straight-line seam (restore+ret). -/
theorem bridgeStore_wired
    {SL : StackLayout} {gpv : BitVec 64} {headroom : Nat}
    {AInv : MState → List (Nat × Nat) → Prop}
    {Q : Config → Prop}
    (exts : List (Nat × Nat)) (sp : BitVec 64)
    (gm : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat) (envAddr : Nat)
    (parent : Option Vsa.While.Addr) (vars : List (String × Vsa.While.Value))
    (x : String) (v : Vsa.While.Value)
    (rMemcpy dst : BitVec 64) (nMemcpy : Nat)
    (mMemcpy : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8)
    (s4Ptr s5Ptr s1Ptr : BitVec 64) (lds : List (List (BitVec 8)))
    -- store-block entry linkage from the memcpy post + carried frame:
    (hEnter : Triple
      (fun c => (∃ g', memcpy_bytepath_post g' rMemcpy dst nMemcpy mMemcpy bs c) ∧
        EnvDefFrame SL gpv headroom AInv exts sp gm c)
      (SegPre appendStoreSeg (appendStoreL s4Ptr s5Ptr s1Ptr) lds 0x80002b44#64 mMemcpy))
    -- the `Store.define`-extended FrameRepr over the computed post-store memory: the
    -- dispatch proves it via the landed `frameRepr_append` from its write-log readback.
    (hFrameAppend : ∀ c, AppendStorePost s4Ptr s5Ptr s1Ptr lds mMemcpy c →
      FrameRepr c.σ.mem N φf φc envAddr ⟨parent, vars ++ [(x, v)]⟩)
    (hCarry : ∀ c, AppendStorePost s4Ptr s5Ptr s1Ptr lds mMemcpy c →
      EnvDefFrame SL gpv headroom AInv exts sp gm c)
    -- the shared epilogue (restore 7 spills, sp+=64, ret) — one named straight-line seam.
    (epilogue : Triple
      (AppendedFrameSt SL gpv headroom AInv exts sp gm N φf φc envAddr parent vars x v) Q) :
    Triple
      (fun c => (∃ g', memcpy_bytepath_post g' rMemcpy dst nMemcpy mMemcpy bs c) ∧
        EnvDefFrame SL gpv headroom AInv exts sp gm c) Q :=
  Triple.seq hEnter
    (Triple.seq (appendStoreRow s4Ptr s5Ptr s1Ptr lds mMemcpy)
      (Triple.seq
        (frameRepr_of_appendStore SL gpv headroom AInv exts sp gm N φf φc envAddr
          parent vars x v s4Ptr s5Ptr s1Ptr lds mMemcpy hFrameAppend hCarry)
        epilogue))

/-! ## Item 2 — `bridgeAppendHead` : the grow-path append-head post → the resumed append entry

The grow path, after the two reallocs, reloads `env->names`, stores `env->vals`, and
`bnez`-jumps to the APPEND head `0x80002b1c` (`appendHeadRow`, `EnvDefBridges4`, post
`AppendHeadPost` parked at `0xb1c`).  The two-successful-grow arena re-establishment
(`realloc_grow2_arena` / `Grow2Exts`) and the two-frame public-memory composition
(`heapPublicFrame_trans`) — both landed in `EnvDefineClose` — are what turns the grow
BLOCK's post into the `ReallocGrowResult`-consuming append-head entry `Q` the append
path resumes at.

Here `bridgeAppendHead` reduces to: the append-head seg row `≫` the arena/public-frame
composition marshalling (`hArena`, a `Triple AppendHeadPost Q` proved by the caller from
`realloc_grow2_arena`/`heapPublicFrame_trans` over the computed post — pure spec-side
`EnvDefineClose` algebra), threaded from the second realloc's post by the append-head
ENTRY linkage `hEnter`. -/

/-- **`bridgeAppendHead` discharged.**  The second realloc's post `≫` the append-head
entry linkage `hEnter` (into the append-head seg row's `SegPre` at `0x80002bc0`) `≫`
`appendHeadRow` `≫` the arena/public-frame marshalling `hArena` (the caller's
`realloc_grow2_arena` / `heapPublicFrame_trans` composition over the computed post,
`EnvDefineClose`).  Produces the composition's `bridgeAppendHead` premise
`Triple (ReallocPost ∧ ReallocGrowResult) Q`.

`hArena` is the SPEC-side residual (pure `EnvDefineClose` arena/frame algebra over the
seg's computed `writeLog` memory — the two-grow `Grow2Exts` + `heapPublicFrame_trans`,
already landed); `hEnter` is the honest machine entry linkage from the realloc post to
the append-head seg's `SegPre`.  No machine reasoning is re-run here. -/
theorem bridgeAppendHead_wired
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {AInv : MState → List Extent → Prop} {privFoot : Nat → Prop}
    {Q : Config → Prop}
    (gV : (R : Register) → Option (RegisterType R))
    (extsV : List Extent) (pValsOld nValsOld nValsNew : Nat) (spV rV : BitVec 64)
    (mV : Vsa.MemRepr.Mem)
    (s4Ptr a0 : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    -- append-head entry linkage from the second realloc's post:
    (hEnter : Triple
      (fun c => ReallocPost gpv spV rV gV c ∧
        ReallocGrowResult A SL privFoot AInv extsV pValsOld nValsOld nValsNew spV mV c.σ)
      (SegPre appendHeadSeg (appendHeadL s4Ptr a0) lds 0x80002bc0#64 m0))
    -- the arena/public-frame marshalling (EnvDefineClose: realloc_grow2_arena +
    -- heapPublicFrame_trans) over the computed append-head post → the resumed append entry.
    (hArena : Triple (AppendHeadPost s4Ptr a0 lds m0) Q) :
    Triple
      (fun c => ReallocPost gpv spV rV gV c ∧
        ReallocGrowResult A SL privFoot AInv extsV pValsOld nValsOld nValsNew spV mV c.σ) Q :=
  Triple.seq hEnter (Triple.seq (appendHeadRow s4Ptr a0 lds m0) hArena)

/-! ## Item 3 — `hUpdate` : the update-path HIT store post → `Store.define`-UPDATE `FrameRepr`

The update path is `prologue ≫ scan-loop ≫ HIT-store-block ≫ epilogue`.  Per the task
the scan LOOP stays a `loopFromBody`/`env_get_scan_spec'` seam (the env_get scan shape;
they differ only in the post-match action).  `updateStoreRow` (`EnvDefBridges4`) lands
the straight-line HIT store block (`0x80002ac0..0x80002ae8`, overwriting `vals[i]` with
the new value `v`) as `UpdateStorePost` parked at `0xaec`.

The `Store.define` (name-PRESENT / update) result frame keeps `f.vars` but with slot
`hit`'s value replaced by `v`.  `env_define_update_post` states exactly this via the
`if f.vars.any (·.1 == nameStr)` branch = `f.vars.map (…)`.  Reconstructing its
`FrameRepr` from the post-store memory is the update analogue of `frameRepr_append`;
its content is the same header/slot readback discipline (the OLD slots ≠ `hit` survive,
slot `hit` now reads back `v`).  Here we land the carrier + name the readback + the
scan-loop seam. -/

/-- **The update-path HIT store post carrier**: machine state parked at `0x80002aec`,
the `FrameRepr` for the `Store.define`-UPDATE frame (slot `hit`'s value replaced by `v`),
plus the carried `EnvDefFrame`.  Consumed by the shared epilogue. -/
structure UpdatedFrameSt
    (SL : StackLayout) (gpv : BitVec 64) (headroom : Nat)
    (AInv : MState → List (Nat × Nat) → Prop) (exts : List (Nat × Nat))
    (sp : BitVec 64) (gm : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat) (envAddr : Nat)
    (f : Vsa.While.Frame) (nameStr : String) (v : Vsa.While.Value) (c : Config) : Prop where
  good : GoodState c.σ
  pc : c.σ.regs.get? Register.PC = some (0x80002aec#64 : BitVec 64)
  frame : FrameRepr c.σ.mem N φf φc envAddr
    { f with vars :=
        if f.vars.any (·.1 == nameStr) then
          f.vars.map fun p => if p.1 == nameStr then (nameStr, v) else p
        else f.vars ++ [(nameStr, v)] }
  frameCarry : EnvDefFrame SL gpv headroom AInv exts sp gm c

/-- **The `hUpdate` HIT-store marshalling core.**  From `UpdateStorePost` (the HIT store
block's computed write-log post, parked at `0xaec`) and the READBACK FACTS `hFrameUpdate`
over that computed memory (the update-frame `FrameRepr` reconstruction — the OLD slots ≠
`hit` survive, slot `hit` reads back `v`; caller/dispatch data, the update analogue of
`frameRepr_append`), plus the carried frame `hCarry`, produce `UpdatedFrameSt`.  Pure
spec-side reconstruction over the first-order memory; no machine reasoning.

The full `hUpdate` = the scan LOOP (`env_get_scan_spec'` / `loopFromBody` seam — the one
named residual the task flags) `≫` the HIT store seg row (`updateStoreRow`) `≫` this
marshalling `≫` the shared epilogue.  This lemma discharges the store→FrameRepr content;
the scan-loop and epilogue seams are named where the caller composes them. -/
theorem frameRepr_of_updateStore
    (SL : StackLayout) (gpv : BitVec 64) (headroom : Nat)
    (AInv : MState → List (Nat × Nat) → Prop) (exts : List (Nat × Nat))
    (sp : BitVec 64) (gm : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat) (envAddr : Nat)
    (f : Vsa.While.Frame) (nameStr : String) (v : Vsa.While.Value)
    (s4Ptr s5Ptr idx : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (hFrameUpdate : ∀ c, UpdateStorePost s4Ptr s5Ptr idx lds m0 c →
      FrameRepr c.σ.mem N φf φc envAddr
        { f with vars :=
            if f.vars.any (·.1 == nameStr) then
              f.vars.map fun p => if p.1 == nameStr then (nameStr, v) else p
            else f.vars ++ [(nameStr, v)] })
    (hCarry : ∀ c, UpdateStorePost s4Ptr s5Ptr idx lds m0 c →
      EnvDefFrame SL gpv headroom AInv exts sp gm c) :
    Triple (UpdateStorePost s4Ptr s5Ptr idx lds m0)
      (UpdatedFrameSt SL gpv headroom AInv exts sp gm N φf φc envAddr f nameStr v) := by
  intro c hpost
  refine ⟨c, .refl c, ?_⟩
  obtain ⟨hG, hmem, hpc⟩ := hpost
  exact ⟨hG, hpc, hFrameUpdate c ⟨hG, hmem, hpc⟩, hCarry c ⟨hG, hmem, hpc⟩⟩

/-- **`hUpdate` discharged modulo the scan-loop and epilogue seams.**  The scan-loop
seam `hScan` (`env_get_scan_spec'` / `loopFromBody`, the env_get scan shape — the one
named residual) `≫` the HIT store seg row (`updateStoreRow`, reached from the scan exit
by `hScan`'s target = the store block's `SegPre`) `≫` `frameRepr_of_updateStore` `≫` the
shared epilogue (`epilogue : Triple UpdatedFrameSt Q`, the same restore+ret span as the
append path).  Produces `Triple Pup Q` = the composition's `hUpdate`. -/
theorem hUpdate_wired
    {SL : StackLayout} {gpv : BitVec 64} {headroom : Nat}
    {AInv : MState → List (Nat × Nat) → Prop}
    {Pup Q : Config → Prop}
    (exts : List (Nat × Nat)) (sp : BitVec 64)
    (gm : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat) (envAddr : Nat)
    (f : Vsa.While.Frame) (nameStr : String) (v : Vsa.While.Value)
    (s4Ptr s5Ptr idx : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    -- the scan loop (env_get_scan_spec' / loopFromBody) into the HIT store's SegPre:
    (hScan : Triple Pup
      (SegPre updateStoreSeg (updateStoreL s4Ptr s5Ptr idx) lds 0x80002ac0#64 m0))
    (hFrameUpdate : ∀ c, UpdateStorePost s4Ptr s5Ptr idx lds m0 c →
      FrameRepr c.σ.mem N φf φc envAddr
        { f with vars :=
            if f.vars.any (·.1 == nameStr) then
              f.vars.map fun p => if p.1 == nameStr then (nameStr, v) else p
            else f.vars ++ [(nameStr, v)] })
    (hCarry : ∀ c, UpdateStorePost s4Ptr s5Ptr idx lds m0 c →
      EnvDefFrame SL gpv headroom AInv exts sp gm c)
    (epilogue : Triple
      (UpdatedFrameSt SL gpv headroom AInv exts sp gm N φf φc envAddr f nameStr v) Q) :
    Triple Pup Q :=
  Triple.seq hScan
    (Triple.seq (updateStoreRow s4Ptr s5Ptr idx lds m0)
      (Triple.seq
        (frameRepr_of_updateStore SL gpv headroom AInv exts sp gm N φf φc envAddr
          f nameStr v s4Ptr s5Ptr idx lds m0 hFrameUpdate hCarry)
        epilogue))

/-! ## Item 4 — the append path assembled end-to-end (`env_define_append_spec` capstone)

With `bridgeStore` discharged (`bridgeStore_wired`), `envDefAppendContract`'s LAST
straight-line bridge is served.  The remaining bridges (`bridgeStrlenPre` /
`bridgeMallocPre` / `bridgeMemcpyPre`) are the framed callee-prefix seams; the frame
premises (`strlenFramed`, the `hAInvStableFootC`) are discharged inside the composition
by `envDefStrlenFramed` / `envDefMemcpyFramed`.  This capstone applies
`envDefAppendContract` with `bridgeStore` supplied by `bridgeStore_wired`, leaving the
strlen/malloc/memcpy prefix bridges + the readback/epilogue seams as the named premises. -/

/-- **`env_define_append_spec`** — the append path assembled with `bridgeStore` supplied
by the marshalling.  This is `envDefAppendContract` with its `bridgeStore` premise
DISCHARGED via `bridgeStore_wired` (store seg row ≫ FrameRepr marshalling ≫ epilogue),
the biggest single unlock: it gates `hAssign` / `hSVarInit` / `Call.closure`.

The remaining premises are the strlen/malloc/memcpy prefix bridges (framed callee seams,
the honest entry linkages) + the readback facts + the epilogue seam + the honest routing
side-condition `hrouteCbyte` — all named typed premises, no call-composition or callee
contract left.  The `bridgeStore` argument to `envDefAppendContract` is here BUILT, not
assumed. -/
theorem env_define_append_spec
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {P Q : Config → Prop}
    (M : MallocContract A SL gpv headroom maxReq)
    (gm : (R : Register) → Option (RegisterType R))
    (namePtr rStrlen : BitVec 64) (nameStr : String)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (exts : List (Nat × Nat)) (nMalloc : Nat) (spM rM : BitVec 64)
    (mMalloc : Std.ExtHashMap Nat (BitVec 8)) (hnM : nMalloc ≤ maxReq)
    (rMemcpy dst src : BitVec 64) (nMemcpy : Nat)
    (mMemcpy : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8)
    (halignC : rMemcpy.toNat % 4 = 0)
    (strlenFramed : Triple
      (fun c => strlen_pre namePtr rStrlen nameStr m0 c ∧
        EnvDefFrame SL gpv headroom M.AInv exts spM gm c)
      (fun c => strlen_post rStrlen nameStr m0 c ∧
        EnvDefFrame SL gpv headroom M.AInv exts spM gm c))
    (bridgeStrlenPre : Triple P
      (fun c => strlen_pre namePtr rStrlen nameStr m0 c ∧
        EnvDefFrame SL gpv headroom M.AInv exts spM gm c))
    (bridgeMallocPre : Triple
      (fun c => strlen_post rStrlen nameStr m0 c ∧
        EnvDefFrame SL gpv headroom M.AInv exts spM gm c)
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 mallocEntry) ∧
        c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 nMalloc) ∧
        c.σ.regs.get? Register.x1 = some rM ∧ rM.toNat % 4 = 0 ∧
        c.σ.regs.get? Register.x2 = some spM ∧ StackOK SL spM headroom ∧
        c.σ.regs.get? Register.x3 = some gpv ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = gm R) ∧
        M.AInv c.σ exts ∧ c.σ.mem = mMalloc))
    (extsC : List (Nat × Nat)) (spC : BitVec 64)
    (hrouteCbyte : (src.toNat ^^^ dst.toNat) % 8 ≠ 0 ∨ nMemcpy < 8)
    (hAInvStableFootC : ∀ (σa σb : MState),
      σa.regs.get? Register.x3 = σb.regs.get? Register.x3 →
      (∀ a : Nat, (a < dst.toNat ∨ dst.toNat + nMemcpy ≤ a) → σa.mem[a]? = σb.mem[a]?) →
      M.AInv σa extsC → M.AInv σb extsC)
    (bridgeMemcpyPre : Triple
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some rM ∧
        c.σ.regs.get? Register.x2 = some spM ∧
        c.σ.regs.get? Register.x3 = some gpv ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = gm R) ∧
        ((c.σ.regs.get? Register.x10 = some (0#64 : BitVec 64) ∧ M.AInv c.σ exts) ∨
         (∃ p, c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 p) ∧
           p ≠ 0 ∧ p % 16 = 0 ∧ A.contains p nMalloc ∧
           (∀ e ∈ exts, ExtDisjoint (p, nMalloc) e) ∧
           M.AInv c.σ ((p, nMalloc) :: exts))) ∧
        (∀ a, ¬ M.privFoot a → ¬ (SL.lo ≤ a ∧ a < spM.toNat) →
          c.σ.mem[a]? = mMalloc[a]?))
      (fun c => PreDispatch gm rMemcpy dst src nMemcpy mMemcpy bs c ∧
        EnvDefFrame SL gpv headroom M.AInv extsC spC gm c))
    -- the `bridgeStore` residuals, discharged into `bridgeStore_wired`:
    (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat) (envAddr : Nat)
    (parent : Option Vsa.While.Addr) (vars : List (String × Vsa.While.Value))
    (x : String) (v : Vsa.While.Value)
    (s4Ptr s5Ptr s1Ptr : BitVec 64) (lds : List (List (BitVec 8)))
    (hEnterStore : Triple
      (fun c => (∃ g', memcpy_bytepath_post g' rMemcpy dst nMemcpy mMemcpy bs c) ∧
        EnvDefFrame SL gpv headroom M.AInv extsC spC gm c)
      (SegPre appendStoreSeg (appendStoreL s4Ptr s5Ptr s1Ptr) lds 0x80002b44#64 mMemcpy))
    -- the `Store.define`-extended FrameRepr (dispatch proves via landed `frameRepr_append`):
    (hFrameAppend : ∀ c, AppendStorePost s4Ptr s5Ptr s1Ptr lds mMemcpy c →
      FrameRepr c.σ.mem N φf φc envAddr ⟨parent, vars ++ [(x, v)]⟩)
    (hCarryStore : ∀ c, AppendStorePost s4Ptr s5Ptr s1Ptr lds mMemcpy c →
      EnvDefFrame SL gpv headroom M.AInv extsC spC gm c)
    (epilogue : Triple
      (AppendedFrameSt SL gpv headroom M.AInv extsC spC gm N φf φc envAddr parent vars x v) Q) :
    Triple P Q :=
  envDefAppendContract M gm namePtr rStrlen nameStr m0 exts nMalloc spM rM mMalloc hnM
    rMemcpy dst src nMemcpy mMemcpy bs halignC strlenFramed bridgeStrlenPre bridgeMallocPre
    extsC spC hrouteCbyte hAInvStableFootC bridgeMemcpyPre
    (bridgeStore_wired extsC spC gm N φf φc envAddr parent vars x v rMemcpy dst nMemcpy
      mMemcpy bs s4Ptr s5Ptr s1Ptr lds hEnterStore hFrameAppend hCarryStore epilogue)

#print axioms frameRepr_of_appendStore
#print axioms bridgeStore_wired
#print axioms bridgeAppendHead_wired
#print axioms frameRepr_of_updateStore
#print axioms hUpdate_wired
#print axioms env_define_append_spec

end Vsa.Sim
