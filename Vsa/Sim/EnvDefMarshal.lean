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

/-! ## Item 4 — the append path assembled end-to-end (`env_define_append_spec` capstone)

With `bridgeStore` discharged (`bridgeStore_wired`), `envDefAppendContract`'s LAST
straight-line bridge is served.  The remaining bridges (`bridgeStrlenPre` /
`bridgeMallocPre` / `bridgeMemcpyPre`) are the framed callee-prefix seams; the frame
premises (`strlenFramed`, the `hAInvStableFootC`) are discharged inside the composition
by `envDefStrlenFramed` / `envDefMemcpyFramed`.  This capstone applies
`envDefAppendContract` with `bridgeStore` supplied by `bridgeStore_wired`, leaving the
strlen/malloc/memcpy prefix bridges + the readback/epilogue seams as the named premises. -/

end Vsa.Sim
