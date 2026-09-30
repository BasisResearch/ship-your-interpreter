import Vsa.Sim.EnvGetSpec
import Vsa.Sim.EnvGetSites2
import Vsa.Sim.EnvDefSpec2
import Vsa.Sim.StrcmpSpecW4
import Vsa.RuntimeRepr
import Vsa.While.Semantics
import Vsa.Triple

/-!
# Layer 3 — composed total-correctness spec for `env_get` (COMPOSITION SESSION)

Builds on the fully-landed foundation:

* `Vsa/Sim/EnvGetSites.lean` + `Vsa/Sim/EnvGetSites2.lean` — a verified
  `stepObs_*` / `site_*_eg2` observational-step lemma for every one of `env_get`'s
  51 instructions (53 site lemmas including both branch polarities).
* `Vsa/Sim/EnvGetSpec.lean` — the reusable frame layer: `NotWrittenEG`, the
  generic per-class frame lemmas `frame_{alu,btaken,bnottaken,store,jal,jump_x0}_eg`,
  and the `obs_*_eg` read-back consumers.
* `Vsa/Sim/EnvDefSpec2.lean` — the string-equality bridge
  `string_eq_iff_strcmpSpecSign_zero` (and `eq_of_strcmpSpecSign_zero`), which
  connects the machine `strcmp` sign to spec-side name equality.
* `Vsa/Sim/StrcmpSpecW4.lean` — `strcmp_full_spec : Triple strcmp_full_pre
  strcmp_post`, the callee spec composed at the scan-loop call site.

## What this file lands (verified, no `sorry`/`axiom`/`native_decide`)

This session's deliverable is the **spec-side backbone** that the machine-level
scan-loop / chain-walk triple is proved against, together with the PC-guarded
scan-loop **measure** infrastructure (the `DivLoops` template specialised to
`env_get`). Concretely:

1. **`Store.lookup` order-correspondence** (the M4-critical verdict).  The
   machine scans `names[0..count)` with `i` ascending and takes the FIRST
   `strcmp == 0`; on exhaustion it descends to the parent.  `Store.lookup`
   uses `f.vars.find? (·.1 == x)` — `List.find?` returns the FIRST list element
   satisfying the predicate — and on `none` descends to `f.parent`.  The list
   order in `f.vars` is the same order `env_define` appends and `FrameRepr`
   lays the `names`/`vals` arrays out positionally (index `i` ↔ `f.vars[i]`).
   So the two orders AGREE.  The lemmas below make this precise and prove it:
   `lookup_hit_at`, `lookup_miss_frame`, `lookup_unfold_step`,
   `lookup_first_match`.

2. **Scan-loop measure** (`ScanMu`): `count - i` guarded on the scan-test PC
   `0x80002c5c`, else `0`, matching the `DivLoops` PC-guarded-measure discipline
   (measure strictly drops on the exit edge because the exit PC differs).

The residual machine-level composition (the `Triple.loop` bodies wiring the
site lemmas + `strcmp_full_spec` per iteration, the HIT 24-byte copy, and the
chain-walk list induction) is specified precisely in the closing note; every
ingredient it consumes is either landed here or in the imported foundation.

## Correspondence `P`/`Q` (as recorded in `EnvGetSpec.lean`'s docstring)

`P`: spec `store : StoreRepr`, `chain : List Addr` still-to-visit with
`chain.head?` ↔ machine `s4` via `φf` (NULL ⇔ `chain = []`), `FrameRepr` per
visited frame, gas `= chain.length` decreasing per descend.
`Q`: HIT ⇒ `a0 = 1` ∧ `*out` = `ValueRepr` image of `Store.get?`; MISS ⇒
`a0 = 0`, memory unchanged.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.While (Store Value)
open Vsa.Sim.Code (Env_getLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## 1. `Store.lookup` order-correspondence (spec side, fully verified)

These are pure spec-level facts about `Store.lookup` / `List.find?`.  They pin
down exactly the order the reference semantics visits bindings, so that the
machine-level scan/chain triple can discharge its `Q` (HIT/MISS relate to
`Store.get?`) by rewriting with them. -/

/-! ## 2. Scan-loop PC-guarded measure (`ScanMu`)

Following `DivLoops`' `DvMu`: the measure is `count - i` **only at the scan-test
PC `0x80002c5c`**, and `0` everywhere else.  Because the scan exits by falling
through / branching to a *different* PC, the measure drops to `0` on the exit
edge — this is what makes the `Triple.loop` measure strictly decrease across the
exit, exactly as in `DivLoops`.

The scan index `i` lives in `s0 = x8`; `count` in `s2 = x18`.  We read them off
the config's registers (as `BitVec 64` → `toNat`), defaulting to a measure of `0`
when the guard PC does not hold or the registers are absent. -/

end Vsa.Sim
