import Vsa.Sim.EnvGetSites2
import Vsa.Sim.Muldi3Spec
import Vsa.Sim.StrcmpSpecW4
import Vsa.RuntimeRepr
import Vsa.While.Semantics
import Vsa.Triple

/-!
# Layer 3 — total-correctness spec for `env_get` (WORK IN PROGRESS FOUNDATION)

Config-level (`Vsa.Logic.Triple`) target: a total-correctness triple for
`env_get(env, name, out)` (`c/src/env.c`, entry `0x80002c10`), the M4-critical
`eval_expr` variable lookup.  The per-site observational steps are landed and
verified in `Vsa/Sim/EnvGetSites.lean` (foundation, `_eg`) and
`Vsa/Sim/EnvGetSites2.lean` (this cluster, `_eg2`) — every one of the 51
instructions has a `stepObs_*` lemma.

This file holds the **reusable, fully-verified composition scaffold**: the
blanket ghost-frame predicate `NotWrittenEG`, the generic per-instruction-class
frame lemmas, and the register-disequality helpers.  These are the same shape as
`EnvNewSpec`'s `NotWrittenEnv`/`frame_*_env` (cloned here with the `_eg` suffix,
tracking `env_get`'s written GPR set) and are the pieces every transition in the
eventual scan-loop / chain-walk triple consumes.

## The two-loop structure (design settled — for the next increment)

`env_get` is a nested loop:

* **Scan loop** (`0x80002c54 … 0x80002c6c`, head-test at `0x80002c5c`,
  back-edge `0x80002c6c → 0x80002c54`): linear scan of `names[0..count)`.  Each
  iteration composes `strcmp(names[i], name)` (via `strcmp_full_spec` at
  `StrcmpSpecW4`; the callee P needs `StrcmpLoaded`, `MaskPinned` at the rodata
  the strcmp reads, `CString` on both argument buffers, the `StrcmpRegion`/
  `WRegion` disjointness, and a ghost tie).  The env code then tests the result
  `== 0` via the `bnez a0` at `0x80002c6c` (`site_80002c6c_{taken,nottaken}_eg2`):
  taken (≠0) ⇒ next iteration; not-taken (==0) ⇒ HIT.  Measure = `count - i`,
  PC-guarded per `DivLoops`.

* **Chain-walk loop** (`0x80002cc4 … 0x80002cc8`, back-edge `0x80002cc8 →
  0x80002c40`): descends `env = env->parent` until NULL.  Measure = the
  **spec-side gas** of `Store.lookup` (its fuel is `frames.size`, threaded as a
  decrementing `Nat`; `StoreRepr` has NO acyclicity field — do not look for one).

## The chain-walk correspondence `P` (settled form)

The walker's `P` carries an `EnvRepr`/`StoreRepr` correspondence for the walked
chain: each machine env pointer equals `φf` of a spec frame address whose
`Store.lookup` visits in the same order.  Concretely, the loop invariant threads:

* a spec-side `store : StoreRepr` and a `chain : List Vsa.While.Addr` of the
  frame addresses still to visit, with `chain.head?` corresponding to the current
  machine `s4 = env` pointer through `φf` (NULL ⇔ `chain = []`);
* `FrameRepr store.mem N φf φc (φf a) (store.frames a)` for each visited `a`
  (count@0 read32, names@8 stride 8, vals@16 stride 24, parent@24 — see
  `RuntimeRepr`);
* the gas `= chain.length`, strictly decreasing on each descend, matching
  `Store.lookup`'s `frames.size` fuel.

## `Q` (settled form)

* **HIT**: `a0 = 1`, `*out` (the 24-byte `Value` window at `s5`) equals the
  `ValueRepr`-image of the found `Store.lookup … name` value, memory framed
  outside the `out`-window (pure walker: no allocator, nothing else changes),
  related to `Store.get?` in `Vsa/While/Semantics.lean` exactly.
* **MISS** (through the whole chain): `a0 = 0`, memory unchanged.

`env_set` is structurally identical (HIT stores 24B INTO `vals[i]`; `Q` is a
`writeMap`-described update + `FrameRepr` re-established + `Store.set`
correspondence) and reuses this scaffold with `_es` names.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step)
open Vsa.Sim.Code (Env_getLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Blanket ghost-frame predicate (`NotWrittenEG`) + generic per-class helpers

`env_get`'s straight-line paths write GPRs `x1` (ra), `x2` (sp), `x8` (s0/i),
`x9` (s1/names-ptr), `x10`–`x15` (a0–a5 scratch), `x18`–`x21` (s2–s5).
`NotWrittenEG R` is the disequality conjunction over those written GPRs and the
per-step write-set / tick-set registers, so preservation of every *other*
register is recovered through the blanket ghost-frame conjunct.  (Because
`env_get` clobbers essentially all caller/temp registers it spills, in practice
callers tie only the ABI-preserved set through the spill/restore; this predicate
is the exhaustive machine-level write set used by the internal transitions.) -/

/-! ## Observation read-back consumers (PC / rd / minstret), reusing `readback`

These lift the `sigmaPost_*` field reads to `σ'` through the tick chain, exactly
as the `obs_*` families in `Muldi3Spec`/`ValueSpec` do; provided here specialised
to the read-backs the eventual triple needs. -/

end Vsa.Sim

