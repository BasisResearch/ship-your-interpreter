import Vsa.Sim.EnvDefCompose
import Vsa.Sim.EnvDefBridges
import Vsa.Sim.EnvNewSpec
import Vsa.Sim.EnvDefSpec4
import Vsa.Sim.ReallocSpec
import Vsa.Sim.ValueSpec
import Vsa.Sim.Code.Env_define
import Vsa.Sim.DecodeTable.Batch02Part27
import Vsa.Sim.DecodeTable.Batch03Part07
import Vsa.Sim.DecodeTable.Batch05Part06
import Vsa.Sim.DecodeTable.Batch02Part08
import Vsa.Sim.DecodeTable.Batch12Part29

/-!
# `EnvDefBridges2` — the grow-path `bridgeCapCompute` machine bridge

`Vsa/Sim/EnvDefCompose.lean`'s `envDefGrowContract` leaves the grow-path prefix as the
named hypothesis `bridgeCapCompute : Triple P (ReallocPre …)` — the cap-compute prefix
`0x80002b90..0x80002ba0`:

```
80002b90  slliw a5,a5,1      -- x15 := 2*cap        (32-bit doubling)
80002b94  slli  a1,a5,3      -- x11 := newcap*8     (the realloc arg n)
80002b98  sw    a5,4(s4)     -- env->cap := newcap  (store into env struct)
80002b9c  mv    a0,s6        -- x10 := s6 = env->names (pOld, the realloc arg p)
80002ba0  jal   realloc      -- x1 := 0x80002ba4, PC := reallocEntry
```

This lands `ReallocPre SL gpv headroom AInv extsN pOld nNew spN 0x80002ba4 mN gN` at the
realloc entry `0x8000527c`.

## Factored abstraction (the exponentiating deliverable)

The `mv rd,rs ; jal callee` tail is the SAME idiom the strlen/malloc prefixes end with
(`EnvDefBridges.strlenPrefix_run`/`mallocPrefix_run`).  `reallocMvJal_run` factors it into
a reusable two-step run keyed on (mv source register, callee entry, link) so this bridge
AND the future `bridgeNamesToVals`/`bridgeAppendHead` realloc calls all instantiate ONE
tail.  The `obs_jal_*`/`frame_*` readbacks are reused verbatim from `EnvNewSpec`.

## Store-memory / AInv threading

The `sw a5,4(s4)` writes `env->cap` — one word inside the caller's live `Env` struct, NOT
inside any allocator extent.  `AInv` (abstract in `ReallocOps`) therefore survives, but no
GENERIC store-frame lemma can exist for an abstract predicate; the survival is carried as
the named typed premise `hAInvStableCap` (the store-analogue of `EnvDefBridges`'s
`hAInvStable`).  The shift-result register values (`newcap = 2*cap`, `nNew = newcap*8`) and
the store-target geometry are supplied by the rich source predicate `GrowCapEntry` — the
dispatch/scan knows `cap` and the `Env` layout, so these are its data, exactly as the
append-path `AppendStrlenEntry` supplies the strlen argument facts.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Site step lemmas for the cap-compute prefix -/

/-! ## The cap-compute prefix run

Chains all five steps `0x80002b90..0x80002ba0`.  From a state at `0x80002b90` with
`x15 = capReg` (the current capacity register), `x20 = s4Ptr` (`env` base), `x22 = s6Ptr`
(`env->names` = `pOld`), runs to a state at `reallocEntry` with:
* `x10 = s6Ptr` (the realloc arg `p`),
* `x11 = newcapx8` where `newcapx8 = (2*cap) <<< 3` (the realloc arg `n`),
* `x1 = 0x80002ba4` (link),
* memory = the input memory with `env->cap` (word at `s4Ptr+4`) overwritten by `newcap`
  (`= writeMap4 … (swData newcap)`),
* every register outside `{x10, x11, x15, x1}` + control preserved (in particular
  `x2`/sp, `x3`/gp and every other callee-saved).

`newcap = sext32(cap[31:0] << 1)`, `newcapx8 = newcap <<< 3` are the concrete machine
shift results; the caller ties them to `ofNat`-forms via `bridgeCapCompute`'s premises. -/

/-! ## `bridgeCapCompute` discharged — FRAME-CARRYING

The grow-path entry predicate `GrowCapEntry` supplies the machine state at `0x80002b90`
(`x15 = cap` register, `x20`/`s4` = `env` base, `x22`/`s6` = `env->names` = `pOld`), the
`sw` store-target geometry, the carried caller-frame `EnvDefFrame`, AND the two
value-tie premises the caller (dispatch/scan) knows from the concrete `cap` value and
`Env` layout:

* `hpTie` : `s6Ptr = ofNat pNamesOld` (the names pointer register holds `pOld`),
* `hnTie` : the machine shift result `(2*cap) <<< 3` equals `ofNat nNamesNew` (`newcap*8`),
* `hmemTie` : the realloc-entry memory `mN` is the post-cap-store memory
  (`writeMap4 m0 capAddr (swData newcap)`).

`bridgeCapCompute_closed` runs `capComputePrefix_run` and repackages the post-state as
`ReallocPre …` at the realloc entry.  The register frame (`sp`/`gp`/callee-saveds)
survives because the prefix writes only `x15`/`x11`/`x10`/`x1`; `AInv` survives the RAM
cap store via the named `hAInvStableCap` (the store-analogue of `EnvDefBridges`'s
`hAInvStable`: mem-agree-off-the-cap-word ∧ gp-agree ⇒ `AInv`). -/

end Vsa.Sim
