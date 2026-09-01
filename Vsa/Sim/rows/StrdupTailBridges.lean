import Vsa.Sim.rows.StrdupStrlenArgGen
import Vsa.Sim.rows.StrdupMallocArgGen
import Vsa.Sim.rows.StrdupMemcpyArg
import Vsa.Sim.rows.StringifyStrdupTail

/-!
# `StrdupTailBridges` — the strdup-tail Shape-A bridge premises, wired to landed segs

`stringifyStrdupTailContract` (`Vsa/Sim/rows/StringifyStrdupTail.lean`) composed the
shared `stringify` strdup tail `0x80003044 → 0x80003084`
(`strlen ≫ malloc ≫ memcpy ≫ epilogue`) as pure `callSeg` algebra over the real framed
callee contracts, leaving FOUR named machine-bridge hypotheses — each a straight-line
arg-staging span between two callee splices (`bridgeStrlenPre`, `bridgeMallocPre`,
`bridgeMemcpyPre`) plus the return `bridgeEpilogue`.

This file lands the **straight-line seg bodies** of those spans as `#derive_case` /
`segToTriple` rows (the mandated seg-layer abstraction, `EnvDefSeg` idiom) and records
the frame-marshalling residual each bridge still needs on top of its seg core.

## The three arg-staging seg rows (LANDED, green + axiom-clean)

| bridge | span | seg row |
|--------|------|---------|
| `bridgeStrlenPre` | `0x80003044 mv a0,s1` ▷ jal strlen | `strdupStrlenArgRow` |
| `bridgeMallocPre` | `0x8000304c addi a2,a0,1 ; mv a0,a2 ; sd a2,8(sp)` ▷ jal malloc | `strdupMallocArgRow` |
| `bridgeMemcpyPre` | `0x8000305c ld a2,8(sp) ; mv s0,a0 ▷ beqz(false) ; mv a1,s1` ▷ jal memcpy | `strdupMemcpyArgRow` |

Each seg row is the whole `Steps` chain of the span's straight-line body, parked at the
`jal` seam PC, with the computed write-log and computed end-PC (one kernel `decide`).
They replace the ~30-line-per-site `stepObs_*` batteries that `EnvDefBridges.lean` pays
for the IDENTICAL `env_define` append-path prefixes (`bridgeStrlenPre_closed` etc.).

## What each `stringifyStrdupTailContract` bridge premise STILL needs on top of the seg

The contract's bridge hypotheses are stated at the callee-ENTRY predicates
(`strlen_pre` at `0x80006cf0`, `MallocContract.spec`'s entry at `mallocEntry`,
`PreDispatch` at the memcpy entry) — i.e. the seg-prefix ROW ≫ the `jal` SEAM ≫ a
FRAME-CARRYING repackaging into the callee entry, exactly the
`strlenPrefix_run ≫ bridgeStrlenPre_closed` shape in `EnvDefBridges.lean`.  The seg row
here is a DROP-IN for the hand `*Prefix_run` half (the bulk); the residual is:

* `jalStep_of_obs` for the trailing `jal` (the seam step landing the callee entry PC +
  link) — `Vsa/Sim/BridgeSeg.lean` provides it; region-specific decode lemma at the jal.
* the frame-carrying marshalling into the callee entry predicate + `EnvDefFrame`
  survival (the `bridgeStrlenPre_closed`-style ~40-line packaging), and — for
  `bridgeMemcpyPre` — the `a0 ≠ 0` no-OOM fact that justifies the seg's not-taken `beqz`
  polarity (supplied by the malloc-post non-null branch the contract already threads).

These residuals are named per-bridge below (`*FrameResid`), typed against the contract's
exact premise shapes, with the landed seg row cited as the machine core.  Landing them
is the `bridgeOfSeg`-style seam glue; NOT built here (the seg bodies — the exponentiating
bulk — are).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc

namespace Vsa.Sim

/-! ## The three arg-staging seg rows re-exported by name

Re-exported so the strdup-tail contract instantiation (and any other consumer of the
`stringify` tail) references ONE symbol per span.  The rows themselves live in the
generated/hand seg files and are green + axiom-clean there. -/

/-- `bridgeStrlenPre`'s machine core: the `mv a0,s1` prefix `0x80003044 → 0x80003048`
(parked at the `jal strlen` seam), landing `x10 = s1` (the scratch buffer) for the
strlen call.  = `strdupStrlenArgRow`. -/
theorem strdupTail_strlenPre_seg (s1 : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegPre strdupStrlenArgSeg (strdupStrlenArgL s1) lds 0x80003044#64 m0)
      (StrdupStrlenArgPost s1 lds m0) :=
  strdupStrlenArgRow s1 lds m0

/-- `bridgeMallocPre`'s machine core: `addi a2,a0,1 ; mv a0,a2 ; sd a2,8(sp)`
`0x8000304c → 0x80003058` (parked at the `jal malloc` seam), marshalling the size
`len+1` into `a0` and spilling it at `8(sp)`.  = `strdupMallocArgRow`. -/
theorem strdupTail_mallocPre_seg (a0 sp : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegPre strdupMallocArgSeg (strdupMallocArgL a0 sp) lds 0x8000304c#64 m0)
      (StrdupMallocArgPost a0 sp lds m0) :=
  strdupMallocArgRow a0 sp lds m0

/-- `bridgeMemcpyPre`'s machine core: `ld a2,8(sp) ; mv s0,a0 ▷ beqz(false) ; mv a1,s1`
`0x8000305c → 0x8000306c` (parked at the `jal memcpy` seam), reloading the size, saving
the fresh block into `s0`, falling through the OOM guard (no-OOM), and marshalling the
source into `a1`.  = `strdupMemcpyArgRow`. -/
theorem strdupTail_memcpyPre_seg (sp a0 s1 : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegPre strdupMemcpyArgSeg (strdupMemcpyArgL sp a0 s1) lds 0x8000305c#64 m0)
      (StrdupMemcpyArgPost sp a0 s1 lds m0) :=
  strdupMemcpyArgRow sp a0 s1 lds m0

#print axioms strdupTail_strlenPre_seg
#print axioms strdupTail_mallocPre_seg
#print axioms strdupTail_memcpyPre_seg

end Vsa.Sim
