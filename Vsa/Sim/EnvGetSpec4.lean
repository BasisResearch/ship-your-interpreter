import Vsa.Sim.EnvGetSpec3
import Vsa.Sim.ObsAvoid

/-!
# Layer 3 — `env_get` scan-loop per-iteration body (`hbody` discharge)

This session's deliverable (task 1 of the continuation): discharge the
per-iteration loop body `hbody` that `env_get_scan_spec` (`EnvGetSpec3`) takes as
a hypothesis, turning the scan-loop `Triple` into an UNCONDITIONAL result
`env_get_scan_spec'`.

The body runs, from the scan-test config (`ScanSt` at `0x80002c5c`) at index
`i < count`:

```
c5c beq s0,s2,cc4   -- NOT taken (i < count ⇒ ofNat i ≠ count)     → c60
c60 ld  a0,0(s1)    -- a0 := names[i] = ofNat qᵢ                     → c64
c64 mv  a1,s3       -- a1 := name                                    → c68
c68 jal strcmp      -- ra := c6c, PC := strcmp entry
    ‹strcmp callee› -- strcmp_full_spec : sign x10 = strcmpSpecSign  → c6c
c6c bnez a0,c54     -- TAKEN  (name ≠ query ⇒ x10 ≠ 0)               → c54  (MISS-iter)
                    -- NOT taken (name = query ⇒ x10 = 0)            → c70  (HIT-in-body)
c54 addi s0,s0,1    -- i := i+1                                      → c58
c58 addi s1,s1,8    -- names += 8                                    → c5c  (AtHead@i+1)
```

Everything the body needs is landed: the 8 site lemmas (`EnvGetSites2`), the
`strcmp_full_spec_cond` callee (`StrcmpSpecW4`), the load↔pointer bridge and index
arithmetic (`EnvGetSpec3`), the equality bridges (`EnvDefSpec2`/`EnvDefSpec3`),
and the `ScanNames` per-binding carrier.  The `strcmp` cross-call is spliced with
the ghost-at-call-site pattern (`g_call := σ_call.regs.get?`, so the callee's
ABI-frame entry is `rfl`), exactly as `env_new_spec` splices `malloc`.

## What this file lands (verified, `sorry`/`axiom`/`native_decide`/`bv_decide`-free)

* `scan_iter` — the per-iteration `Steps` chain from `ScanSt`@c5c (i<count) to the
  disjunctive next config: `ScanSt`@c5c at i+1 with the first-match invariant
  extended (MISS), OR the HIT block `0x80002c70` (HIT-in-body).
* `env_get_scan_body` — `scan_iter` packaged as the `hbody` loop-body `Triple`.
* `env_get_scan_spec'` — `env_get_scan_spec` with `hbody` discharged: the
  UNCONDITIONAL scan-loop disjunctive `Triple`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While (Store Value)
open Vsa.Alloc
open Vsa.Sim.Code (Env_getLoaded StrcmpLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Local `jal` read-back consumers

`EnvGetSpec3`'s import closure (via `Muldi3Spec`/`StepJump`) has `readback` and
`get?_sigmaPost_jal`, but the DivSites2 `post_jal_*`/`obs_jal_*` read-back
consumers are outside it.  We re-derive the two we need (`PC`, `rd`) locally. -/

/-! ## The per-iteration body chain (`scan_iter`)

From a scan-test config (`ScanSt`@`0x80002c5c`) at index `i < count` with the
first-match invariant, one loop body runs to the disjunctive next config:

* MISS-iter: `ScanSt`@`0x80002c5c` at `i+1` with the first-match invariant
  extended to `i+1` (the slot-`i` name differed), OR
* HIT-in-body: the HIT block `0x80002c70` at index `i` with `f.vars[i].1 = nameStr`
  and the first-match invariant (the slot-`i` name matched).

The chain: `c5c`(beq not taken) → `c60`(load `names[i]=ofNat qᵢ`, via `scan_c60_load`)
→ `c64`(`mv a1,s3`) → `c68`(`jal strcmp`, ghost `g' := σ_call.regs.get?`) → `strcmp`
(`strcmp_full_spec_cond`; pre from `ScanNames`) → `c6c`(`bnez a0`): TAKEN (x10≠0 ⇒ names
differ ⇒ MISS-iter after `c54`/`c58`), NOT taken (x10=0 ⇒ names equal ⇒ HIT-in-body). -/

/-! ## The unconditional scan-loop `Triple` (`env_get_scan_spec'`)

`scan_iter` discharges the per-iteration body.  We package it as the `Triple.loop`
body over an EXISTENTIAL-ghost invariant `ScanInvE` (the loop-variant registers
`x8`/`x9` change each iteration, so the ghost tie is re-anchored to the current
reads per iteration — the invariant existentially quantifies the ghost).  `r` is
pinned to the strcmp return address `0x80002c6c` (the scan calls `strcmp` every
iteration, clobbering `x1` to that value). -/

end Vsa.Sim
