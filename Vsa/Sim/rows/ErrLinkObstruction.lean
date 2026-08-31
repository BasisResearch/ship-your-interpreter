import Vsa.Sim.ErrorSiteJal

/-!
# `ErrLinkObstruction` — the machine-checked witness that FORCED the routing fix

**HISTORICAL.**  This file records the obstruction that was diagnosed and then
FIXED (2026-08-31, `errlink-forall-shape-obstruction`).  The generated error
routing (`ErrorRouting.lean`, `ErrorRoutingClasses.lean`) previously demanded, per
`jal runtime_error` site, an **unconditional universal**

```
hsite / hlink_<pc> : ∀ c : Config, JalErrPre S.g S.inp S.m0 <pc> <bytes> c
```

— every config `c` is *already* parked at the site's `jal runtime_error` (PC
`= pcJal`, `x10 = inp`, `mem = m0`, `tick < 2`, …).  That proposition is **false**:
pick any config not so parked (e.g. `tick := 2`).  The `genseg`/arm machinery
produces a `Triple SitePre (JalErrPre …)` = the *implication* `∀ c, SitePre c → …`,
a DIFFERENT shape, so no seg/arm/bridge could inhabit the bare universal.

`jalErrPre_forall_false` below is the machine-checked refutation (Law 4).  It
drove the corrected residual now emitted by `scripts/gen_m5_error_routing.py`:
the route KEEPS each premise's spec-derivation context and demands the
`SitePre`-conditioned reachability

```
hsite : ∀ c <spec-binders>, <spec-hyps> → ReachJal S.g S.inp S.m0 <pc> <bytes> c
```

where `ReachJal … c := ∃ c', Steps c c' ∧ JalErrPre … c'` (`ErrorReach.lean`) —
the entry config `c` RUNS to the jal, an inhabitable claim (demonstrated in
`ErrorReachInhab.lean`).  This witness is retained as the record of why the shape
changed; it refutes only the OLD (now-removed) universal.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable Vsa
open Vsa.Machine (MState Config Steps)
open Register

namespace Vsa.Sim

/-- **The obstruction, machine-checked.**  For ANY site parameters, the field
shape `∀ c : Config, JalErrPre g inp m0 pcJal b0 b1 b2 b3 c` is refutable: the
config obtained from any `σ` with `tick := 2` violates `JalErrPre`'s `tick < 2`
conjunct.  Hence no `hlink_<pc>` field is provable, and no `Triple`-shaped genseg
arm (whose type is `∀ c, SitePre c → …`) can have this type.  The genuine
residual is `SitePre`-conditioned reachability, not this universal. -/
theorem jalErrPre_forall_false
    (g : (R : Register) → Option (RegisterType R))
    (inp : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (pcJal : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (σ : MState) :
    ¬ (∀ c : Config, JalErrPre g inp m0 pcJal b0 b1 b2 b3 c) := by
  intro h
  -- Instantiate the universal at a config with `tick = 2`; the `tick < 2`
  -- conjunct of `JalErrPre` then reads `2 < 2`, absurd.  Destructure by name
  -- (no positional `.2.2…` navigation).
  obtain ⟨_hG, _hRE, _hLJ, _hmem, _hpc, _hx10, _hwin, _hminstret, htick, _hframe,
    _hb0, _hb1, _hb2, _hb3⟩ := h ⟨σ, 2, 0⟩
  have : (2 : Nat) < 2 := htick
  exact absurd this (by decide)

#print axioms jalErrPre_forall_false

end Vsa.Sim
