import Vsa.Sim.ErrorSiteJal

/-!
# `ErrorReach` — the `SitePre`-conditioned reachability residual for error routing (L6)

## The obstruction this replaces

The generated error-routing wrappers (`rows/ErrorRouting.lean`) previously demanded,
per `jal runtime_error` site, an **unconditional universal**

```
hsite : ∀ c : Config, JalErrPre S.g S.inp S.m0 <pc> <bytes> c
```

claiming EVERY config `c` is already parked at that site's `jal runtime_error`.  That
proposition is machine-checked FALSE (`Vsa/Sim/rows/ErrLinkObstruction.lean :
jalErrPre_forall_false`: a config with `tick := 2` violates `JalErrPre`'s `tick < 2`).
The route emitted it because it DISCARDED each error premise's spec-derivation data
(`fun c _ _ … =>`) and fed `errRow`'s `hsite : SitePre c` at an arbitrary `c`.

## What `errRow` actually requires

`errRow … (SitePre := P) (T : Triple P (RuntimeErrorAt …)) c (hsite : P c) : ErrHalts c`
is polymorphic in `SitePre`.  Reading `errFamily_of_sites` (`InterpSimBundle.lean`),
the config `c` is the **top-level entry config**, bound once and threaded into every
premise as `(hVarUndef c)`; the premise carries the spec error-derivation as
hypotheses but NO machine facts.  So the honest, inhabitable requirement is not
"`c` is at the jal" but "`c` REACHES the jal": pick

```
SitePre := ReachJal S pc b0 b1 b2 b3
         := fun c => ∃ c', Steps c c' ∧ JalErrPre S.g S.inp S.m0 pc b0 b1 b2 b3 c'
```

Then `T := Triple.seq (reachJal_triple …) (errSite_<pc> …)` and the residual becomes
`hsite : ReachJal … c`, i.e. **reachability from the entry config into the site's
`jal`** — conditioned, in the route, on the retained spec-derivation binders.

`ReachJal` is genuinely inhabitable (unlike the old universal): from an arm-branch
entry context one exhibits the concrete `c'` parked at the jal (`Steps` via a
`#derive_case` error-branch seg, then the seg's post IS `JalErrPre`).  See
`ErrorReachInhab.lean` for the machine-checked demonstration on one class.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable Vsa
open Vsa.Machine (MState Config Steps)
open Vsa.Logic (Triple)
open Register

namespace Vsa.Sim

/-- **The `SitePre`-conditioned reachability residual.**  Config `c` (the top-level
entry config) *reaches* a config `c'` parked at the site's `jal runtime_error`
(`JalErrPre …`).  This is the corrected, inhabitable shape of the per-route error
residual: not "`c` is at the jal" (the refuted universal) but "`c` runs to the jal". -/
def ReachJal (g : (R : Register) → Option (RegisterType R))
    (inp : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (pcJal : BitVec 64) (b0 b1 b2 b3 : BitVec 8) (c : Config) : Prop :=
  ∃ c', Steps c c' ∧ JalErrPre g inp m0 pcJal b0 b1 b2 b3 c'

/-- **`ReachJal` is a triple into `JalErrPre`.**  The zero-extra-content step: the
existential witness `c'` with its `Steps c c'` IS the run, and its `JalErrPre c'` IS
the post.  So `Triple.seq reachJal_triple (errSite_<pc> …)` gives a
`Triple (ReachJal …) (RuntimeErrorAt …)` — exactly the `T` `errRow` consumes with
`SitePre := ReachJal …`. -/
theorem reachJal_triple (g : (R : Register) → Option (RegisterType R))
    (inp : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (pcJal : BitVec 64) (b0 b1 b2 b3 : BitVec 8) :
    Triple (ReachJal g inp m0 pcJal b0 b1 b2 b3)
      (JalErrPre g inp m0 pcJal b0 b1 b2 b3) :=
  fun _ ⟨c', hsteps, hjal⟩ => ⟨c', hsteps, hjal⟩

end Vsa.Sim
