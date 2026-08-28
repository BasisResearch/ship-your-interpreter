import Vsa.Sim.ErrorSiteRows
import Vsa.Sim.DeriveErrorSite

/-!
# `ErrorSiteApplied` — the `T` hypothesis DISCHARGED on a live error-site row (L6)

Every landed error-site row (`ErrorSiteRows`, `ErrorSiteRows2`) takes its per-site
machine `Triple`

```
T : Triple SitePre (fun c' => RuntimeErrorAt g inp m0 c')
```

as a HYPOTHESIS — the ~200-line bespoke jal→`RuntimeErrorAt` marshalling was never
executed; it was assumed.  The v2 metaprogram layer
(`experiments/exponentiation-endgame-design.md`, Shape B) changed that: the
`#derive_error_site` command in `DeriveErrorSite.lean` PROVES such a `T`
UNCONDITIONALLY for the real `jal runtime_error @ 0x800034e4` site, as

```
Vsa.Sim.errSite_800034e4 :
  ∀ g inp m0, Triple (JalErrPre g inp m0 0x800034e4#64 0xef#8 0xf0#8 0x5f#8 0x8c#8)
                     (fun c' => RuntimeErrorAt g inp m0 c')
```

This file APPLIES that generated `Triple` to a live error-site row.
`row_hNegType_applied` below has the EXACT `∀`-closure conclusion of the
`EvalErr.negType` row (`row_hNegType` in `ErrorSiteRows.lean`), the leaf whose
`jal runtime_error` site IS `0x800034e4` — so the generated `Triple`'s
precondition `JalErrPre g inp m0 0x800034e4#64 …` matches the row's `SitePre`.

The DIFFERENCE from `row_hNegType`: the `T` argument is NO LONGER a hypothesis.
`SitePre` is pinned to `JalErrPre g inp m0 0x800034e4#64 0xef#8 0xf0#8 0x5f#8 0x8c#8`,
and `errRow`'s `T` slot is supplied internally by `errSite_800034e4 g inp m0`.
This converts the row from a conditional residual (assuming its per-site machine
`Triple`) into one whose per-site `Triple` is genuinely PROVED on live code.

## What is discharged vs. what residuals remain

* **DISCHARGED** (no longer a hypothesis): the per-site machine
  `Triple SitePre (RuntimeErrorAt g inp m0)` — supplied by the generated
  `errSite_800034e4`, itself proved unconditionally by `#derive_error_site` from
  the site's decode data (no `sorry`/`axiom`).
* **REMAINING residuals** (still hypotheses, as in every Wave-D row): the shared
  L7/L8 facts `SC : SnprintfContract …` and `out`/`HT : ErrorTailChain …` (the
  SAME two for all 42 sites), and the reachability link
  `hsite : JalErrPre g inp m0 0x800034e4#64 … c` (the M4-side caller linkage that
  the fixed interpreter config `c` is parked at this error node's `jal`).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable Vsa
open Vsa.Machine (MState Config Steps Halts)
open Vsa.Logic (Triple)
open Vsa.While
open Register

namespace Vsa.Sim

/-- The WHILE spec state (`Vsa.While.St`), qualified to avoid the clash with the
`Vsa.Sim.St` register-bundle structure in scope. -/
local notation "SpecSt" => Vsa.While.St

/-- **`EvalErr.negType` row with its per-site `Triple` DISCHARGED.**

Identical `∀`-closure conclusion to `row_hNegType` (`ErrorSiteRows.lean`) — the
exact `errorSimFull` minor-premise shape — but the `T` argument is GONE from the
hypothesis list.  Instead `SitePre` is instantiated to
`JalErrPre g inp m0 0x800034e4#64 0xef#8 0xf0#8 0x5f#8 0x8c#8` and `errRow`'s `T`
slot is supplied by the generated `errSite_800034e4 g inp m0` (proved
unconditionally by `#derive_error_site`, `DeriveErrorSite.lean`).

Remaining hypotheses: the shared L7/L8 `SC`/`out`/`HT`, and the reachability link
`hsite : JalErrPre g inp m0 0x800034e4#64 … c`. -/
theorem row_hNegType_applied
    (g : (R : Register) → Option (RegisterType R)) (inp : BitVec 64)
    (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (SC : SnprintfContract g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0)
    (out : String) (HT : ErrorTailChain ra0 ExitStorePreExit out)
    (c : Config)
    (hsite : JalErrPre g inp m0 0x800034e4#64 0xef#8 0xf0#8 0x5f#8 0x8c#8 c) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value),
      EvalE st d env e st' v → (∀ n : Int, v ≠ .int n) → ErrHalts c :=
  fun _ _ _ _ _ _ _ _ =>
    errRow g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0
      SC out HT
      (SitePre := JalErrPre g inp m0 0x800034e4#64 0xef#8 0xf0#8 0x5f#8 0x8c#8)
      (errSite_800034e4 g inp m0) c hsite

#print axioms row_hNegType_applied

end Vsa.Sim
