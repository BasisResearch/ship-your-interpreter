import Vsa.Sim.rows.ErrSpillRows
import Vsa.Sim.rows.ErrSetupRows

/-!
# `ErrReachSpan` — the reach-to-`pc0` span combinator (`reachJal_of_span`)

## Where the error family stands (measured, this lane)

The 42 routed `hsite` residuals of `errFamily_of_sites` are ALL discharged down
to the two collectors `ErrArmLinks`/`ErrArmLinksB` (`rows/ErrArmLinks*.lean`).
Each collector field `link_h*` has the shape

```
<spec-error context> → SpillArmPre S m0 L lds <seg> pc0 pcJal b0 b1 b2 b3 c
```

(Family A) or the `SetupArmPre` analogue (Family B).  `SpillArmPre`/`SetupArmPre`
are NOT "`c` reaches `pc0`" — they are **"`c` is parked EXACTLY at the error
block-entry `pc0`"** with the full geometry (`GoodState`, `mem = m0`,
`PC = pc0`, `GHolds L`, `ChainFacts`, `x10 = inp`, the `NotWrittenJmp` ghost
frame, code loaded).  The seg-generic `spill*_toJalErr` / `setup*_toJalErr` then
runs the pure-store / register-setup prefix `pc0 → pcJal` and hands over the
`Triple (SpillArmPre …) (JalErrPre …)` the route consumes.

So the genuinely-open work per site is: **from the interpreter's top-level entry,
under the premise's spec-error derivation, the machine RUNS to a config parked at
`pc0`.**  That is the deep eval/exec-recursion reachability into the specific
error branch — the M4 arm-sim error-edge linkage.  No landed M4 arm-sim yet pins
any of these error edges (`0x800034c0 → 0x800034d0` for `hNegType`, etc.), so
every `link_h*` field is still open (ledger `errlink-forall-shape-obstruction`).

## What THIS file adds — the composition abstraction

`reachJal_of_armBranch` (`rows/ErrorReachInhab.lean`) inhabits `ReachJal … c`
from `ArmBranchPre c` when `ArmBranchPre` is *already* the block-entry predicate
(`c` at `pc0`).  That is the `span := identity` special case.  When an M4 arm-sim
lands a NON-trivial span `Triple SpanPre (SpillArmPre …)` (its precondition
`SpanPre` = a real reachable entry, its post = the block-entry predicate), the
route needs to compose that span with the landed seg into `ReachJal … c`.

`reachJal_of_span` is exactly that composition: `Triple.seq span segToJal`
followed by `ReachJal`'s defeq to `Triple _ (JalErrPre …)`.  It is
relation-agnostic in `SpanPre` and works uniformly for Family A (`SpillArmPre`)
and Family B (`SetupArmPre`), because it only sees the two triples' shared middle
type.  `reachJal_of_armBranch` is recovered as `span := Triple.rfl`.

This is the missing "straight-line/branch span → jal ≫ errSite" combinator.
The residual it leaves is honest and named: the span `Triple SpanPre
(SpillArmPre …)` (an M4 arm's reach-to-`pc0`) — NOT a config already at `pc0`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable Vsa
open Vsa.Machine (MState Config Steps)
open Vsa.Logic (Triple)
open Vsa.While
open Register

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

/-- **The reach-to-`pc0` span combinator.**  From ANY span `spanToBlock : Triple
SpanPre BlockPre` (an M4 arm's run from a reachable entry `SpanPre` to the error
block-entry predicate `BlockPre` — e.g. `SpillArmPre …` / `SetupArmPre …`) and
the landed seg bridge `segToJal : Triple BlockPre (JalErrPre …)`, the
`SitePre`-conditioned residual `ReachJal … c` holds for any `c` with `SpanPre c`.

Unlike `reachJal_of_armBranch` (which needs `c` *at* `pc0`), this admits an
arbitrary reach-to-`pc0` span, so a real M4 arm-sim drops in directly.  Proof:
`Triple.seq` the two triples, then `ReachJal … c` IS `(Triple.seq …) c hspan`
(definitional: `ReachJal … c = ∃ c', Steps c c' ∧ JalErrPre … c'`). -/
theorem reachJal_of_span (S : ErrShared)
    (pcJal : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    {SpanPre BlockPre : Config → Prop}
    (spanToBlock : Triple SpanPre BlockPre)
    (segToJal : Triple BlockPre (JalErrPre S.g S.inp S.m0 pcJal b0 b1 b2 b3))
    (c : Config) (hspan : SpanPre c) :
    ReachJal S.g S.inp S.m0 pcJal b0 b1 b2 b3 c :=
  (Triple.seq spanToBlock segToJal) c hspan

#print axioms reachJal_of_span

/-- **`reachJal_of_armBranch` is the `span := Triple.rfl` case.**  When the span is
the identity (`c` already satisfies the block-entry predicate `BlockPre`),
`reachJal_of_span` degenerates to `reachJal_of_armBranch`.  Machine-checked here
so the general combinator is a genuine strengthening, not a divergent copy. -/
theorem reachJal_of_armBranch_eq_span (S : ErrShared)
    (pcJal : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    {BlockPre : Config → Prop}
    (segToJal : Triple BlockPre (JalErrPre S.g S.inp S.m0 pcJal b0 b1 b2 b3))
    (c : Config) (hblock : BlockPre c) :
    reachJal_of_span S pcJal b0 b1 b2 b3 (Triple.rfl (P := BlockPre)) segToJal c hblock
      = reachJal_of_armBranch S pcJal b0 b1 b2 b3 segToJal c hblock := by
  rfl

#print axioms reachJal_of_armBranch_eq_span

/-! ## Demonstration — a Family-A site closes from a genuine reach-to-`pc0` span

`negTypeReach_of_span` shows the corrected residual for `hNegType`
(jal `0x800034e4`, block-entry `0x800034d0`) closes from a NON-identity span
`Triple SpanPre (SpillArmPre …)` (an M4 arm's run to the spill-block entry) and
the landed `spill800034e4_toJalErr`, under the arm linkage that the `negType`
spec context lands the machine at the span's entry `SpanPre`.  This is the shape
an M4 arm-sim error edge supplies: it reaches `pc0` via a real span, not by
already being there.  Contrast `reachJal_of_armBranch`, which forced the entry
config to be AT `pc0`. -/
theorem negTypeReach_of_span (S : ErrShared) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (L : GRegs) (lds : List (List (BitVec 8)))
    {SpanPre : Config → Prop}
    (spanToBlock : Triple SpanPre
      (SpillArmPre S m0 L lds spill800034e4Seg 0x800034d0#64 0x800034e4#64
        0xef#8 0xf0#8 0x5f#8 0x8c#8))
    (hlink : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt)
      (v : Value),
      EvalE st d env e st' v → (∀ n : Int, v ≠ .int n) → SpanPre c) :
    ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt)
      (v : Value),
      EvalE st d env e st' v → (∀ n : Int, v ≠ .int n) →
      ReachJal S.g S.inp S.m0 0x800034e4#64 0xef#8 0xf0#8 0x5f#8 0x8c#8 c :=
  fun c st d env e st' v hEval hNotInt =>
    reachJal_of_span S 0x800034e4#64 0xef#8 0xf0#8 0x5f#8 0x8c#8
      spanToBlock (spill800034e4_toJalErr S m0 L lds) c
      (hlink c st d env e st' v hEval hNotInt)

#print axioms negTypeReach_of_span

/-- **The full `hNegType` route residual, from a reach-to-`pc0` span.**  Composes
`negTypeReach_of_span` through `route_hNegType` to the routing conclusion
`ErrHalts c`.  This is the drop-in the collector field `A.link_hNegType` becomes
once an M4 arm-sim supplies a span `Triple SpanPre (SpillArmPre …)` plus the
linkage `hlink : negType-context → SpanPre c`. -/
theorem negType_hsite_of_span (S : ErrShared) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (L : GRegs) (lds : List (List (BitVec 8)))
    {SpanPre : Config → Prop}
    (spanToBlock : Triple SpanPre
      (SpillArmPre S m0 L lds spill800034e4Seg 0x800034d0#64 0x800034e4#64
        0xef#8 0xf0#8 0x5f#8 0x8c#8))
    (hlink : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt)
      (v : Value),
      EvalE st d env e st' v → (∀ n : Int, v ≠ .int n) → SpanPre c) :
    ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt)
      (v : Value),
      EvalE st d env e st' v → (∀ n : Int, v ≠ .int n) → ErrHalts c :=
  route_hNegType S (negTypeReach_of_span S m0 L lds spanToBlock hlink)

#print axioms negType_hsite_of_span

end Vsa.Sim
