import Vsa.Sim.EvalRecCommon
import Vsa.Sim.ExecBlock

/-!
# Layer 4 — `WidenMeta`: ONE parametric exit-widener (the 5-widener zoo unified)

This file collapses the five bespoke exit-wideners — `LeafWiden` (EvalLeafD),
`ExecLeafWiden` (ExecCaseGeom), `ExecRecWiden` (ExecRecRows), `EvalRecWiden`
(CallRows), and the `evalExit_rebase`/`blockD_v_phic` φ-widened epilogue
(CallArmEpilogue) — into ONE relation-agnostic object, per
`experiments/abstraction-tower-design.md` §T1.2.

## What every widener does

Each answers the SAME question: upgrade a bare exit predicate (`EvalExit` /
`ExecExit`) to the motive's `*ExitD` by re-supplying the two clauses `*Exit`
forgets:

* **(a) presence monotonicity** — `MemExtends m0 mem` (`Widen.pres`);
* **(b) `[SL.lo,SL.hi)`-store-survival** — the re-represented `st'.store`, at ONE
  coherent extended φ-pair (`Widen.phiF`/`Widen.phiC`/`Widen.surv`), tolerates
  arbitrary further memory change confined to the survival footprint.

They differ only along three axes, ALL now parameters of `Widen`:

1. **which exit family** — `Eval` vs `Exec`.  `Widen` takes the FULLY-APPLIED
   exit predicate `ExitP : Config → Prop`, so it is relation-agnostic; the two
   family bridges (`evalExitD_of_widen`/`execExitD_of_widen`) marshal into the
   respective `*ExitD`.
2. **φ story** — identity (leaf: the sub-derivation allocates nothing, so the
   supplied `φf'/φc'` are `φf/φc` by `PhiExtends.refl`) vs extends (recursive:
   the sub-derivation grew the store maps, so `φf'/φc'` are genuine extensions).
   Both are the SAME `∃ φf' φc', PhiExtends φf φf' nf ∧ PhiExtends φc φc' nc ∧ …`
   shape — leaves witness it at `refl`.
3. **survival footprint** — a `Nat → Prop` predicate `foot` (the FrameMeta
   `memFrame` style): spill-only `[SL.lo,SL.hi)` for the leaves and the rec exits;
   `[SL.lo,SL.hi) ∪ [aRet,aRet+24)` for the retslot-writing statement cases
   (retNull/varNull).  A `Widen` at ANY footprint `foot ⊇ [SL.lo,SL.hi)`
   discharges the footprint-fixed `*ExitD` survival clause (`Widen.footMono`).

## Elaboration story

`Widen` is a projected named-field `structure … : Prop where` (R6/R7 gate: no
positional `.2`-towers); the bridges are term-level record reshapes.  No whnf of
Sail state — everything is stated on `MemExtends`/`StoreRepr` presence and the
`PhiExtends`/`≤` reindexing the sub-derivations already carry.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc

namespace Vsa.Sim

/-! ## `stackFoot` — the canonical `[SL.lo,SL.hi)` survival footprint

The footprint every leaf/rec widener uses.  Named so callers reference it by name
rather than re-inlining the interval, and so `footMono` proofs are `fun _ h => h`. -/

/-! ## `Widen` — the ONE parametric exit-widener

For ANY config `c` satisfying the fully-applied exit predicate `ExitP`, yields the
two `*ExitD` upgrade clauses about `c`: presence monotonicity and the survival of
`st'.store` at one extended φ-pair over the footprint `foot`.  This is TRUE of
every leaf/recursive exit (the memory delta is a `writeMap` chain over `m0` —
presence-preserving — and the store footprint is disjoint from `foot`), and is the
honest re-supply of what `*Exit` forgets; the recursor's minor premise provides
it.  `ExitP` is fully applied, so `Widen` is relation-agnostic (Eval/Exec). -/

/-! ## The two family bridges — `Widen` at `stackFoot SL` → `*ExitD`

Both `EvalExitD` and `ExecExitD` are `*Exit ∧ MemExtends m0 mem ∧ ∃ φf' φc',
PhiExtends φf φf' nf ∧ PhiExtends φc φc' nc ∧ (survival at `[SL.lo,SL.hi)`)`.
Given the row's own `*Exit … c` and a `Widen` at `stackFoot SL`, the bridge is a
term-level record reshape — no new machine content. -/

end Vsa.Sim
