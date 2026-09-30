import Vsa.Sim.ApproxSeamFold

/-!
# `ApproxDispatchSuppliers` — the concrete-entry supplier pass for `ApproxDispatch` (Task #73)

`Vsa/Sim/ApproxSeamFold.lean` proves the mutual step-lower-bound fold `allLB` for
ANY six abstract entry predicates plus a `ApproxDispatch` bundle of 37 counted-prefix
fields, and lifts it to `approxSeam_of_dispatch` / `divFamily_of_assemblies`.  This
file performs the SUPPLIER pass: it CHOOSES the concrete entries and discharges the
fields that existing machine content supplies, leaving the rest as ONE precisely
named residual structure (`ApproxArmResid`).

## The concrete `SqEntry` (the only entry pinned by the composition boundary)

`approxSeam_of_dispatch`'s `hSqEntry` obligation links the loop-head `SegEntry`
+ `Reflect` to `SqEntry`.  The WEAKEST `SqEntry` making `hSqEntry` DEFINITIONAL is
exactly that pair:

```
SqEntryC Reflect cH st d env ss :=
  ∃ ghosts…, SegEntry ghosts st d dLeft aLeft interpLoopHeadPC m0 cH ∧ Reflect cH env ss
```

So `hSqEntry` is `fun … hSeg hRefl => ⟨…, hSeg, hRefl⟩` — no machine content.  This
is the ONE entry the divergence-family boundary constrains; the other five
(`EEntry`/`AEntry`/`CEntry`/`SEntry`/`FEntry`) are interior landing targets and stay
ABSTRACT parameters (the supplier of the arm classes picks them together with the
arm segs — see the residual).

## The sequence class `seqStep` is supplied FOR FREE by `IterSeamResid`

`ApproxDispatch.seqStep` wants, from `ExecS st d env s st' .normal` and
`SqEntryC cH st d env (s :: ss)`, a `LandedN 1 cH (fun c' => SqEntryC c' st' d env ss)`.
With `SqEntryC = SegEntry + Reflect`, that is EXACTLY the shape
`IterSeamAssembly.iterSeam_of_resid` produces: `∃ m c₁ cH' ghosts', 1 ≤ m ∧
StepsN m cH c₁ ∧ StepsN 0 c₁ cH' ∧ SegEntry ghosts' st' … cH' ∧ Reflect cH' env ss`.
The `StepsN 0 c₁ cH'` collapses `c₁ = cH'`, so this IS `LandedN 1 cH (SqEntryC ss)`.
`seqStep_class` below marshals it with no new machine work — the loop-body span
`iterSeam` already consumes is reused verbatim.

## Why the other 35 fields are a NAMED residual, not "free from segToTripleN"

The brief's design intent — "the weakest entries whose dispatch prefixes genuinely
run: PC + GoodState + GHolds + tick/minstret" — is not attainable as a CLOSED
supplier from the existing segs, for a machine-checked reason recorded in
`experiments/observations.md` (`approxdispatch-entries-cannot-be-weakest-pc-only`):

* Each non-sequence field maps the entry of a COMPOUND term to the entry of a CHILD
  (`binaryL`: `EEntry (.binary op l r)` ⇒ `EEntry l`).  A PC-only entry cannot name
  the child's machine entry PC — it depends on the child NODE ADDRESS, which neither
  the spec term nor a bare PC pin carries.  This is precisely why `DivergeSim.Corr`
  and this file's five interior entries stay ABSTRACT: the node-address ↔ PC map is
  the abstract correspondence.
* The real M4 arm segs (`blockA_binaryArm`, `blockB_binary`, the `ExecDispatchRows`
  sims, `ScaffoldRows`) start from the RICH `EvalEntry`/`ExecEntry` and produce rich
  posts.  Forgetting the post is free (`LandedN` drops it); but the ENTRY they
  consume is a `SegPre`-at-arm-PC (needs `GHolds` pins + `ChainFacts` decode), and
  re-exposing each as a weak-entry→weak-entry `LandedN 1` is a per-SEG-CLASS reseat,
  not a per-field one.

So the honest deliverable is: the 35 non-sequence fields collapse to the SEG CLASSES
they share (all 10 binary-op left/right operands share `blockB_binary`; the unary/
call/args/stmt/for classes similar) and are bundled as `ApproxArmResid` — one field
per field of `ApproxDispatch` for the non-sequence constructors, ∀-closed over the
abstract five entries.  `approxDispatch_of_armResid` assembles the full
`ApproxDispatch` from `ApproxArmResid` + the concrete `seqStep_class` +
`seqHead` (which is itself an arm-class residual: it lands at `SEntry`).  This makes
the capstone `divFamily_of_armResid` a COMPOSING corollary: the whole divergence arm
closes once the arm residual is discharged (per class) upstream.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no `maxHeartbeats` bump.
Axioms of every theorem ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps StepsN)
open Vsa.Logic (TripleN)
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc
open Vsa.Refine (Layout)
open Vsa.While (St Stmt Expr BinOp UnOp Value ClosureData Store Status Addr SApprox EApprox ArgsApprox CApprox FlApprox Approx EvalE EvalArgs ForCond ExecInit ExecStep ExecS)

namespace Vsa.Sim.ApproxDispatchSuppliers

local notation "SpecSt" => Vsa.While.St

/-! ## §1. The concrete `SqEntry`: loop-head `SegEntry` + `Reflect`

The one entry the composition boundary pins.  A machine config `cH` is a valid
sequence entry for `(st, d, env, ss)` iff, for SOME layout ghosts, it satisfies the
loop-head `SegEntry` at `interpLoopHeadPC` for `st` executing at depth `d` and the
abstract `Reflect cH env ss` carries the (non-computational) node fact.  This is a
Prop-valued `∃` over the ghosts (they are DATA — layout maps — so a `structure : Prop`
cannot project them; the sanctioned landing-bundle shape). -/

/-! ## §2. The sequence `seqStep` class — supplied FOR FREE by `IterSeamResid`

`iterSeam_of_resid` produces exactly the `LandedN 1 cH (SqEntryC ss)` shape (its
`StepsN 0 c₁ cH'` collapses the intermediate config).  We marshal it into the
`ApproxDispatch.seqStep` field type.  This is the ONE non-sequence-independent field
that has a landed supplier already in the tree — the loop-body span both `iterSeam`
and this consume. -/

/-! ## §3. `ApproxArmResid` — the 35 non-`seqStep` fields, one per SEG CLASS

Everything `ApproxDispatch` demands EXCEPT the `seqStep` field discharged above.
Bundled as a NAMED-FIELD structure (gate R6/R7 — never a positional `∧` tower over
`ApproxDispatch`) so a supplier discharges it CLASS-BY-CLASS: all 10 binary-op
operand fields share `blockB_binary`; unary/call/args/stmt/for share their arm segs.
∀-closed over the five interior entries (`EEntry`/…/`FEntry`) and `SqEntryC Reflect`
(the callBody/stmtBlock/stmtForInit fields land back at a sequence entry).

Each field's type is COPIED VERBATIM from `ApproxDispatch` (same doc-named supplier),
so `approxDispatch_of_armResid` fills the corresponding `ApproxDispatch` field by
projection.  The `seqHead` field is here too: it lands at `SEntry` (an interior
entry), so it is an arm-class residual, not a sequence-supplied one. -/

/-! ## §4. `approxDispatch_of_armResid` — assemble the full `ApproxDispatch`

The full 37-field `ApproxDispatch` from `ApproxArmResid` (35 fields, projected) +
the concrete `seqStep_class` (from `IterSeamResid`).  `SqEntryC Reflect` is the
concrete sixth entry; the other five stay the abstract parameters `ApproxArmResid`
was closed over. -/

/-! ## §5. The composing capstone — `divFamily_of_armResid`

Threading `approxDispatch_of_armResid` into `ApproxSeamFold.divFamily_of_assemblies`
with the concrete `SqEntryC` and the definitional `hSqEntry` (`sqEntryC_of_seg`).
The `DivFamily L` is closed on: the shared entry drive (`hEntry`), the iter loop-body
assembly (`hIter : IterSeamResid` — which ALSO supplies `seqStep`), and the arm
residual (`R : ApproxArmResid`).  So the WHOLE divergence arm reduces to `hEntry` +
`hIter` + the per-class `ApproxArmResid` — the sequence class is fully discharged,
`seqStep` for free from `hIter`, `hSqEntry` definitional; only the interior-entry arm
classes remain (one supplier per seg class, upstream). -/

end Vsa.Sim.ApproxDispatchSuppliers
