import Vsa.Sim.InterpRunLoopSeamsClose
import Vsa.Sim.StepCount
import Vsa.Sim.rows.LoopHeadDispatch
import Vsa.Sim.IterSeamAssembly

/-!
# `approxSeamFold` — the mutual step-lower-bound family for `approxSeam` (wave 27)

This file closes the LAST divergence-family field,
`InterpRunLoopSeamsClose.InterpRunLoopResiduals.approxSeam`.

`approxSeam` takes a loop-head `SegEntry`, `Reflect cH env (s :: ss)`, and a
still-running head `SApprox n st d env s`, and must conclude
`∃ m c₁, n + 1 ≤ m ∧ StepsN m cH c₁` — a bare machine-step LOWER BOUND, NOT a
re-landing (a diverging head never returns to the loop head, so — unlike
`iterSeam` — only the count survives; this is exactly the `LandedN (n+1) cH
(fun _ => True)` shape of `StepCount.lean` and `approxFromCountedRun`).

## Why a single parametric fold is impossible, and what the honest shape is

`SApprox` is one of a SIX-relation entangled bounded-progress family
(`EApprox`/`ArgsApprox`/`CApprox`/`SApprox`/`FlApprox` — the mutual block,
`Vsa/While/ErrorSem.lean:345-523` — PLUS `Approx`, the sequence relation, a
SEPARATE inductive at `:532` that `SApprox.block`/`forInit` and `CApprox.body`
recurse INTO and `Approx.head` recurses back OUT of).  Its 37 constructors recurse
through `EvalE`/`ExecS`/`EvalArgs`/`ForCond`/`ExecInit`/`ExecStep`, EACH at its own
machine entry geometry (a sub-expression `eval_expr` entry, an inner loop body, a
callee body at `d + 1`).  So the lower bound cannot be a single motive pinned at
the loop head: the argument demands the SIX sub-relation entry predicates.

The honest shape (this file) is therefore a **mutual step-lower-bound family**:
six `…LB` predicates, one per relation, each saying "this relation, still running
with fuel `n`, forces `≥ n` machine steps FROM ANY VALID ENTRY config for it"
(`Divg n c := ∃ m c₁, n ≤ m ∧ StepsN m c c₁`).  The six entry predicates are
ABSTRACTED as parameters (`EEntry`/`AEntry`/`CEntry`/`SEntry`/`FEntry`/`SqEntry`)
— the WEAKEST-possible entry each relation's dispatch prefix genuinely runs from —
kept opaque exactly as `DivergeSim.Corr` / the section `Reflect` keeps the machine
correspondence abstract.  The per-constructor machine content (the counted
dispatch prefix at each entry, and the linkage from a constructor to its
sub-relation's entry) is bundled into ONE named-field `structure ApproxDispatch`
— one field per CONSTRUCTOR CLASS (the kind-generic arm shapes: `binaryL`/
`binaryR`/`logicalL`/`logicalR`/`callArgs`/`callC`/…), whose enclosing side is the
abstract entry applied to the COMPOUND term and whose landing is the sub-entry
applied to the recursive premise's child (no auxiliary linkage predicates needed).

`allLB` proves all six `…LB` predicates by ONE STRONG INDUCTION on the shared fuel
`n` — NOT the per-inductive mutual recursor, which cannot span the `Approx`-vs-
mutual-block declaration boundary.  Every constructor's conclusion is at fuel
`n + 1` and its recursive premise at fuel `n` (or the same `n` for the
`while`/`for`/`loop` self-recursions), so all recursion is at fuel `< n + 1` and
the strong-induction IH covers all six at every `m ≤ n`.  Each case is exactly ONE
`divg_step` (a `LandedN.bind` from `StepCount.lean`): the matching `ApproxDispatch`
field supplies the ≥ 1-step dispatch prefix (`LandedN 1 c sub-entry`), the IH
supplies the `Divg` from the sub-entry, composing to `Divg (n + 1)`.  The `zero`
cases are `Divg 0` — the empty run.

Each `…LB` predicate is `Prop`-valued and quantifies the entry config, so the
strong induction carries the entry linkage through (design decision 3 of the
task): where a constructor needs a fact about the sub-machine-entry it cannot
cheaply derive, the fact lives inside the `ApproxDispatch` field that supplies
that class's prefix, `∀`-quantified over the entry, discharged when the supplier
BUILDS the field from the real M4 entries.

## `approxSeam` from the family

The loop head is a SEQUENCE position (executing `s :: ss`), not a bare statement
position, so `approxSeam_of_dispatch` lifts the still-running head
`SApprox n st d env s` to `Approx (n + 1) st d env (s :: ss)` via `Approx.head`,
then applies the `ApproxLB` projection at the loop-head `SqEntry` to get
`Divg (n + 1) cH = ∃ m c₁, n + 1 ≤ m ∧ StepsN m cH c₁` — exactly the `approxSeam`
conclusion.  The supplier need only instantiate `SqEntry` at the loop-head
`SegEntry` + `Reflect` (the `hSqEntry` obligation, whose supplier is
`loopHeadDispatch_span` — the SAME span `iterSeam` consumes).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no `maxHeartbeats`
bump.  Axioms of every theorem ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps StepsN)
open Vsa.Logic (TripleN)
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc
open Vsa.Refine (Layout)
open Vsa.While (St Stmt Expr BinOp UnOp Value ClosureData Store Status Addr EvalE EvalArgs ForCond ExecInit ExecStep ExecS)

namespace Vsa.Sim.ApproxSeamFold

local notation "SpecSt" => Vsa.While.St

/-! ## §0. Five of the six abstract entry predicates and the reusable landing shape

Each relation runs its dispatch prefix from its own machine entry.  We keep the
entries ABSTRACT (parameters), so the family below is a pure step-count argument
that a supplier instantiates with the real M4 entry predicates
(`EvalEntry`/`ExecEntry`/…) later.  These five are the eval/args/callee/stmt/for
entries; the sixth (`SqEntry`, for the sequence relation `Approx`) is introduced
in §1.  `Divg k c := ∃ m c₁, k ≤ m ∧ StepsN m c c₁` is the shared lower-bound
shape (`= LandedN k c (fun _ => True)`, `StepCount`): "from `c`, ≥ k machine steps
exist".  It is exactly the `approxFromCountedRun` input, and `LandedN.bind`
composes a dispatch prefix with an IH. -/

variable
  (EEntry : Config → SpecSt → Nat → Addr → Expr → Prop)
  (AEntry : Config → SpecSt → Nat → Addr → List Expr → Prop)
  (CEntry : Config → SpecSt → Nat → Value → List Value → Prop)
  (SEntry : Config → SpecSt → Nat → Addr → Stmt → Prop)
  (FEntry : Config → SpecSt → Nat → Addr → Option Expr → Option Expr → Stmt → Prop)

/-! ## §1. The sixth entry: the sequence relation `Approx`

`Approx` (`Vsa/While/ErrorSem.lean:532`) is a SEPARATE inductive from the mutual
`SApprox`/…/`FlApprox` block, yet it is mutually entangled with it:
`SApprox.block`/`forInit` and `CApprox.body` recurse INTO `Approx`, and
`Approx.head` recurses back into `SApprox`.  Lean's mutual recursor spans only the
5-family; `Approx` is outside it.  We therefore prove ALL SIX lower bounds by ONE
strong induction on the shared fuel `n` (every constructor's recursive premise has
fuel `≤ n` when the conclusion has fuel `n + 1` — see §3), which crosses the
declaration boundary cleanly.  `SqEntry` is the sixth abstract entry (for
`Approx`, the interp_run / `ExecSeq` sequence head). -/

variable
  (SqEntry : Config → SpecSt → Nat → Addr → List Stmt → Prop)

/-! ## §2. The per-constructor-class dispatch obligations

`ApproxDispatch` bundles, as named-field providers (gate R6/R7 — one field per
CONSTRUCTOR CLASS, never a positional tower), the machine content the fold cannot
derive: for each arm shape, the counted dispatch prefix that runs ≥ 1 step from a
config satisfying the ENCLOSING relation's entry (`EEntry`/`SEntry`/… applied to
the COMPOUND term) to a config satisfying the SUB-relation's entry (applied to the
recursive premise's term).  Each field is a `LandedN 1 c (sub-entry)`-producer —
the shape `divg_step` consumes — quantified over the entry config, so the strong
induction carries the entry linkage through (task design decision 3: any fact
about the sub-entry a constructor cannot cheaply derive lives inside its class
field, `∀`-closed over the entry, discharged when the supplier BUILDS the field
from the real M4 entries).

No auxiliary linkage predicates are needed: the enclosing entry is just the
abstract entry applied to the compound term (`EEntry c st d env (.binary op l r)`
etc.), and the sub-entry is the abstract entry applied to the child.  This
collapses the 35 constructors to the kind-generic arm shapes already proved in the
M4 stack (`BinArmBridge`, `blockB_binary`, `ExecDispatchRows`,
`loopHeadDispatch_span`), one field per shape.  Every field's non-recursive
side-conditions (the completed `EvalE`/`EvalArgs`/`ForCond`/… premises) are
carried verbatim so the supplier knows exactly which post-state the sub-entry sits
at. -/

/-! ## §3. The six lower-bound predicates and the mutual fold

Each `…LB n …` says: for EVERY config `c` that is a valid entry for this relation
instance, `Divg (n + 1) c` (≥ n+1 machine steps).  The six are proved together by
STRONG INDUCTION on the shared fuel `n`: every constructor's conclusion is at fuel
`n + 1` and its recursive premise is at fuel `n` (or the sub-relation carries the
same `n`), so all recursion is at fuel `≤ n`, and the strong-induction IH covers
all six at every `m ≤ n`.  This crosses the `Approx`-vs-mutual-block declaration
boundary that Lean's per-inductive recursor cannot (see §1). -/

/-! ## §4. The fold — all six lower bounds by strong induction on the fuel

`allLB` proves `AllLB n` for every `n` from `ApproxDispatch`.  The strong-
induction IH `ih : ∀ m, m < n → AllLB m` covers every recursive premise (all at
fuel `< n` once a constructor fixes the conclusion fuel to its `n`).  Every case
is one `divg_step`: the matching `ApproxDispatch` field supplies the ≥ 1-step
dispatch prefix (`LandedN 1 c sub-entry`), the IH supplies the `Divg` from the
sub-entry.  The `zero` cases are `Divg 0` — trivially the empty run. -/

/-! ## §5. `approxSeam` from the fold

The loop head is a SEQUENCE position (executing `s :: ss`), not a bare statement
position.  A still-running head `SApprox n st d env s` lifts to `Approx (n + 1) st
d env (s :: ss)` via `Approx.head`, and `ApproxLB (n + 1)` at the loop-head
`SqEntry` gives `Divg (n + 1) cH` — exactly the `approxSeam` conclusion.  So the
supplier need only instantiate `SqEntry` at the loop-head `SegEntry` + `Reflect`
(the last obligation, `hSqEntry`, whose supplier is `loopHeadDispatch_span` — the
SAME span `iterSeam` consumes). -/

/-! ## §6. The divergence family closed on both assemblies

`approxSeam_of_dispatch` IS the `InterpRunLoopResiduals.approxSeam` field body
(identical ∀-signature and `∃ m c₁, n + 1 ≤ m ∧ StepsN m cH c₁` conclusion), so it
plugs directly into `IterSeamAssembly.interpRunLoopResiduals_of_iter` /
`divFamily_of_iterAssembly` alongside the assembled `iterSeam`.  `divFamily_of_
assemblies` composes the two: the whole divergence arm closed on the shared entry
drive + the iter loop-body assembly (`IterSeamResid`) + the approx dispatch
(`ApproxDispatch` + the loop-head-entry instantiation `hSqEntry`). -/

end Vsa.Sim.ApproxSeamFold
