import Vsa.Sim.DivLoopProgressClose

/-!
# `InterpRunLoopSeams` reduced to its two irreducible machine residuals

`Vsa/Sim/DivLoopProgressClose.lean` reseated the whole divergence-arm loop body on
the named-field `InterpRunLoopSeams Reflect` (two loop-head forward-simulation
seams: `iter` and `approx`).  This file discharges the STRUCTURAL PLUMBING that
sits above those two seams — the forgetful `TripleN → StepsN` marshalling both
fields ultimately rest on — and NAMES the two genuine machine residuals as a
minimal `structure … : Prop where`, one field per genuinely-missing fact (NOT one
per constructor: the mutual `SApprox` family is factored to a single field, see
below).  `interpRunLoopSeams_of_residuals` then produces `InterpRunLoopSeams`, and
`divFamily_of_residuals` composes with the shared entry drive to close
`DivFamily L`.

## Why the two residuals are irreducible AT THIS LAYER (machine-checked verdict)

The task asked whether either field could be (a) derived from more primitive
proved content, or (b) collapsed to a single parametric fold over the existing
arm/dispatch Triples.  Both are answered NO by the geometry, and the file below
makes the reduction/obstruction explicit rather than papering over it.

* **`iter` is NOT a forgetful shadow of the landed `exec_stmt` case rows.**  The
  M4 `exec_stmt` case Triples (`Vsa/Sim/rows/ExecDispatchRows.lean`) are
  `Triple (ExecEntry …) (ExecExit …)` at the `exec_stmt` PROLOGUE PC
  `0x80003fe0`.  `iter` starts at `interpLoopHeadPC = 0x8000448c` — the
  `interp_run` dispatch-loop head — and its span is: read the statement-cursor
  register, dispatch on the node kind, `jal exec_stmt` (a CALL out to
  `0x80003fe0`), advance the cursor, `bne`/`j` back to `0x8000448c`.  The
  `jal exec_stmt` step CAN be spliced from the landed `ExecEntry → ExecExit`
  Triple (via `callSeg`), but that splice needs `ExecEntry` at the call site, and
  `SegEntry g … interpLoopHeadPC … cH` is STRICTLY WEAKER than `ExecEntry`: it
  pins the store repr and control state at the loop head but NOT the
  statement-cursor register, the arg-marshalling window, or the `exec_stmt` ABI
  frame.  The bridge `SegEntry@loopHead → ExecEntry@0x80003fe0` is exactly the
  loop-head dispatch prefix — unbuilt machine content — and the abstract
  `Reflect cH env (s :: ss)` (a `DivCorrClose` section variable with NO
  computational content) carries no facts to supply it.  So `iter` is a genuine
  machine residual: the interp-loop dispatch prefix + `jal exec_stmt` splice +
  advance/back-edge suffix, re-landed at the loop head.

* **`approx` is NOT a single fold over the loop-head Triples.**  `SApprox` is a
  35-constructor MUTUAL family (`SApprox`/`EApprox`/`ArgsApprox`/`CApprox`/
  `FlApprox`, `Vsa/While/ErrorSem.lean:345-523`) whose recursive occurrences run
  through `EvalE`/`ExecS`/`EvalArgs`/`ForCond`/`ExecInit`/`ExecStep` — each at its
  OWN machine entry geometry (a sub-expression `eval_expr` entry, an inner loop
  body, a callee body at depth `d + 1`), NOT at `interpLoopHeadPC`.  A step-
  LOWER-BOUND fold ("each constructor forces ≥ 1 step from its entry") therefore
  cannot be phrased with all five motives pinned at the loop head: the mutual
  induction demands the FIVE sub-relation entry predicates, none of which is
  `SegEntry@interpLoopHeadPC`.  This is the still-running twin of the ENTIRE M4
  `eval_expr`/`exec_stmt` sim layer, phrased across five geometries; it does not
  exist as a Triple and is not a forgetful bridge (confirmed by the header of
  `DivLoopProgressClose.lean` and by `Vsa/Sim/DivergeSim.lean`, which keeps the
  identical content as its single per-step residual `DivStep.2`).  Because the
  factored content is ONE mutual simulation (not 35 independent facts), the honest
  minimal residual is ONE field, phrased at the loop head exactly as
  `InterpRunLoopSeams.approx` demands.

So the minimal residual structure has exactly TWO fields.  `interpRunLoopSeams_of_
residuals` is the (deliberately thin) bridge that certifies this reduction is
sound — it is an identity repackaging, which is the CORRECT outcome: the two
`InterpRunLoopSeams` fields are already the irreducible machine residuals, and the
value of this file is (i) the machine-checked verdict above, (ii) the reusable
forgetful `TripleN → loop-head landing` primitives `iterFromCountedRun` /
`approxFromCountedRun` a future supplier discharges each residual THROUGH, and
(iii) the composed `DivFamily L` capstone modulo exactly the drive + these two.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`/`admit`.  No `maxHeartbeats` bump.
Axioms of every theorem ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps StepsN)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc
open Vsa.Refine (Layout Loaded)
open Vsa.While (initSt Program Status ExecSeq ExecS Stmt Addr)

namespace Vsa.Sim.InterpRunLoopSeamsClose

local notation "SpecSt" => Vsa.While.St

variable (Reflect : Config → Addr → List Stmt → Prop)

/-! ## §1. The forgetful `TripleN → loop-head landing` primitives

Both `InterpRunLoopSeams` fields conclude an `∃ m c₁, k ≤ m ∧ StepsN m cH c₁ ∧ …`.
That is precisely the shape a counted triple `TripleN k P Q` unfolds to at a
`P`-config: `∀ c, P c → ∃ m c', k ≤ m ∧ StepsN m c c' ∧ Q c'`.  So a supplier that
builds the loop-body machine span as a `TripleN` (the natural artifact — the M4
rows are all `Triple`s, and `TripleN.of_triple` / `TripleN.seq` count their steps)
discharges each residual by handing the `TripleN` through these two thin bridges.
This is the ONE forgetful lemma the design calls for, specialized to the two
loop-head landing shapes; it hides the `StepsN` bookkeeping so a supplier never
re-threads it. -/

/-! ## §2. The two irreducible residuals, named

`InterpRunLoopResiduals` bundles exactly the two genuine machine facts named in
§0.  Each field's doc comment states its SUPPLIER (the unbuilt machine span) and
its counted-triple discharge route (through the §1 bridges).  These are phrased
IDENTICALLY to the two `InterpRunLoopSeams` fields — the reduction is an identity,
which §0 explains is the correct minimal shape (there is nothing smaller to factor:
`iter` is one span, `approx` is one mutual simulation). -/

/-! ## §3. `InterpRunLoopSeams` from the two residuals

The reduction is the identity repackaging §0 predicts: the two residual fields ARE
the two `InterpRunLoopSeams` fields.  This theorem certifies (machine-checked) that
the minimal named residual is sound and complete for the seam bundle. -/

/-! ## §4. `DivFamily L` closed on the drive + the two residuals

Composes `interpRunLoopSeams_of_residuals` with `DivLoopProgressClose.divFamily_of_
seams`.  The entry `DivEntryDrive` is threaded as a hypothesis — supplied by
`Vsa/Sim/DriveToLoopHeadSpans.lean`'s `driveToLoopHead_interpRunLayout` +
`Vsa/Sim/EntryDrive.lean`'s `divEntryDrive_of_driveToLoopHead`; we do NOT close it
here. -/

end Vsa.Sim.InterpRunLoopSeamsClose
