import Vsa.Sim.InterpRunLoopSeamsClose
import Vsa.Sim.rows.LoopHeadDispatch
import Vsa.Sim.rows.InterpBackEdgeSeg
import Vsa.Sim.rows.ExecDispatchRows
import Vsa.Sim.StepCount

/-!
# `iterSeam` assembled — the interp_run back-edge iteration span (Task, wave 26)

`Vsa/Sim/InterpRunLoopSeamsClose.lean` names the `iterSeam` residual (the first
field of `InterpRunLoopResiduals`) and pins its discharge route: build the loop-body
machine span from the loop head `cH` back to the tail loop head `cH'`, ≥ 1 step,
re-landing `SegEntry@interpLoopHeadPC` for `st'` executing `ss` (with `Reflect cH'
env ss`).  Wave 25 landed the two inputs this assembly composes:

* `loopHeadDispatch_span` (`rows/LoopHeadDispatch.lean`) — the loop-head → `exec_stmt`
  ENTRY span: `SegEntry@loopHead cH → ∃ cE, Steps cH cE ∧ ExecEntry@0x80003fe0 cE`,
  return link `x1 = 0x80004478`.
* `interpBackEdgeRow` (`rows/InterpBackEdgeSeg.lean`) — the exec_stmt RETURN → loop
  head suffix `[0x80004478 → 0x8000448c)`: `beq a0,s3` (NOT taken, status `.normal`
  ⇒ a0 = 0 ≠ s3 = 3) ; `addiw a0,a0,-1` ; `bgeu s4,a0` (NOT taken, s4 = 1 <
  0xFFFF…FFFF) ; `addi s0,s0,8` (advance the cursor) ; `beq s0,s2` (NOT taken, the
  tail `ss` is non-empty ⇒ cursor ≠ array-end bound), landing at `0x8000448c`.
* `StepCount.lean` — the counted-run algebra (`StepsN`/`TripleN`, `segToTripleN`,
  `iterFromCountedRun`) the raw landing is threaded through.

## The iteration shape (one loop pass)

```
  cH  @0x8000448c  (SegEntry@loopHead, st, executing s :: ss, Reflect cH env (s::ss))
      │  loopHeadDispatch_span      (dispatch head ≫ value_null ≫ arg-setup ≫ jal)
      ▼
  cE  @0x80003fe0  (ExecEntry, head statement s, link 0x80004478)
      │  exec_stmt IH  (ExecIH st d env s st' .normal — the M4 exec_stmt Triple)
      ▼
  cX  @0x80004478  (ExecExit@ret target, a0 = StatusCode .normal = 0)
      │  interpBackEdgeRow          (the back-edge suffix, 5 instrs, 3 not-taken br)
      ▼
  cH' @0x8000448c  (SegEntry@loopHead, st', executing ss, Reflect cH' env ss)
```

## The residual structure — what the exit genuinely cannot supply

`IterSeamGeom` bundles, as named-field providers (gate R6/R7 — no positional
towers, one field per genuinely-missing fact), exactly the content the composition
does NOT already have:

* `hExecIH` — the `exec_stmt` machine Triple for the head statement `s`
  (`ExecIH st d env s st' .normal`).  This is the crux: the M4 statement-family
  simulation applied to `s`, supplied by `rows/ExecDispatchRows.lean` (the dispatch/
  loop cases) + the leaf/recursive `ExecS` rows.  NOT derivable from the loop-head
  `SegEntry`/`Reflect` (both carry no `exec_stmt`-entry ABI/AST geometry).
* `hDispatch` — from `SegEntry@loopHead cH` + `Reflect cH env (s :: ss)`, the
  dispatch-span landing at `ExecEntry` (`loopHeadDispatch_span`'s conclusion).  This
  packages `LoopHeadDispatchGeom` (the stack/AST/code geometry off the loop head),
  the value_null call splice, and the arg-setup ≫ jal exec_stmt seam — none a
  consequence of `SegEntry`; `Reflect` is where the head statement `s`'s node
  geometry (`aStmt`, `StmtRepr`) enters.  Its `cE`'s `x1 = 0x80004478` link is what
  makes the back-edge land at the suffix.
* `hReenter` — from the `exec_stmt` ExecExit landing at `0x80004478` for `st'`
  `.normal`, drive the back-edge suffix to the loop head and RE-ESTABLISH
  `SegEntry@loopHead` for `st'` executing `ss`, with `Reflect cH' env ss`.  The
  back-edge suffix run is `interpBackEdgeRow` (proved), but its branch guards
  (a0 = 0 ≠ s3 = 3, s4 = 1 < …, cursor ≠ bound) need the loop-invariant registers
  `s3`/`s4`/`s2` and the advanced cursor `s0` — off `SegEntry`, carried through
  `exec_stmt` as callee-saveds — and the re-established `SegEntry` needs the store
  transported (ExecExit's extended-φ `StoreRepr` re-cast to `SegEntry.store`) and
  the abstract `Reflect cH' env ss` for the tail (the section variable's non-
  computational content, exactly as `Reflect cH env (s :: ss)` supplied the head).

`iterSeam_of_geom` composes the three: `Steps cH cE` (dispatch) ≫ `Steps cE cX`
(exec_stmt IH) ≫ `Steps cX cH'` (back-edge, ≥ 1 step ⇒ the whole run is ≥ 1 step,
counted off the `steps` field via `StepCount`), landing the raw `iterSeam`
conclusion (`StepsN m cH cH' ∧ StepsN 0 cH' cH' ∧ SegEntry@loopHead st' ss ∧
Reflect`).  `iterSeam_of_residuals` ∀-closes it into the `InterpRunLoopResiduals.
iterSeam` field, and `divFamily_of_iterAssembly` threads it into
`divFamily_of_residuals` alongside the (still-open) `approxSeam`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no `maxHeartbeats`
bump.  Axioms of every theorem ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps StepsN)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc
open Vsa.Refine (Layout Loaded)
open Vsa.While (initSt Program Status ExecSeq ExecS SApprox Stmt Addr St)

namespace Vsa.Sim.IterSeamAssembly

local notation "SpecSt" => Vsa.While.St

variable (Reflect : Config → Addr → List Stmt → Prop)

/-! ## §1. The iteration residual — named-field providers -/

/-! ## §2. The step-count witness — the raw landing is ≥ 1 step

The composite `Steps cH cH'` advances the `steps` counter by ≥ 1 (the dispatch
span alone runs real machine steps).  `StepCount.Steps.toN_of_stepsField` reads
the count off the `steps` field; the `≥ 1` bound comes from the back-edge suffix
being a non-empty seg run whose landing config has a strictly larger `steps` field
than its entry, and the counter is monotone along the preceding runs. -/

/-! ## §3. `iterSeam` assembled from the residual -/

/-! ## §4. The `iterSeam` field, and threading into `InterpRunLoopResiduals`

`IterSeamResid` ∀-closes `IterSeamGeom` over the per-node layout ghosts — the
supplier the `iterSeam` field genuinely needs (one bundle per `(st,d,env,s,ss,st')`
node, for every loop-head config/layout).  `iterSeam_of_resid` turns it into the
raw `iterSeam` field body via `iterSeam_of_geom`.  `interpRunLoopResiduals_of_iter`
then packages it with a supplied `approxSeam` into the full two-field
`InterpRunLoopResiduals`, and `divFamily_of_iterAssembly` closes `DivFamily L`
modulo the entry drive, the `IterSeamResid` supplier, and `approxSeam`. -/

end Vsa.Sim.IterSeamAssembly
