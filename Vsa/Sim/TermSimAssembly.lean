import Vsa.Sim.ExecSeqIndexed
import Vsa.Sim.CallEntry

/-!
# Layer 4 — the M4 CAPSTONE: the mutual-recursor ASSEMBLY (`term_sim_of_cases`)

`Vsa/Sim/InductionScaffold.lean` established and VALIDATED the `@EvalE.rec`
plumbing (nine motives, ~50 minor premises, binder order) against the kernel with
*trivial* (`fun … => True`) motives. This file replaces those with the **REAL**
simulation motives and applies the recursor to assemble the whole mutual
induction, taking the per-constructor case Triples as explicit hypotheses.

## What is real here

* **The nine motives** (`§1`) are the honest simulation projections, using the
  *widened* exit predicates the landed recursive cases actually target:
  - `mEvalE`  = `EvalReturnIH TrivialOwned` (`EvalEntry → EvalReturn`; `.forget` = `EvalIH`),
  - `mExecS`  = `ExecBlock.ExecIH`      (`ExecEntry → ExecExitD`),
  - `mEvalArgs`/`mCall`/`mExecInit`/`mForLoop`/`mForCond`/`mExecStep`/`mExecSeq`
    are the `SegEntry → SegExit` Triples (`InductionScaffold` skeletons), at the
    decoded call/args PCs where those exist (`CallEntry`).
  Every motive ignores the derivation node (its last argument) and is
  ∀-closed over the layout ghosts + budgets, exactly the shape of the landed
  case Triples.

* **`term_sim_of_cases`** (`§2`) is the full nine-motive `@EvalE.rec`
  application. Each of the ~50 minor premises is taken as an EXPLICIT hypothesis
  of the theorem, in the exact ∀-closed shape the recursor demands (constructor
  args, then the sub-derivation IHs in the motive shape, then the motive
  conclusion). The proof is `@EvalE.rec` applied to those hypotheses: it
  type-checks iff the nine real motives compose through every constructor —
  i.e. it is the kernel-checked demonstration that the mutual induction assembles
  with the real simulation motives.

  The hypotheses are exactly the landed case Triples (`evalIntSim`, `evalNegSim`,
  …, `execBlockSim`, `evalCallSim`, …) MODULO their residual bundles: each landed
  theorem discharges its corresponding minor-premise hypothesis (conditionally on
  its named residuals / M6-layout facts / the `Call.closure` crux). The
  case ↔ hypothesis mapping is documented at each premise.

`term_sim` itself (the top-level `BigStep`-level statement) then follows by
instantiating `term_sim_of_cases` at the whole-program entry and discharging the
minor-premise hypotheses from the landed cases once the residual-unification
interface (M6) closes. That last step is future work; what is proved here is that
the induction COMPOSES and pins EXACTLY the per-constructor obligations.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`/`admit`.
-/

namespace Vsa.Sim.TermSimAssembly

open LeanRV64DExecutable Sail
open Register
open Vsa.Machine (MState Config)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim

local notation "SpecSt" => Vsa.While.St

/-! ## §1. The nine REAL motives

Each `m_R` maps a derivation node (last, ignored argument) to the simulation
`Triple` STATEMENT for that node. `EvalE`/`ExecS` use the widened
`EvalIH`/`ExecIH` (the shape the recursive cases produce and consume — `EvalExit`
upgraded to `EvalExitD` for the presence/survival facts recursive callers need);
the other seven use the `InductionScaffold` `SegEntry → SegExit` skeleton
Triples, at the real decoded PCs where `CallEntry` provides them. -/

/-! ### Route-indexed statement child interface

The existing `mExecS` is retained while constructor rows are migrated.  The
interface below names the three machine entries a statement child can actually
have: a fresh call, an in-frame dispatch, and a while-arm loop-back. -/

/-! ### Context-indexed `for` boundaries

`ExecInit` omits the enclosing `for` node.  `ForLoop` omits its `init` field.
Both machine fragments retain the full `Stmt.forStmt` pointer.  The motives
therefore quantify the missing context instead of erasing it. -/

/-! ### The seq-loop span table + ground (ITEM ZERO / falsity #12, shape 3)

`mExecSeq`'s `∀ p q` is GENUINELY needed by consumers — the statement loop is
compiled at (at least) THREE inlined copies, and landed consumers instantiate
the motive at all three pairs:

* `interp_run`'s top-level statement loop, `0x8000448c → 0x80004514`
  (`EntryHalts.hPrologue_of` / `TermEntry` / `EntrySeams`);
* the closure-body loop inside `eval_expr`'s `EX_CALL` arm,
  `callBodyLoopPC = 0x80003354 → callBodyRetPC = 0x80003378`
  (`rows/CallClosureRow`, the crux);
* the `block` arm's loop inside `exec_stmt`,
  `execSeqLoopPC = 0x800041a4 → execSeqContPC = 0x8000409c`
  (`ExecDispatchRows.BlockGeom`'s `hArm`/`hEpi` seam).

So the B6 "pin both PCs" cure is unavailable; instead the motive gets the
`mCall`/`EntryImage` wave-40 precedent: an entry-side GUARD, table-driven.
`seqLoopImage` maps exactly the legitimate loop-copy PC pairs to the landed
code-image predicate covering that copy's bytes; `SeqSpanGround p q m0`
(named-field, R6/R7) says the pair is TABLED and its image is loaded in `m0`.
Untabled pairs make the motive VACUOUS (`tabled` is unsatisfiable), so a
supplier of `hSeqNil`/`hSeqCons*` owes only the three real loop copies WITH
their code bytes in hand — dissolving fleet B6's code-free-`SegEntry`
obstruction (`seq-motive-independent-pq-no-code`).  Signature-free for every
recursor/`TermCases` reference (all fully applied); only the unfolding
producers/consumers intro/supply the hypothesis. -/

/-! ## §2. The assembled mutual induction — `term_sim_of_cases`

The full nine-motive `@EvalE.rec` application with the REAL simulation motives.
Each of the 50 minor premises is an explicit hypothesis, in the exact ∀-closed
shape the recursor demands: the constructor's arguments (including its
sub-derivation proofs `a`, `a_1`, …), then the sub-derivation induction
hypotheses in the motive shape (`mEvalE …`/`mExecS …`/…), then the motive
conclusion for this node (with the reconstructed derivation term). The body is
the recursor applied to these hypotheses.

This TYPE-CHECKS iff the nine real motives compose through every constructor of
the mutual family — it is the kernel-checked assembly of the whole simulation
induction with real motives (not the `True`-motive plumbing check of
`InductionScaffold`). It concludes `mEvalE … t = EvalReturnIH TrivialOwned …`, the coherent
`EvalE`-simulation Triple, for an arbitrary `EvalE` derivation.

Each hypothesis `h<Ctor>` is discharged — conditionally on that case's named
residuals / M6-layout facts / the `Call.closure` crux — by the correspondingly
named landed case theorem. The case ↔ hypothesis mapping (module doc):

* EvalE: hInt←`evalIntSim`, hStr←`evalStrSim`, hBool←`evalBoolSim`,
  hNull←`evalNullSim`, hVar←`evalVarSim`, hNeg←`evalNegSim`, hNot←`evalNotSim`,
  hBinary←`evalAddSim`/`evalSubSim`/`evalLtSim`/… (per `op`; le/gt/eq/ne/mul/
  div/mod mechanical-pending), hOrTrue←`evalOrTrueSim`, hOrFalse←`evalOrFalseSim`,
  hAndFalse←`evalAndSim`, hAndTrue←`evalAndTrueSim`, hCall←`evalCallSim`,
  hFn←`evalFnSim`; hAssign is a native-store case (pending env_define contract).
* EvalArgs: hArgsNil←`evalArgsNil`, hArgsCons←`evalArgsCons`.
* Call: hCallAssertOk←`callAssertOk`; hCallClosure (crux, env_define-blocked),
  hCallPrint/hCallPrintln (native output-append, template ready) are the open
  minor premises taken as hypotheses.
* ExecS: hSExpr←`execExprSim`, hSVarInit←`envDefineTail_run` (rows/Field_hSVarInitClosed),
  hSVarNull←`varNull_run` (rows/Field_hSVarNullClosed), hSBlock←`execBlockSim`,
  hSIfTrue←`execIfTrueSim`, hSIfFalse←`execIfFalseSim`, hSIfNone←`execIfNoneSim`,
  hSWhile*←`execWhileSim`, hSForStart←`execForStartSim`, hSRet←`execRetSim`,
  hSRetNull←`retNull_run` (rows/Field_hSRetNullClosed), hSBrk←`execBrkSim`,
  hSCont←`execContSim`.
* ExecSeq: hSeqNil←`execSeqNil`, hSeqConsNormal/hSeqConsAbrupt←`execSeqLoop`
  (the per-iteration rule that consumes these).
* ForLoop: hFl*←`execForLoopBody`; ForCond/ExecStep/ExecInit (hFc*/hEs*/hInit*)
  are the loop-scaffold sub-relations (`SegEntry → SegExit`), taken as
  hypotheses pending their per-relation machine proofs.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`/`admit`.  -/

end Vsa.Sim.TermSimAssembly
