import Vsa.Sim.ArmSegSplitNonEval
import Vsa.Sim.ArmSegSplitExecEval

/-!
# `ArmSegSplitTwins` — the bridge twins for the remaining non-eval child fields (Wave 44)

The wave-43 lane machine-checked (observations `nonevalchild-remaining-8-shape-map`,
`ifstmt-then-else-tail-redispatch-not-jal`) that 8 of the 11 `NonEvalChildStages`
fields plus `flStep` do NOT fit the landed pre-bundles.  This file builds the three
bridge twins that carry the honest machine shapes:

* **§1 (twin 1 — tail re-dispatch).**  The `.ifStmt` then/else arms reach the child
  via `ld s0,16/24(s0); j/bnez 0x80004014` — a TAIL re-dispatch to the POST-PROLOGUE
  dispatch head in the SAME `exec_stmt` frame, never a fresh `jal exec_stmt`.
  `SEntryC` (via `ExecEntry.pc`) hard-pins the child entry PC at `execStmtEntry =
  0x80003fe0`, which the tail route never revisits — the frozen `ApproxArmResid`
  field CONCLUSION `LandedN 1 c (SEntryC · st' d env t)` is therefore
  machine-unreachable on the if-arms.  The machine-checked obstruction core is
  `sEntryC_pins_entry_pc` / `sEntryC_false_at_dispatchHead` (§1.1).  The honest
  twin is `ExecDispatchEntry` (the named-field post-prologue dispatch-head entry at
  `execStmtDispatchHead = 0x80004014`) + `execEntry_of_jTailRedispatch` (§1.3), fed
  by the terminator-agnostic hop `GRegsHopInto` (§1.2, instantiable from `j`
  (`sigmaPost_jump_x0`) AND taken-branch (`sigmaPost_branch_taken`) site obs — the
  `bnez`-entered else arm rides the same twin).

  **AMENDMENT PLAN (reported, not applied — not signature-free):** re-seat the
  three tail fields on `SDispatchC`:
  - `ApproxArmReseat.SEntryC` → `∃ …, ExecEntry … ∨ ExecDispatchEntry …` (or the
    fold's `stmtIfThen`/`stmtIfElse` recursion target → `SDispatchC`), with
    `sEntryC_drives` supplying the fresh-call disjunct via the 14-instr prologue
    seg `0x80003fe0 → 0x80004010` (a `#derive_case` span, unbuilt).
  - `stmtWhileLoop` is the THIRD tail shape: `bne a0,a5,0x80004034` re-enters the
    WHILE-ARM head `0x80004034` (post-dispatch, not the dispatch head — no
    `a4`/`a6` re-materialization on that path), so its amended target is a
    while-arm entry (or the dispatch-head entry once the fold recursion is
    re-seated so the loop-back rides the arm-head block); NOT covered by
    `ExecDispatchEntry`.
  - Consumers to re-thread (grep `SEntryC`): `ArmStagesWave34` (29 refs, forbidden
    this wave), `ArmSegSplitEval` (27), `ArmSegSplitSqEntry` (14),
    `ArmSegSplitExecEval` (11), `ArmStagesPartial` (5), `ApproxArmResidGapAssembly`
    (2), rows `StmtWhileBody/StmtForInit/StmtExpr/StmtWhileCond/StmtVarInit/
    StmtRet/StmtIfCond` ArmStagePre files.

* **§2 (twin 2 — branch/fallthrough/jalr SegEntry entry).**  `SegPreBundle`
  hardcodes a static-`jal`-site premise (`callPC + jalImm = entryPC` + a
  `sigmaPost_jal` site), but `callArgs`/`argsTail`/`callC`/`stmtForLoop`/`flLoop`
  enter their interior control points by fallthrough/`j`/`jalr` — no jal targets
  them.  `SegPreBundleB` replaces the jal model with the terminator-agnostic
  one-step hop `StepInto` (any step landing at `entryPC` preserving mem/out —
  `j`, taken/not-taken branch, `jalr`, or plain fallthrough).  `SegPreBundle`
  strictly refines it (`segPreBundleB_of_jal`), and the five `*_splitB` theorems
  conclude the EXACT frozen `ApproxArmResid` field types (those are fine — the
  `AEntryC`/`CEntryC`/`FEntryC` bundles anchor on `SegEntry` at a GHOST interior
  PC, no jal pin).

* **§3 (twin 3 — `flStep_split'`).**  `flStep` evaluates the for-STEP expr via
  `jal eval_expr @0x800042e8` sited in `exec_stmt`'s text (the EXEC frame,
  sp-176), but `ArmSegSplitEval.flStep_split` hardcodes the eval-frame
  `JalPreBundle` (whose `hjalSite` is `Eval_exprLoaded`-typed — the falsity-#7
  class, wave-40 precedent).  `flStep_split'` is the exec-frame twin typed to
  `ExecJalPreBundle`, finishing through `execEvalEntry_of_jalPrefix`; its
  conclusion is the exact `ApproxArmResid.flStep` field type.  The
  `ArmStages.flStep` STAGING premise (`ApproxArmResidGapAssembly`) is still
  `JalPreBundle`-typed; re-typing it to `ExecJalPreBundle` breaks
  `armStages_mk`/`divFamily_of_armStageComponents`/`divFamily_wave34/40/42`
  premise types (not signature-free) — the wave-45 assembly consumes
  `flStep_split'` directly when building `ApproxArmResidGap`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no `maxHeartbeats`
bump.  Axioms of every theorem ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps StepsN)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.While (St Stmt Expr BinOp UnOp Value ClosureData Store Status Addr EvalE EvalArgs ForCond ExecInit ExecStep ExecS)
open Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

set_option linter.unusedVariables false

/-! ## §1.1. The tail-re-dispatch obstruction core (Law 4, machine-checked)

`SEntryC` demands a full `ExecEntry`, whose `pc` field literally pins
`execStmtEntry = 0x80003fe0`.  The if-then arm's actual terminator is
`j 0x80004014` (word `0xde5ff06f @ 0x80004230`), the else arm's is
`bnez s0,0x80004014` (`@ 0x800042d0`): both land at the post-prologue dispatch
head, and the child re-dispatch never revisits `0x80003fe0` (a fresh `jal
exec_stmt` with the CHILD node happens only for grandchildren).  So any config on
the tail route fails `SEntryC` — pinned here once, decidably. -/

/- `execStmtDispatchHead` / `ExecDispatchEntry` / `SDispatchC` MOVED UPSTREAM to
`Vsa/Sim/ApproxArmReseat.lean` (wave-45 dedup): the amended 3-way `SEntryC`
disjunction needs them at its own def site.  This file consumes them through
`open Vsa.Sim.ApproxArmReseat`. -/

/-! ## §1.2. The terminator-agnostic hops

`StepInto` — ONE machine step lands at a target PC preserving mem/out (all the
light `SegEntry` needs).  `GRegsHopInto` strengthens it with the non-noise
register frame (what the rich dispatch-head entry needs).  Both are instantiable
from the three terminator obs classes (`sigmaPost_jump_x0`,
`sigmaPost_branch_taken`, `sigmaPost_branch_nottaken`) via the `BlockTerm`
`pc_*_bt`/`mi_*_bt`/`frame_term_*_bt` consumers — and from a `jal` site obs
(`segPreBundleB_of_jal` below), so the jal model is a strict special case. -/

/-! ## §1.3. `ExecDispatchEntry` — the honest tail-re-dispatch child entry

The post-prologue dispatch-head state at `0x80004014`: the child statement staged
in the SAME frame (`s0 = aStmt` — the tail route reloads it from the parent node;
`s1`/`s3`/`s2` still carry interp/env/retslot from the prologue), the jump-table
base re-materialized (`a4 = stmtJumpTableBase`, `a6 = 8` — the if-arm re-executes
`li a6,8; auipc/addi a4` at `0x8000421c..0x80004224` before its terminator), `sp`
ALREADY lowered (`stackOK … 1088`: the exec frame is live, only the eval headroom
remains).  Mirrors `ExecEntry` minus the call-boundary fields (`a0-a3`/`ra`: the
frame's `ra` slot belongs to the PARENT call and is untouched by the tail). -/

/- `ExecDispatchEntry` / `SDispatchC` formerly defined HERE — MOVED UPSTREAM to
`Vsa/Sim/ApproxArmReseat.lean` (wave-45 dedup, the amended `SEntryC`'s second
disjunct).  Consumed below through `open Vsa.Sim.ApproxArmReseat`. -/

-- discipline: allow(R7-conj-tower-def) `ExecStmtTailPreBundle` is the SANCTIONED
-- ∃-ghost LANDING BUNDLE for the tail twin (same precedent as `ExecStmtPreBundle`);
-- carries layout DATA a `structure : Prop` cannot project.  Its named destructurer
-- is `landedN_sDispatchC_of_preBundle`.

/-! ## §2. `SegPreBundleB` — the terminator-agnostic SegEntry pre-bundle

`SegPreBundle`'s jal-site model (`callPC + jalImm = entryPC` + `sigmaPost_jal`)
does not match the interior entries of `callArgs`/`argsTail`/`callC`/
`stmtForLoop`/`flLoop` (fallthrough/`j`/`jalr` targets — no static jal aims at
them).  `SegPreBundleB` carries the light hop `StepInto` instead; everything a
`SegEntry` needs survives ANY mem/out-preserving step. -/

-- discipline: allow(R7-conj-tower-def) `SegPreBundleB` is the SANCTIONED ∃-ghost
-- LANDING BUNDLE variant of `SegPreBundle` (same precedent); consumers go through
-- the named destructurers below.

/-! ### The generic B split combinators + the 5 field splits

Each `*_splitB` concludes the EXACT frozen `ApproxArmResid` field type (the
`AEntryC`/`CEntryC`/`FEntryC` conclusions are jal-free — only the STAGING bundle
changes), so the wave-45 assembly can feed them straight into the
`ApproxArmResidGap` literal in place of the jal-typed `*_split` outputs. -/

/-! ## §3. `flStep_split'` — the exec-frame flStep twin

The lone `flStep` field of `ApproxArmResid` (`... → FEntryC cnd (some e) b →
LandedN 1 (EEntryC e)`) with its staging re-typed to `ExecJalPreBundle` (the
`Exec_stmtLoaded`-sited jal seam, wave-40 falsity-#7 class) — the honest type for
the for-STEP arm's `jal eval_expr @0x800042e8` in the EXEC frame. -/

end Vsa.Sim
