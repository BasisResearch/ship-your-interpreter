import Vsa.Sim.JalPreCore
import Vsa.Sim.ApproxArmReseat

/-!
# `ArmSegSplitEval` — the `EEntryC`-valued jal→child bridge + the unary split (Task #75)

`ArmSegSplit.evalEntry_of_jalPrefix` lands the recursive `jal eval_expr` prefix at
the child's rich `EvalEntry`.  `ApproxArmReseat`'s divergence-fold entries are the
∃-ghost bundles `EEntryC c st d env e := ∃ ghosts, EvalEntry … e … c`.  This file
supplies:

* `landedN_eentryC_of_jalPrefix` — the marshalling fact re-wrapped into the exact
  `LandedN 1 c (fun c' => EEntryC c' st d env esub)` shape `ApproxArmResid`'s
  fields demand (existentially discharging the layout ghosts).  This is the ONE
  reusable bridge from `ArmSegSplit` into the divergence-fold entry type — every
  Eval-child arm class (unary / binaryL / binaryR / logicalL / … / callF /
  argsHead / stmtExpr / …) closes through it after its own arm-head staging span
  establishes the `evalEntry_of_jalPrefix` pre-bundle.

* `unaryE_split` — the **unary class** field of `ApproxArmResidGap`, delivered as a
  precisely-typed split lemma.  Its statement is `ApproxArmResid.unaryE` with the
  interior entries pinned to `EEntryC`, EXCEPT it additionally takes the
  **arm-head staging bundle** `UnaryStagePre` as a hypothesis — the machine-checked
  obstruction below.

## Machine-checked obstruction: why `unaryE` needs staging premises beyond `EEntryC`

`ApproxArmResid.unaryE` asks `EEntryC c st d env (.unary op e) → LandedN 1 c
(EEntryC e)`.  But `EEntryC (.unary op e)` = `∃ ghosts, EvalEntry (.unary op e)`,
and `EvalEntry (.unary op e)`:
  1. is at `eval_expr`'s ENTRY (`pc = evalExprEntry`), NOT at the recursive
     `jal eval_expr` PC (`0x800035e8`).  Reaching the jal requires the WHOLE
     dispatch (`blockA_k`: prologue spills + kind read + jump-table dispatch to the
     arm PC `0x800035e0`) THEN the arm head (`ld a2,16(a2)` operand load; `addi
     a0,sp,144` sub-buffer) — dozens of machine steps, not a named prefix cut.
  2. bakes in the OUTER frame's `sp`, geometry, and `ExprRepr (.unary op e)`.  The
     child entry needs the LOWERED frame `sp - 1088`, the operand node's
     `ExprRepr esub` at `aOperand` (read out of the parent node), and the
     recursive-case extras (`a1 = interp*`, `SL.lo + 3264 ≤ sp` headroom, the
     operand/sub-buffer disjointness at `sp - 1088`).  These are exactly the
     "recursive-case extras" `EvalNegSim.blockB_unary` carries BEYOND its
     `ArmEntryK` — the `ArmEntryK` widening residual — and are NOT projectable from
     `EvalEntry (.unary op e)`.

So the split is genuinely `(dispatch ∘ arm-head staging) ⊗ (jal marshalling)`; the
second factor is `evalEntry_of_jalPrefix` (built + verified), the first is the
UNBUILT arm-head+dispatch staging span (`EvalNegSim.blockB_unary`'s body up to its
`armTail_rec` call, re-cut to land at the pre-bundle instead of consuming the IH).
`unaryE_split` names that span precisely as `UnaryStagePre` and discharges the rest,
making the residual a single, upstream-dischargeable staging lemma.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no `maxHeartbeats`
bump.  Axioms of every theorem ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps StepsN)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim

/-! ## §1. The reusable `EEntryC`-valued bridge -/

/-! ## §2. The unary-class split — `ApproxArmResid.unaryE` at `EEntryC`

The arm-head staging bundle `UnaryStagePre op e c st d env` is the precise,
upstream-dischargeable residual: it says the config `c` at `EEntryC (.unary op e)`
can be advanced (through the dispatch + arm head — the UNBUILT staging span) to a
config satisfying the `evalEntry_of_jalPrefix` pre-bundle for the operand `e`, at a
lowered frame.  Equivalently (and this is the honest packaging), `UnaryStagePre` is
just the existence of the fully-staged jal pre-bundle reached from `c` — a
`LandedN` to the pre-bundle.  With it, the split is `LandedN.bind` of the staging
onto the marshalling bridge (`LandedN.bind` adds the counts, so `1 ≤` is
preserved). -/

-- discipline: allow(R7-conj-tower-def) Existing existential landing bundle; consumers use landedN_eentryC_of_preBundle.

/-! ## §3. The generic Eval-child split combinator + the binary/logical classes

Every Eval-child arm field of `ApproxArmResid` has the shape "from `EEntryC` at a
COMPOUND node, land (`≥ 1` step) at `EEntryC` of a CHILD sub-expression".  The
divergence-fold proof is ALWAYS the same: the arm-head staging span reaches
`JalPreBundle child`, then the verified marshalling bridge finishes.  This
combinator captures that composition ONCE; each class supplies only its staging
residual (a `LandedN 1 … (JalPreBundle child)`). -/

/-! ## §4. The exec-dispatch → eval-child classes

The statement arms that evaluate a sub-EXPRESSION (`stmtExpr`, `stmtRet`,
`stmtVarInit`, `stmtIfCond`, `stmtWhileCond`) and the for-cond arm (`flCond`) all
land at an `EEntryC` (a child expression), so they reuse the SAME
`evalChildSplit_of_stage` combinator — only their SOURCE entry differs
(`SEntryC`/`FEntryC` instead of `EEntryC`).  The staging residual is the
exec-dispatch prefix (`ExecDispatch`'s prologue + kind read + jump-table dispatch
to the arm) plus the arm head reaching the `jal eval_expr` — re-cut to land at
`JalPreBundle` rather than consume the eval IH. -/

/-! ## §5. Capstone — the eval-child staging bundle

`EvalChildStages` bundles the staging residuals for 14 EVAL-CHILD-LANDING
fields of `ApproxArmResidGap` (the fields whose post is `EEntryC <child expr>`,
with no extra spec-side hypotheses; `flStep` also lands at `EEntryC` but carries
`ForCond`/`ExecS`/status premises, so it is the separate `flStep_split`).
Each residual is STRICTLY SMALLER than the raw field: it stops at `JalPreBundle`,
and the verified marshalling bridge (`landedN_eentryC_of_preBundle`, built on
`evalEntry_of_jalPrefix`) finishes.  A future supplier that lands the 14 staging
spans (arm-head + dispatch re-cut to `JalPreBundle`) fills these 14 fields of
`ApproxArmResidGap` by the `*_split` corollaries below (plus `flStep_split`).

The remaining fields land at NON-`EEntryC` entries (`AEntryC` arg-loop tail,
`CEntryC` callee body, `SEntryC`/`SqEntryC`/`FEntryC` statement/for control) and
need their OWN marshalling facts (`exec_stmt`-entry / `SegEntry`-anchored), NOT
the eval-child bridge — they stay named in `ApproxArmResidGap`. -/

end Vsa.Sim
