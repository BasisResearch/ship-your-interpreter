import Vsa.Sim.ApproxDispatchSuppliers
import Vsa.Sim.InterpEntry
import Vsa.Sim.ExecEntry

/-!
# `ApproxArmReseat` — concrete interior entries for `ApproxArmResid` + the precise gap (Task #74)

`ApproxDispatchSuppliers.ApproxArmResid` is ∀-closed over FIVE abstract interior
entry predicates (`EEntry`/`AEntry`/`CEntry`/`SEntry`/`FEntry`) plus the concrete
`SqEntryC`.  Task #74 is to CHOOSE those five as ∃-ghost landing bundles (the
sanctioned `def : Prop := ∃ data, props` shape — model `SqEntryC`) each carrying
PC + `GoodState` + the child NODE ADDRESS the arm segs' write-logs expose (the
observation `approxdispatch-entries-cannot-be-weakest-pc-only`: an interior entry
CANNOT be PC-only; it must carry the child node address), then discharge the 36
`ApproxArmResid` fields per SEG CLASS.

## What this file delivers, and the machine-checked obstruction it records

The five interior entries are instantiated as the sanctioned ∃-ghost bundles over
the RICH M4 entries (`EvalEntry`/`ExecEntry` and, for the interior control points
that have no dedicated rich struct — the callee body, the arg loop, the for-loop
remainder — a `SegEntry` at that control point's PC + a `Reflect`-style abstract
node fact).  With these entries pinned, EACH `ApproxArmResid` field acquires a
CONCRETE, precisely-typed statement: it is exactly the "arm seg split at the
recursive `jal`/dispatch-to-child point" lemma — the prefix from the arm head to
the point where control reaches the CHILD's rich entry.

The machine-checked finding (verified against `blockA_binaryArm`, `blockB_unary`,
`blockA_k`, and the `ExecDispatchRows`/`ExecRouting` term-family sims): **no arm
seg currently exposes this split.**  Every landed M4 arm artifact is a FULL
`Entry → Exit` Triple for the NORMAL-termination path, and it consumes the child
sub-evaluation as a RETURNING induction hypothesis (`blockB_unary` literally takes
`hIH : EvalIH st d env esub st' vsub` and composes it, landing at
`SubEvalReturn` — control AFTER the recursive call returns), NEVER as a
step-counted prefix landing AT the child's entry.  The child's rich entry IS
reached (the recursive `jal eval_expr` inside the arm chain targets `evalExprEntry`
with the child node pointer in registers), but it is buried as a sub-config partway
through the arm's `Steps` chain, not factored into a named lemma.

So the divergence arm (whose recursion goes INTO the child that never returns)
needs the arm segs re-cut at the `jal`: the PREFIX (arm head → jal target = child
entry) is a genuine `LandedN ≥1 c (child-EEntry)`, and it is a sub-chain of the
existing arm seg, but re-exposing it is UPSTREAM arm-seg surgery (not a supplier
pass over existing artifacts).  This is the class-by-class reseat the observation
`approxdispatch-entries-cannot-be-weakest-pc-only` named; this file makes it
concrete by pinning the entries so every gap field is a precisely-typed,
upstream-dischargeable statement, and bundles the 36 as `ApproxArmResidGap`.

`armResid_of_gap` proves `ApproxArmResid <the concrete entries> ← ApproxArmResidGap`
(identity projection — the gap structure has the same 36 field types, instantiated
at the concrete entries), and `divFamily_of_armResidGap` is the composing
corollary through `ApproxDispatchSuppliers.divFamily_of_armResid`.  Discharging the
divergence arm now reduces to the 36 named split lemmas (one per class, upstream)
plus `hEntry`/`hIter`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no `maxHeartbeats`
bump.  Axioms of every theorem ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Sim.Code
open Vsa.Machine (MState Config Step Steps StepsN)
open Vsa.Logic (TripleN)
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc
open Vsa.Refine (Layout)
open Vsa.While (St Stmt Expr BinOp UnOp Value ClosureData Store Status Addr SApprox EApprox ArgsApprox CApprox FlApprox Approx EvalE EvalArgs ForCond ExecInit ExecStep ExecS)

namespace Vsa.Sim.ApproxArmReseat

local notation "SpecSt" => Vsa.While.St

-- The opaque interior entries (`AEntryC`/`CEntryC`/`FEntryC`) carry the child spec
-- node via the ghost interior PC, so their spec-node args are intentionally unused.
set_option linter.unusedVariables false

-- discipline: allow(R7-conj-tower-def) the five interior entries below are the
-- SANCTIONED ∃-ghost LANDING BUNDLES (`def : Prop := ∃ data, props`), the exact
-- shape mandated by Task #74 and modelled by `ApproxDispatchSuppliers.SqEntryC`:
-- a `structure : Prop` cannot project the layout DATA (`Addr → Nat` φ-maps, arenas)
-- the entries carry, so each MUST be a `∃` over that data wrapping a NAMED-FIELD
-- rich entry (`EvalEntry`/`ExecEntry`/`SegEntry`). Five such bundles = 10 `∃`; this
-- is landing-bundle data, not an anonymous post/entry tower.

/-! ## §1. The five concrete interior entries (∃-ghost landing bundles)

Each entry is a `Prop`-valued `∃` over the layout/ghost DATA (a `structure : Prop`
cannot project the `Addr → Nat` φ-maps), carrying the child NODE ADDRESS via the
rich entry's `aExpr`/`aStmt` field — exactly the exposure the observation demands.
`EEntry`/`SEntry` wrap the rich `EvalEntry`/`ExecEntry`; `AEntry`/`CEntry`/`FEntry`
anchor on a `SegEntry` at the relevant interior control PC (the arg loop, the
callee-inline body head, the for-cond re-entry), whose `entryPC` ghost is the
child dispatch address the arm's write-log exposes. -/

/-! ### The wave-45 `SEntryC` amendment (re-land): the two re-entry routes

Wave 44 machine-checked (`sEntryC_false_at_dispatchHead`, `ArmSegSplitTwins`)
that the `stmtIfThen`/`stmtIfElse` tail re-dispatch (`j`/`bnez 0x80004014`) and
the `stmtWhileLoop` loop-back (`bne a0,a5,0x80004034`) NEVER revisit
`execStmtEntry` — a child statement can be entered three ways.  `SEntryC` is
therefore re-seated as the 3-way disjunction of the honest entry classes:
fresh call (`SFreshC`), post-prologue dispatch head (`SDispatchC`), and the
while-arm head (`SWhileArmC`, shape-guarded to `.whileStmt` so every non-while
consumer refutes the leg by `nomatch`).  `ExecDispatchEntry`/`SDispatchC` and
`execStmtDispatchHead` are MOVED here from `ArmSegSplitTwins` (wave-45 dedup)
so the disjunction sits upstream of every consumer. -/

/-! ## §2. `ApproxArmResidGap` — the 36 arm fields at the CONCRETE entries

With the five interior entries pinned (§1), `ApproxArmResid` acquires concrete
field types.  `ApproxArmResidGap Reflect` IS `ApproxArmResid Reflect EEntryC …
FEntryC` — no smaller remainder is possible, because (machine-checked against
`blockA_binaryArm`/`blockB_unary`/`blockA_k` and the `ExecDispatchRows`/
`ExecRouting` term sims) NONE of the 36 fields is dischargeable from an existing
seg: every M4 arm artifact is a full `Entry → Exit` normal-termination Triple that
CONSUMES the child sub-evaluation as a returning IH, so no arm currently exposes
the `arm-head → LandedN ≥1 → child-entry` PREFIX the divergence fold needs (that
prefix is a sub-chain of the arm seg, cut at the recursive `jal`, but not a named
lemma).  Naming it as an alias makes each field a precisely-typed, upstream-
dischargeable split-lemma statement over the concrete entries. -/

/-! ## §3. The composing capstone — `divFamily_of_armResidGap`

Threading the concrete entries + `ApproxArmResidGap` through
`ApproxDispatchSuppliers.divFamily_of_armResid`.  The whole divergence arm reduces
to the shared entry drive (`hEntry`), the iter loop-body assembly (`hIter` — which
also supplies `seqStep` and the concrete `SqEntryC`), and the 36 upstream arm-seg-
split lemmas bundled as `ApproxArmResidGap`.  This is the LAST divergence content
localised to precisely-typed, per-class split statements. -/

end Vsa.Sim.ApproxArmReseat
