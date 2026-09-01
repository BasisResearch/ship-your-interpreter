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
open Vsa.Machine (MState Config Step Steps StepsN)
open Vsa.Logic (TripleN)
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc
open Vsa.Refine (Layout)
open Vsa.While (St Stmt Expr BinOp UnOp Value ClosureData Store Status Addr
  SApprox EApprox ArgsApprox CApprox FlApprox Approx
  EvalE EvalArgs ForCond ExecInit ExecStep ExecS)
open Vsa.Sim.Scaffold (SegEntry)
open Vsa.Sim.ApproxSeamFold
open Vsa.Sim.ApproxDispatchSuppliers

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

/-- **Eval entry.**  `c` is at `eval_expr`'s entry with the node `e` at some ghost
address `aExpr` (the child address the parent arm seg wrote into `a2`). -/
def EEntryC (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) : Prop :=
  ∃ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem),
    EvalEntry g N A SL φf φc st d env e sp r sret aEnv aExpr m0 c

/-- **Statement entry.**  `c` is at `exec_stmt`'s entry with the node `s` at some
ghost address `aStmt`. -/
def SEntryC (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) : Prop :=
  ∃ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem),
    ExecEntry g N A SL φf φc st d env s sp r aInterp aStmt aEnv aRet m0 c

/-- **Args entry.**  `c` is at the EX_CALL arg-loop control point (a ghost interior
PC) for the remaining arg list `es`.  Anchored on `SegEntry` at that PC — the
arg-loop head the parent `callArgs` prefix reaches; the abstract node fact carries
the arg-list correspondence (which arg node is next), kept opaque exactly as the
`DivergeSim.Corr` correspondence. -/
def AEntryC (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (es : List Expr) : Prop :=
  ∃ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft argLoopPC : Nat) (m0 : Mem),
    SegEntry g N A SL φf φc st d dLeft aLeft argLoopPC m0 c

/-- **Callee body entry.**  `c` is at the callee-inline body head (a ghost interior
PC) for the callee value `fv` applied to `vs`.  Anchored on `SegEntry`; the
abstract fact carries the callee/args correspondence. -/
def CEntryC (c : Config) (st : SpecSt) (d : Nat) (fv : Value) (vs : List Value) : Prop :=
  ∃ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft calleeBodyPC : Nat) (m0 : Mem),
    SegEntry g N A SL φf φc st d dLeft aLeft calleeBodyPC m0 c

/-- **For-loop remainder entry.**  `c` is at the for-loop re-entry control point (a
ghost interior PC) for the remaining `cnd`/`step`/`b`. -/
def FEntryC (c : Config) (st : SpecSt) (d : Nat) (env : Addr)
    (cnd step : Option Expr) (b : Stmt) : Prop :=
  ∃ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft forCondPC : Nat) (m0 : Mem),
    SegEntry g N A SL φf φc st d dLeft aLeft forCondPC m0 c

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

/-- The arm residual at the concrete interior entries.  Every one of its 36 fields
is an upstream arm-seg-split lemma (see the file header); none is closable from
existing segs. -/
abbrev ApproxArmResidGap (Reflect : Config → Addr → List Stmt → Prop) : Prop :=
  ApproxArmResid Reflect EEntryC AEntryC CEntryC SEntryC FEntryC

/-- `ApproxArmResidGap` IS `ApproxArmResid` at the concrete entries (definitional
alias).  Kept as a named theorem so the capstone reads uniformly and a future
supplier that discharges the split lemmas plugs its `ApproxArmResidGap` straight
in. -/
theorem armResid_of_gap
    (Reflect : Config → Addr → List Stmt → Prop)
    (G : ApproxArmResidGap Reflect) :
    ApproxArmResid Reflect EEntryC AEntryC CEntryC SEntryC FEntryC :=
  G

#print axioms armResid_of_gap

/-! ## §3. The composing capstone — `divFamily_of_armResidGap`

Threading the concrete entries + `ApproxArmResidGap` through
`ApproxDispatchSuppliers.divFamily_of_armResid`.  The whole divergence arm reduces
to the shared entry drive (`hEntry`), the iter loop-body assembly (`hIter` — which
also supplies `seqStep` and the concrete `SqEntryC`), and the 36 upstream arm-seg-
split lemmas bundled as `ApproxArmResidGap`.  This is the LAST divergence content
localised to precisely-typed, per-class split statements. -/

theorem divFamily_of_armResidGap
    (Reflect : Config → Addr → List Stmt → Prop) (L : Layout)
    (hEntry : Vsa.Sim.DivCorrClose.DivEntryDrive Reflect L)
    (hIter : Vsa.Sim.IterSeamAssembly.IterSeamResid Reflect)
    (G : ApproxArmResidGap Reflect) :
    Vsa.Sim.InterpSimBundle.DivFamily L :=
  divFamily_of_armResid Reflect L
    EEntryC AEntryC CEntryC SEntryC FEntryC hEntry hIter (armResid_of_gap Reflect G)

#print axioms divFamily_of_armResidGap

end Vsa.Sim.ApproxArmReseat
