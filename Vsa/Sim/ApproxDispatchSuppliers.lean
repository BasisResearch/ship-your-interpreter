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
open Vsa.While (St Stmt Expr BinOp UnOp Value ClosureData Store Status Addr
  SApprox EApprox ArgsApprox CApprox FlApprox Approx
  EvalE EvalArgs ForCond ExecInit ExecStep ExecS)
open Vsa.Sim.Scaffold (SegEntry)
open Vsa.Sim.ApproxSeamFold

namespace Vsa.Sim.ApproxDispatchSuppliers

local notation "SpecSt" => Vsa.While.St

/-! ## §1. The concrete `SqEntry`: loop-head `SegEntry` + `Reflect`

The one entry the composition boundary pins.  A machine config `cH` is a valid
sequence entry for `(st, d, env, ss)` iff, for SOME layout ghosts, it satisfies the
loop-head `SegEntry` at `interpLoopHeadPC` for `st` executing at depth `d` and the
abstract `Reflect cH env ss` carries the (non-computational) node fact.  This is a
Prop-valued `∃` over the ghosts (they are DATA — layout maps — so a `structure : Prop`
cannot project them; the sanctioned landing-bundle shape). -/

/-- **The concrete sequence entry.**  `cH` executes the loop-head `SegEntry` for `st`
at depth `d`, with `Reflect cH env ss`.  `hSqEntry` (below) is definitional. -/
def SqEntryC (Reflect : Config → Addr → List Stmt → Prop)
    (cH : Config) (st : SpecSt) (d : Nat) (env : Addr) (ss : List Stmt) : Prop :=
  ∃ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft : Nat) (m0 : Mem),
    SegEntry g N A SL φf φc st d dLeft aLeft interpLoopHeadPC m0 cH ∧
    Reflect cH env ss

/-- **`hSqEntry`, definitional.**  A loop-head `SegEntry` + `Reflect` IS a `SqEntryC`.
This is the `approxSeam_of_dispatch` / `divFamily_of_assemblies` `hSqEntry` obligation,
supplied with NO machine content (the concrete entry was CHOSEN to be this pair). -/
theorem sqEntryC_of_seg (Reflect : Config → Addr → List Stmt → Prop) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt)
      (cH : Config)
      (g : (R : Register) → Option (RegisterType R))
      (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
      (dLeft aLeft : Nat) (m0 : Mem),
      SegEntry g N A SL φf φc st d dLeft aLeft interpLoopHeadPC m0 cH →
      Reflect cH env (s :: ss) →
      SqEntryC Reflect cH st d env (s :: ss) := by
  intro st d env s ss cH g N A SL φf φc dLeft aLeft m0 hSeg hRefl
  exact ⟨g, N, A, SL, φf, φc, dLeft, aLeft, m0, hSeg, hRefl⟩

#print axioms sqEntryC_of_seg

/-! ## §2. The sequence `seqStep` class — supplied FOR FREE by `IterSeamResid`

`iterSeam_of_resid` produces exactly the `LandedN 1 cH (SqEntryC ss)` shape (its
`StepsN 0 c₁ cH'` collapses the intermediate config).  We marshal it into the
`ApproxDispatch.seqStep` field type.  This is the ONE non-sequence-independent field
that has a landed supplier already in the tree — the loop-body span both `iterSeam`
and this consume. -/

/-- **`seqStep`, from `IterSeamResid`.**  A sequence entry `(s :: ss)` whose head runs
`.normal` to `st'` steps ≥ 1 to the tail sequence entry `ss` at `st'`.  Reuses the
`iterSeam` loop-body span (`iterSeam_of_resid`) verbatim, forgetting nothing but the
intermediate config equality. -/
theorem seqStep_class
    (Reflect : Config → Addr → List Stmt → Prop)
    (hIter : Vsa.Sim.IterSeamAssembly.IterSeamResid Reflect) :
    ∀ (c : Config) (st st' : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt),
      ExecS st d env s st' .normal → SqEntryC Reflect c st d env (s :: ss) →
      LandedN 1 c (fun c' => SqEntryC Reflect c' st' d env ss) := by
  intro c st st' d env s ss hExec hSq
  obtain ⟨g, N, A, SL, φf, φc, dLeft, aLeft, m0, hSeg, hRefl⟩ := hSq
  obtain ⟨m, c₁, cH', g', N', A', SL', φf', φc', dLeft', aLeft', m0',
          hm, hstep, hstep0, hSeg', hRefl'⟩ :=
    Vsa.Sim.IterSeamAssembly.iterSeam_of_resid Reflect hIter
      st d env s ss st' hExec c g N A SL φf φc dLeft aLeft m0 hSeg hRefl
  -- `StepsN 0 c₁ cH'` ⇒ `c₁ = cH'`, so the ≥1-step run already lands at `cH'`.
  cases hstep0 with
  | zero =>
    exact ⟨m, c₁, hm, hstep,
      ⟨g', N', A', SL', φf', φc', dLeft', aLeft', m0', hSeg', hRefl'⟩⟩

#print axioms seqStep_class

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

structure ApproxArmResid
    (Reflect : Config → Addr → List Stmt → Prop)
    (EEntry : Config → SpecSt → Nat → Addr → Expr → Prop)
    (AEntry : Config → SpecSt → Nat → Addr → List Expr → Prop)
    (CEntry : Config → SpecSt → Nat → Value → List Value → Prop)
    (SEntry : Config → SpecSt → Nat → Addr → Stmt → Prop)
    (FEntry : Config → SpecSt → Nat → Addr → Option Expr → Option Expr → Stmt → Prop)
    : Prop where
  ------------------------------------------------------------------ EApprox
  assignE : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr),
    EEntry c st d env (.assign x e) →
    LandedN 1 c (fun c' => EEntry c' st d env e)
  binaryL : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr),
    EEntry c st d env (.binary op l r) →
    LandedN 1 c (fun c' => EEntry c' st d env l)
  binaryR : ∀ (c : Config) (st st' : SpecSt) (d : Nat) (env : Addr) (op : BinOp)
    (l r : Expr) (lv : Value),
    EvalE st d env l st' lv → EEntry c st d env (.binary op l r) →
    LandedN 1 c (fun c' => EEntry c' st' d env r)
  logicalL : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (lop : Vsa.While.LogOp)
    (l r : Expr),
    EEntry c st d env (.logical lop l r) →
    LandedN 1 c (fun c' => EEntry c' st d env l)
  logicalR : ∀ (c : Config) (st st' : SpecSt) (d : Nat) (env : Addr)
    (lop : Vsa.While.LogOp) (l r : Expr) (lv : Value),
    EvalE st d env l st' lv → EEntry c st d env (.logical lop l r) →
    LandedN 1 c (fun c' => EEntry c' st' d env r)
  unaryE : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (op : UnOp) (e : Expr),
    EEntry c st d env (.unary op e) →
    LandedN 1 c (fun c' => EEntry c' st d env e)
  callF : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (f : Expr)
    (args : List Expr),
    EEntry c st d env (.call f args) →
    LandedN 1 c (fun c' => EEntry c' st d env f)
  callArgs : ∀ (c : Config) (st st' : SpecSt) (d : Nat) (env : Addr) (f : Expr)
    (args : List Expr) (fv : Value),
    EvalE st d env f st' fv → EEntry c st d env (.call f args) →
    LandedN 1 c (fun c' => AEntry c' st' d env args)
  callC : ∀ (c : Config) (st st' st'' : SpecSt) (d : Nat) (env : Addr) (f : Expr)
    (args : List Expr) (fv : Value) (vs : List Value),
    EvalE st d env f st' fv → EvalArgs st' d env args st'' vs →
    EEntry c st d env (.call f args) →
    LandedN 1 c (fun c' => CEntry c' st'' d fv vs)
  ------------------------------------------------------------------ ArgsApprox
  argsHead : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (e : Expr)
    (es : List Expr),
    AEntry c st d env (e :: es) →
    LandedN 1 c (fun c' => EEntry c' st d env e)
  argsTail : ∀ (c : Config) (st st' : SpecSt) (d : Nat) (env : Addr) (e : Expr)
    (es : List Expr) (v : Value),
    EvalE st d env e st' v → AEntry c st d env (e :: es) →
    LandedN 1 c (fun c' => AEntry c' st' d env es)
  ------------------------------------------------------------------ CApprox
  callBody : ∀ (c : Config) (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData)
    (vs : List Value) (store' : Store) (frame : Addr),
    st.store.closures[a]? = some cd → vs.length = cd.params.length →
    d < Vsa.While.maxCallDepth →
    Vsa.While.Store.allocFrame st.store (some cd.env) = (store', frame) →
    CEntry c st d (.closure a) vs →
    LandedN 1 c (fun c' => SqEntryC Reflect c'
      ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store', st.out⟩
      (d + 1) frame cd.body)
  ------------------------------------------------------------------ SApprox
  stmtExpr : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (e : Expr),
    SEntry c st d env (.expr e) →
    LandedN 1 c (fun c' => EEntry c' st d env e)
  stmtRet : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (e : Expr),
    SEntry c st d env (.ret (some e)) →
    LandedN 1 c (fun c' => EEntry c' st d env e)
  stmtVarInit : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (x : String)
    (e : Expr),
    SEntry c st d env (.varDecl x (some e)) →
    LandedN 1 c (fun c' => EEntry c' st d env e)
  stmtBlock : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (ss : List Stmt)
    (store' : Store) (inner : Addr),
    st.store.allocFrame (some env) = (store', inner) →
    SEntry c st d env (.block ss) →
    LandedN 1 c (fun c' => SqEntryC Reflect c' ⟨store', st.out⟩ d inner ss)
  stmtIfCond : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr)
    (t : Stmt) (e : Option Stmt),
    SEntry c st d env (.ifStmt cnd t e) →
    LandedN 1 c (fun c' => EEntry c' st d env cnd)
  stmtIfThen : ∀ (c : Config) (st st' : SpecSt) (d : Nat) (env : Addr) (cnd : Expr)
    (t : Stmt) (e : Option Stmt) (v : Value),
    EvalE st d env cnd st' v → v.truthy = true → SEntry c st d env (.ifStmt cnd t e) →
    LandedN 1 c (fun c' => SEntry c' st' d env t)
  stmtIfElse : ∀ (c : Config) (st st' : SpecSt) (d : Nat) (env : Addr) (cnd : Expr)
    (t e : Stmt) (v : Value),
    EvalE st d env cnd st' v → v.truthy = false → SEntry c st d env (.ifStmt cnd t (some e)) →
    LandedN 1 c (fun c' => SEntry c' st' d env e)
  stmtWhileCond : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (b : Stmt),
    SEntry c st d env (.whileStmt cnd b) →
    LandedN 1 c (fun c' => EEntry c' st d env cnd)
  stmtWhileBody : ∀ (c : Config) (st st' : SpecSt) (d : Nat) (env : Addr) (cnd : Expr)
    (b : Stmt) (v : Value),
    EvalE st d env cnd st' v → v.truthy = true → SEntry c st d env (.whileStmt cnd b) →
    LandedN 1 c (fun c' => SEntry c' st' d env b)
  stmtWhileLoop : ∀ (c : Config) (st st' st'' : SpecSt) (d : Nat) (env : Addr)
    (cnd : Expr) (b : Stmt) (v : Value) (status : Status),
    EvalE st d env cnd st' v → v.truthy = true →
    ExecS st' d env b st'' status → (status = .normal ∨ status = .cont) →
    SEntry c st d env (.whileStmt cnd b) →
    LandedN 1 c (fun c' => SEntry c' st'' d env (.whileStmt cnd b))
  stmtForInit : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (init : Stmt)
    (cnd step : Option Expr) (b : Stmt) (store' : Store) (outer : Addr),
    st.store.allocFrame (some env) = (store', outer) →
    SEntry c st d env (.forStmt (some init) cnd step b) →
    LandedN 1 c (fun c' => SEntry c' ⟨store', st.out⟩ d outer init)
  stmtForLoop : ∀ (c : Config) (st st' : SpecSt) (d : Nat) (env : Addr)
    (init : Option Stmt) (cnd step : Option Expr) (b : Stmt) (store' : Store) (outer : Addr),
    st.store.allocFrame (some env) = (store', outer) →
    ExecInit ⟨store', st.out⟩ d outer init st' →
    SEntry c st d env (.forStmt init cnd step b) →
    LandedN 1 c (fun c' => FEntry c' st' d outer cnd step b)
  ------------------------------------------------------------------ FlApprox
  flCond : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (cc : Expr)
    (step : Option Expr) (b : Stmt),
    FEntry c st d env (some cc) step b →
    LandedN 1 c (fun c' => EEntry c' st d env cc)
  flBody : ∀ (c : Config) (st st' : SpecSt) (d : Nat) (env : Addr) (cnd : Option Expr)
    (step : Option Expr) (b : Stmt),
    ForCond st d env cnd st' → FEntry c st d env cnd step b →
    LandedN 1 c (fun c' => SEntry c' st' d env b)
  flStep : ∀ (c : Config) (st st' st'' : SpecSt) (d : Nat) (env : Addr) (cnd : Option Expr)
    (e : Expr) (b : Stmt) (status : Status),
    ForCond st d env cnd st' → ExecS st' d env b st'' status →
    (status = .normal ∨ status = .cont) → FEntry c st d env cnd (some e) b →
    LandedN 1 c (fun c' => EEntry c' st'' d env e)
  flLoop : ∀ (c : Config) (st st' st'' st''' : SpecSt) (d : Nat) (env : Addr)
    (cnd : Option Expr) (step : Option Expr) (b : Stmt) (status : Status),
    ForCond st d env cnd st' → ExecS st' d env b st'' status →
    (status = .normal ∨ status = .cont) → ExecStep st'' d env step st''' →
    FEntry c st d env cnd step b →
    LandedN 1 c (fun c' => FEntry c' st''' d env cnd step b)
  ------------------------------------------------------------------ Approx.head (SEntry-landing)
  /-- `Approx.head`: a sequence entry `(s :: ss)` whose head is still running ⇒ 1 step
  to the head statement's `SEntry`.  SUPPLIER: the loop-head dispatch prefix
  (`loopHeadDispatch_span`), forgetting the `ExecEntry` post.  This lands at the
  interior `SEntry`, so it is an ARM-class residual (not sequence-supplied). -/
  seqHead : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt)
    (ss : List Stmt),
    SqEntryC Reflect c st d env (s :: ss) →
    LandedN 1 c (fun c' => SEntry c' st d env s)

/-! ## §4. `approxDispatch_of_armResid` — assemble the full `ApproxDispatch`

The full 37-field `ApproxDispatch` from `ApproxArmResid` (35 fields, projected) +
the concrete `seqStep_class` (from `IterSeamResid`).  `SqEntryC Reflect` is the
concrete sixth entry; the other five stay the abstract parameters `ApproxArmResid`
was closed over. -/

theorem approxDispatch_of_armResid
    (Reflect : Config → Addr → List Stmt → Prop)
    (EEntry : Config → SpecSt → Nat → Addr → Expr → Prop)
    (AEntry : Config → SpecSt → Nat → Addr → List Expr → Prop)
    (CEntry : Config → SpecSt → Nat → Value → List Value → Prop)
    (SEntry : Config → SpecSt → Nat → Addr → Stmt → Prop)
    (FEntry : Config → SpecSt → Nat → Addr → Option Expr → Option Expr → Stmt → Prop)
    (hIter : Vsa.Sim.IterSeamAssembly.IterSeamResid Reflect)
    (R : ApproxArmResid Reflect EEntry AEntry CEntry SEntry FEntry) :
    ApproxDispatch EEntry AEntry CEntry SEntry FEntry (SqEntryC Reflect) where
  assignE := R.assignE
  binaryL := R.binaryL
  binaryR := R.binaryR
  logicalL := R.logicalL
  logicalR := R.logicalR
  unaryE := R.unaryE
  callF := R.callF
  callArgs := R.callArgs
  callC := R.callC
  argsHead := R.argsHead
  argsTail := R.argsTail
  callBody := R.callBody
  stmtExpr := R.stmtExpr
  stmtRet := R.stmtRet
  stmtVarInit := R.stmtVarInit
  stmtBlock := R.stmtBlock
  stmtIfCond := R.stmtIfCond
  stmtIfThen := R.stmtIfThen
  stmtIfElse := R.stmtIfElse
  stmtWhileCond := R.stmtWhileCond
  stmtWhileBody := R.stmtWhileBody
  stmtWhileLoop := R.stmtWhileLoop
  stmtForInit := R.stmtForInit
  stmtForLoop := R.stmtForLoop
  flCond := R.flCond
  flBody := R.flBody
  flStep := R.flStep
  flLoop := R.flLoop
  seqStep := seqStep_class Reflect hIter
  seqHead := R.seqHead

#print axioms approxDispatch_of_armResid

/-! ## §5. The composing capstone — `divFamily_of_armResid`

Threading `approxDispatch_of_armResid` into `ApproxSeamFold.divFamily_of_assemblies`
with the concrete `SqEntryC` and the definitional `hSqEntry` (`sqEntryC_of_seg`).
The `DivFamily L` is closed on: the shared entry drive (`hEntry`), the iter loop-body
assembly (`hIter : IterSeamResid` — which ALSO supplies `seqStep`), and the arm
residual (`R : ApproxArmResid`).  So the WHOLE divergence arm reduces to `hEntry` +
`hIter` + the per-class `ApproxArmResid` — the sequence class is fully discharged,
`seqStep` for free from `hIter`, `hSqEntry` definitional; only the interior-entry arm
classes remain (one supplier per seg class, upstream). -/

theorem divFamily_of_armResid
    (Reflect : Config → Addr → List Stmt → Prop) (L : Layout)
    (EEntry : Config → SpecSt → Nat → Addr → Expr → Prop)
    (AEntry : Config → SpecSt → Nat → Addr → List Expr → Prop)
    (CEntry : Config → SpecSt → Nat → Value → List Value → Prop)
    (SEntry : Config → SpecSt → Nat → Addr → Stmt → Prop)
    (FEntry : Config → SpecSt → Nat → Addr → Option Expr → Option Expr → Stmt → Prop)
    (hEntry : Vsa.Sim.DivCorrClose.DivEntryDrive Reflect L)
    (hIter : Vsa.Sim.IterSeamAssembly.IterSeamResid Reflect)
    (R : ApproxArmResid Reflect EEntry AEntry CEntry SEntry FEntry) :
    Vsa.Sim.InterpSimBundle.DivFamily L :=
  Vsa.Sim.ApproxSeamFold.divFamily_of_assemblies
    EEntry AEntry CEntry SEntry FEntry (SqEntryC Reflect) Reflect L
    hEntry hIter
    (approxDispatch_of_armResid Reflect EEntry AEntry CEntry SEntry FEntry hIter R)
    (sqEntryC_of_seg Reflect)

#print axioms divFamily_of_armResid

end Vsa.Sim.ApproxDispatchSuppliers
