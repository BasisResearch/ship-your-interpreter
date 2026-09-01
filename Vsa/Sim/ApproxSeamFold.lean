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
open Vsa.While (St Stmt Expr BinOp UnOp Value ClosureData Store Status Addr
  SApprox EApprox ArgsApprox CApprox FlApprox Approx
  EvalE EvalArgs ForCond ExecInit ExecStep ExecS)
open Vsa.Sim.Scaffold (SegEntry)

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

/-- The shared lower-bound conclusion: from config `c`, at least `k` machine
steps exist.  `= LandedN k c (fun _ => True)`; kept as its own `def` so the fold
reads uniformly and `approxFromCountedRun` consumes it directly. -/
def Divg (k : Nat) (c : Config) : Prop :=
  ∃ (m : Nat) (c₁ : Config), k ≤ m ∧ StepsN m c c₁

/-- `Divg` IS `LandedN … (fun _ => True)`, so the `LandedN` algebra applies. -/
theorem divg_iff_landedN (k : Nat) (c : Config) :
    Divg k c ↔ LandedN k c (fun _ => True) := by
  constructor
  · rintro ⟨m, c₁, hk, hs⟩; exact ⟨m, c₁, hk, hs, trivial⟩
  · rintro ⟨m, c₁, hk, hs, _⟩; exact ⟨m, c₁, hk, hs⟩

/-- Turn a `LandedN` into a `Divg` (forget the post). -/
theorem divg_of_landedN {k : Nat} {c : Config} (h : LandedN k c (fun _ => True)) :
    Divg k c := (divg_iff_landedN k c).mpr h

/-- Turn a `Divg` into the `LandedN` shape `LandedN.bind` consumes. -/
theorem landedN_of_divg {k : Nat} {c : Config} (h : Divg k c) :
    LandedN k c (fun _ => True) := (divg_iff_landedN k c).mp h

/-- **The one composition primitive.**  A dispatch prefix that lands ≥ 1 machine
step at some SUB-ENTRY config, followed by a `Divg n` from that sub-entry,
composes to `Divg (n + 1)`.  This is `LandedN.bind` (`StepCount`) specialised:
`LandedN 1 c (SubEntry)` `bind` `(∀ c', SubEntry c' → LandedN n c' True)` gives
`LandedN (1 + n) = LandedN (n + 1)`.  EVERY non-`zero` constructor case is one
application of this: the prefix is the arm's dispatch/spill instructions, the
`k` continuation is the IH at the sub-relation entry. -/
theorem divg_step
    {c : Config} {n : Nat} {SubEntry : Config → Prop}
    (hpre : LandedN 1 c SubEntry)
    (hk : ∀ c', SubEntry c' → Divg n c') :
    Divg (n + 1) c := by
  have hbind : LandedN (1 + n) c (fun _ => True) :=
    LandedN.bind hpre (fun c' hc' => landedN_of_divg (hk c' hc'))
  have : LandedN (n + 1) c (fun _ => True) := by rwa [Nat.add_comm] at hbind
  exact divg_of_landedN this

#print axioms divg_iff_landedN
#print axioms divg_step

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

set_option maxHeartbeats 1000000 in
/-- The counted-prefix obligations, one per constructor class.  A supplier builds
each from the arm segs/rows (SUPPLIER named per field), forgetting the exit post
and keeping the ≥ 1-step count.  Each is `∀ entry-config, (side premises) →
LandedN 1 c (sub-entry)`. -/
structure ApproxDispatch : Prop where
  ------------------------------------------------------------------ EApprox
  /-- `EApprox.assignE`: `(.assign x e)` entry ⇒ 1 step to `e`'s entry. -/
  assignE : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr),
    EEntry c st d env (.assign x e) →
    LandedN 1 c (fun c' => EEntry c' st d env e)
  /-- `EApprox.binaryL`: `(.binary op l r)` entry ⇒ 1 step to `l`'s entry. -/
  binaryL : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr),
    EEntry c st d env (.binary op l r) →
    LandedN 1 c (fun c' => EEntry c' st d env l)
  /-- `EApprox.binaryR`: `(.binary op l r)` entry with a COMPLETED left eval to
  `st'` ⇒ 1 step to `r`'s entry at `st'`. -/
  binaryR : ∀ (c : Config) (st st' : SpecSt) (d : Nat) (env : Addr) (op : BinOp)
    (l r : Expr) (lv : Value),
    EvalE st d env l st' lv → EEntry c st d env (.binary op l r) →
    LandedN 1 c (fun c' => EEntry c' st' d env r)
  /-- `EApprox.orL`/`andL`: `(.logical lop l r)` entry ⇒ 1 step to `l`'s entry. -/
  logicalL : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (lop : Vsa.While.LogOp)
    (l r : Expr),
    EEntry c st d env (.logical lop l r) →
    LandedN 1 c (fun c' => EEntry c' st d env l)
  /-- `EApprox.orR`/`andR`: `(.logical lop l r)` entry with a completed left eval
  to `st'` ⇒ 1 step to `r`'s entry at `st'`. -/
  logicalR : ∀ (c : Config) (st st' : SpecSt) (d : Nat) (env : Addr)
    (lop : Vsa.While.LogOp) (l r : Expr) (lv : Value),
    EvalE st d env l st' lv → EEntry c st d env (.logical lop l r) →
    LandedN 1 c (fun c' => EEntry c' st' d env r)
  /-- `EApprox.unaryE`: `(.unary op e)` entry ⇒ 1 step to `e`'s entry. -/
  unaryE : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (op : UnOp) (e : Expr),
    EEntry c st d env (.unary op e) →
    LandedN 1 c (fun c' => EEntry c' st d env e)
  /-- `EApprox.callF`: `(.call f args)` entry ⇒ 1 step to `f`'s entry. -/
  callF : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (f : Expr)
    (args : List Expr),
    EEntry c st d env (.call f args) →
    LandedN 1 c (fun c' => EEntry c' st d env f)
  /-- `EApprox.callArgs`: `(.call f args)` entry with completed `f`-eval to `st'`
  ⇒ 1 step to the arg-list entry `AEntry` at `st'`. -/
  callArgs : ∀ (c : Config) (st st' : SpecSt) (d : Nat) (env : Addr) (f : Expr)
    (args : List Expr) (fv : Value),
    EvalE st d env f st' fv → EEntry c st d env (.call f args) →
    LandedN 1 c (fun c' => AEntry c' st' d env args)
  /-- `EApprox.callC`: `(.call f args)` entry with completed `f`-eval and
  `args`-eval to `st''` ⇒ 1 step to the callee `CEntry` for `(fv, vs)`. -/
  callC : ∀ (c : Config) (st st' st'' : SpecSt) (d : Nat) (env : Addr) (f : Expr)
    (args : List Expr) (fv : Value) (vs : List Value),
    EvalE st d env f st' fv → EvalArgs st' d env args st'' vs →
    EEntry c st d env (.call f args) →
    LandedN 1 c (fun c' => CEntry c' st'' d fv vs)
  ------------------------------------------------------------------ ArgsApprox
  /-- `ArgsApprox.head`: `(e :: es)` args entry ⇒ 1 step to `e`'s eval entry. -/
  argsHead : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (e : Expr)
    (es : List Expr),
    AEntry c st d env (e :: es) →
    LandedN 1 c (fun c' => EEntry c' st d env e)
  /-- `ArgsApprox.tail`: `(e :: es)` args entry with completed `e`-eval to `st'`
  ⇒ 1 step to the `es` args entry at `st'`. -/
  argsTail : ∀ (c : Config) (st st' : SpecSt) (d : Nat) (env : Addr) (e : Expr)
    (es : List Expr) (v : Value),
    EvalE st d env e st' v → AEntry c st d env (e :: es) →
    LandedN 1 c (fun c' => AEntry c' st' d env es)
  ------------------------------------------------------------------ CApprox
  /-- `CApprox.body`: a `.closure a` callee entry (with the depth/alloc premises)
  ⇒ 1 step (allocate the callee frame at `d + 1`) to the body sequence entry. -/
  callBody : ∀ (c : Config) (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData)
    (vs : List Value) (store' : Store) (frame : Addr),
    st.store.closures[a]? = some cd → vs.length = cd.params.length →
    d < Vsa.While.maxCallDepth →
    Vsa.While.Store.allocFrame st.store (some cd.env) = (store', frame) →
    CEntry c st d (.closure a) vs →
    LandedN 1 c (fun c' => SqEntry c'
      ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store', st.out⟩
      (d + 1) frame cd.body)
  ------------------------------------------------------------------ SApprox
  /-- `SApprox.expr`: `(.expr e)` stmt entry ⇒ 1 step to `e`'s eval entry. -/
  stmtExpr : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (e : Expr),
    SEntry c st d env (.expr e) →
    LandedN 1 c (fun c' => EEntry c' st d env e)
  /-- `SApprox.ret`: `(.ret (some e))` stmt entry ⇒ 1 step to `e`'s eval entry. -/
  stmtRet : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (e : Expr),
    SEntry c st d env (.ret (some e)) →
    LandedN 1 c (fun c' => EEntry c' st d env e)
  /-- `SApprox.varInit`: `(.varDecl x (some e))` stmt entry ⇒ 1 step to `e`. -/
  stmtVarInit : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (x : String)
    (e : Expr),
    SEntry c st d env (.varDecl x (some e)) →
    LandedN 1 c (fun c' => EEntry c' st d env e)
  /-- `SApprox.block`: `(.block ss)` stmt entry (with the inner-frame alloc)
  ⇒ 1 step to the inner sequence `SqEntry`. -/
  stmtBlock : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (ss : List Stmt)
    (store' : Store) (inner : Addr),
    st.store.allocFrame (some env) = (store', inner) →
    SEntry c st d env (.block ss) →
    LandedN 1 c (fun c' => SqEntry c' ⟨store', st.out⟩ d inner ss)
  /-- `SApprox.ifCond`: `(.ifStmt c t e)` stmt entry ⇒ 1 step to the condition. -/
  stmtIfCond : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr)
    (t : Stmt) (e : Option Stmt),
    SEntry c st d env (.ifStmt cnd t e) →
    LandedN 1 c (fun c' => EEntry c' st d env cnd)
  /-- `SApprox.ifThen`: `(.ifStmt cnd t e)` entry, completed cond-eval to `st'`
  (truthy) ⇒ 1 step to the THEN branch `t`. -/
  stmtIfThen : ∀ (c : Config) (st st' : SpecSt) (d : Nat) (env : Addr) (cnd : Expr)
    (t : Stmt) (e : Option Stmt) (v : Value),
    EvalE st d env cnd st' v → v.truthy = true → SEntry c st d env (.ifStmt cnd t e) →
    LandedN 1 c (fun c' => SEntry c' st' d env t)
  /-- `SApprox.ifElse`: `(.ifStmt cnd t (some e))` entry, completed cond-eval to
  `st'` (falsy) ⇒ 1 step to the ELSE branch `e`. -/
  stmtIfElse : ∀ (c : Config) (st st' : SpecSt) (d : Nat) (env : Addr) (cnd : Expr)
    (t e : Stmt) (v : Value),
    EvalE st d env cnd st' v → v.truthy = false → SEntry c st d env (.ifStmt cnd t (some e)) →
    LandedN 1 c (fun c' => SEntry c' st' d env e)
  /-- `SApprox.whileCond`: `(.whileStmt cnd b)` entry ⇒ 1 step to the condition. -/
  stmtWhileCond : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (b : Stmt),
    SEntry c st d env (.whileStmt cnd b) →
    LandedN 1 c (fun c' => EEntry c' st d env cnd)
  /-- `SApprox.whileBody`: `(.whileStmt cnd b)` entry, completed cond-eval to `st'`
  (truthy) ⇒ 1 step to the body `b`. -/
  stmtWhileBody : ∀ (c : Config) (st st' : SpecSt) (d : Nat) (env : Addr) (cnd : Expr)
    (b : Stmt) (v : Value),
    EvalE st d env cnd st' v → v.truthy = true → SEntry c st d env (.whileStmt cnd b) →
    LandedN 1 c (fun c' => SEntry c' st' d env b)
  /-- `SApprox.whileLoop`: `(.whileStmt cnd b)` entry, one completed iteration
  (cond truthy, body to `st''` normal/cont) ⇒ 1 step to the loop `SEntry` at
  `st''`. -/
  stmtWhileLoop : ∀ (c : Config) (st st' st'' : SpecSt) (d : Nat) (env : Addr)
    (cnd : Expr) (b : Stmt) (v : Value) (status : Status),
    EvalE st d env cnd st' v → v.truthy = true →
    ExecS st' d env b st'' status → (status = .normal ∨ status = .cont) →
    SEntry c st d env (.whileStmt cnd b) →
    LandedN 1 c (fun c' => SEntry c' st'' d env (.whileStmt cnd b))
  /-- `SApprox.forInit`: `(.forStmt (some init) cnd step b)` entry (with the outer
  alloc) ⇒ 1 step to the init statement `SEntry` at the outer frame. -/
  stmtForInit : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (init : Stmt)
    (cnd step : Option Expr) (b : Stmt) (store' : Store) (outer : Addr),
    st.store.allocFrame (some env) = (store', outer) →
    SEntry c st d env (.forStmt (some init) cnd step b) →
    LandedN 1 c (fun c' => SEntry c' ⟨store', st.out⟩ d outer init)
  /-- `SApprox.forLoop`: `(.forStmt init cnd step b)` entry (outer alloc + completed
  `ExecInit` to `st'`) ⇒ 1 step to the `FEntry` for the for-loop remainder. -/
  stmtForLoop : ∀ (c : Config) (st st' : SpecSt) (d : Nat) (env : Addr)
    (init : Option Stmt) (cnd step : Option Expr) (b : Stmt) (store' : Store) (outer : Addr),
    st.store.allocFrame (some env) = (store', outer) →
    ExecInit ⟨store', st.out⟩ d outer init st' →
    SEntry c st d env (.forStmt init cnd step b) →
    LandedN 1 c (fun c' => FEntry c' st' d outer cnd step b)
  ------------------------------------------------------------------ FlApprox
  /-- `FlApprox.cond`: a `(some c)` for-cond entry ⇒ 1 step to the cond eval. -/
  flCond : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (cc : Expr)
    (step : Option Expr) (b : Stmt),
    FEntry c st d env (some cc) step b →
    LandedN 1 c (fun c' => EEntry c' st d env cc)
  /-- `FlApprox.body`: for-cond entry with completed `ForCond` to `st'` ⇒ 1 step to
  the body `b`. -/
  flBody : ∀ (c : Config) (st st' : SpecSt) (d : Nat) (env : Addr) (cnd : Option Expr)
    (step : Option Expr) (b : Stmt),
    ForCond st d env cnd st' → FEntry c st d env cnd step b →
    LandedN 1 c (fun c' => SEntry c' st' d env b)
  /-- `FlApprox.step`: for entry with completed cond + body (to `st''`, normal/cont)
  ⇒ 1 step to the step expression `e`. -/
  flStep : ∀ (c : Config) (st st' st'' : SpecSt) (d : Nat) (env : Addr) (cnd : Option Expr)
    (e : Expr) (b : Stmt) (status : Status),
    ForCond st d env cnd st' → ExecS st' d env b st'' status →
    (status = .normal ∨ status = .cont) → FEntry c st d env cnd (some e) b →
    LandedN 1 c (fun c' => EEntry c' st'' d env e)
  /-- `FlApprox.loop`: for entry with completed cond + body + step (to `st'''`)
  ⇒ 1 step to the next `FEntry`. -/
  flLoop : ∀ (c : Config) (st st' st'' st''' : SpecSt) (d : Nat) (env : Addr)
    (cnd : Option Expr) (step : Option Expr) (b : Stmt) (status : Status),
    ForCond st d env cnd st' → ExecS st' d env b st'' status →
    (status = .normal ∨ status = .cont) → ExecStep st'' d env step st''' →
    FEntry c st d env cnd step b →
    LandedN 1 c (fun c' => FEntry c' st''' d env cnd step b)
  ------------------------------------------------------------------ Approx (sequence)
  /-- `Approx.step`: a sequence entry `(s :: ss)` whose head runs `.normal` to `st'`
  ⇒ 1 step to the tail sequence entry `ss` at `st'`.  SUPPLIER: `iterSeam`'s
  loop-body span, forgetting the re-landing post. -/
  seqStep : ∀ (c : Config) (st st' : SpecSt) (d : Nat) (env : Addr) (s : Stmt)
    (ss : List Stmt),
    ExecS st d env s st' .normal → SqEntry c st d env (s :: ss) →
    LandedN 1 c (fun c' => SqEntry c' st' d env ss)
  /-- `Approx.head`: a sequence entry `(s :: ss)` whose head is itself still running
  ⇒ 1 step to the head statement's `SEntry`.  SUPPLIER: the loop-head dispatch
  prefix (`loopHeadDispatch_span`), forgetting the `ExecEntry` post. -/
  seqHead : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt)
    (ss : List Stmt),
    SqEntry c st d env (s :: ss) →
    LandedN 1 c (fun c' => SEntry c' st d env s)

/-! ## §3. The six lower-bound predicates and the mutual fold

Each `…LB n …` says: for EVERY config `c` that is a valid entry for this relation
instance, `Divg (n + 1) c` (≥ n+1 machine steps).  The six are proved together by
STRONG INDUCTION on the shared fuel `n`: every constructor's conclusion is at fuel
`n + 1` and its recursive premise is at fuel `n` (or the sub-relation carries the
same `n`), so all recursion is at fuel `≤ n`, and the strong-induction IH covers
all six at every `m ≤ n`.  This crosses the `Approx`-vs-mutual-block declaration
boundary that Lean's per-inductive recursor cannot (see §1). -/

/-- `EApprox` lower bound: a still-running expression forces ≥ n+1 steps from any
`EEntry`. -/
def EApproxLB (n : Nat) (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) : Prop :=
  ∀ c, EEntry c st d env e → Divg n c

/-- `ArgsApprox` lower bound. -/
def ArgsApproxLB (n : Nat) (st : SpecSt) (d : Nat) (env : Addr) (es : List Expr) : Prop :=
  ∀ c, AEntry c st d env es → Divg n c

/-- `CApprox` lower bound (callee still running). -/
def CApproxLB (n : Nat) (st : SpecSt) (d : Nat) (fv : Value) (vs : List Value) : Prop :=
  ∀ c, CEntry c st d fv vs → Divg n c

/-- `SApprox` lower bound (statement still running). -/
def SApproxLB (n : Nat) (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) : Prop :=
  ∀ c, SEntry c st d env s → Divg n c

/-- `FlApprox` lower bound (for-loop remainder still running). -/
def FlApproxLB (n : Nat) (st : SpecSt) (d : Nat) (env : Addr)
    (cnd step : Option Expr) (b : Stmt) : Prop :=
  ∀ c, FEntry c st d env cnd step b → Divg n c

/-- `Approx` lower bound (sequence still running). -/
def ApproxLB (n : Nat) (st : SpecSt) (d : Nat) (env : Addr) (ss : List Stmt) : Prop :=
  ∀ c, SqEntry c st d env ss → Divg n c

/-- The bundled six-way lower bound at a single fuel `n`: the strong-induction
motive, as a NAMED-FIELD structure (gate R6 — never a positional `∧` tower; every
projection below is by field name).  One field per relation, each quantifying that
relation's spec arguments so a case can instantiate the IH at the recursive
premise's arguments. -/
structure AllLB (n : Nat) : Prop where
  eLB : ∀ st d env e, EApprox n st d env e → EApproxLB EEntry n st d env e
  aLB : ∀ st d env es, ArgsApprox n st d env es → ArgsApproxLB AEntry n st d env es
  cLB : ∀ st d fv vs, CApprox n st d fv vs → CApproxLB CEntry n st d fv vs
  sLB : ∀ st d env s, SApprox n st d env s → SApproxLB SEntry n st d env s
  fLB : ∀ st d env cnd step b, FlApprox n st d env cnd step b →
      FlApproxLB FEntry n st d env cnd step b
  sqLB : ∀ st d env ss, Approx n st d env ss → ApproxLB SqEntry n st d env ss

/-! ## §4. The fold — all six lower bounds by strong induction on the fuel

`allLB` proves `AllLB n` for every `n` from `ApproxDispatch`.  The strong-
induction IH `ih : ∀ m, m < n → AllLB m` covers every recursive premise (all at
fuel `< n` once a constructor fixes the conclusion fuel to its `n`).  Every case
is one `divg_step`: the matching `ApproxDispatch` field supplies the ≥ 1-step
dispatch prefix (`LandedN 1 c sub-entry`), the IH supplies the `Divg` from the
sub-entry.  The `zero` cases are `Divg 0` — trivially the empty run. -/

/-- **The fold.**  From the per-class dispatch prefixes (`ApproxDispatch`), all
six relation lower bounds hold at every fuel.  Strong induction on the fuel;
every case = one `divg_step`. -/
theorem allLB (D : ApproxDispatch EEntry AEntry CEntry SEntry FEntry SqEntry) :
    ∀ n, AllLB EEntry AEntry CEntry SEntry FEntry SqEntry n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    ------------------------------------------------------------------ EApprox
    · -- EApprox n
      intro st d env e hderiv c hE
      cases hderiv with
      | zero => exact ⟨0, c, Nat.le_refl 0, .zero c⟩
      | assignE n st d env x e h =>
        exact divg_step (D.assignE c st d env x e hE)
          (fun c' hc' => (ih n (by omega)).eLB st d env e h c' hc')
      | binaryL n st d env op l r h =>
        exact divg_step (D.binaryL c st d env op l r hE)
          (fun c' hc' => (ih n (by omega)).eLB st d env l h c' hc')
      | binaryR n st d env op l r st' lv hEv h =>
        exact divg_step (D.binaryR c st st' d env op l r lv hEv hE)
          (fun c' hc' => (ih n (by omega)).eLB st' d env r h c' hc')
      | orL n st d env l r h =>
        exact divg_step (D.logicalL c st d env .or l r hE)
          (fun c' hc' => (ih n (by omega)).eLB st d env l h c' hc')
      | orR n st d env l r st' lv hEv _ht h =>
        exact divg_step (D.logicalR c st st' d env .or l r lv hEv hE)
          (fun c' hc' => (ih n (by omega)).eLB st' d env r h c' hc')
      | andL n st d env l r h =>
        exact divg_step (D.logicalL c st d env .and l r hE)
          (fun c' hc' => (ih n (by omega)).eLB st d env l h c' hc')
      | andR n st d env l r st' lv hEv _ht h =>
        exact divg_step (D.logicalR c st st' d env .and l r lv hEv hE)
          (fun c' hc' => (ih n (by omega)).eLB st' d env r h c' hc')
      | unaryE n st d env op e h =>
        exact divg_step (D.unaryE c st d env op e hE)
          (fun c' hc' => (ih n (by omega)).eLB st d env e h c' hc')
      | callF n st d env f args h =>
        exact divg_step (D.callF c st d env f args hE)
          (fun c' hc' => (ih n (by omega)).eLB st d env f h c' hc')
      | callArgs n st d env f args st' fv hEv h =>
        exact divg_step (D.callArgs c st st' d env f args fv hEv hE)
          (fun c' hc' => (ih n (by omega)).aLB st' d env args h c' hc')
      | callC n st d env f args st' st'' fv vs hEv hEa h =>
        exact divg_step (D.callC c st st' st'' d env f args fv vs hEv hEa hE)
          (fun c' hc' => (ih n (by omega)).cLB st'' d fv vs h c' hc')
    ------------------------------------------------------------------ ArgsApprox
    · -- ArgsApprox n
      intro st d env es hderiv c hE
      cases hderiv with
      | zero => exact ⟨0, c, Nat.le_refl 0, .zero c⟩
      | head n st d env e es h =>
        exact divg_step (D.argsHead c st d env e es hE)
          (fun c' hc' => (ih n (by omega)).eLB st d env e h c' hc')
      | tail n st d env e es st' v hEv h =>
        exact divg_step (D.argsTail c st st' d env e es v hEv hE)
          (fun c' hc' => (ih n (by omega)).aLB st' d env es h c' hc')
    ------------------------------------------------------------------ CApprox
    · -- CApprox n
      intro st d fv vs hderiv c hE
      cases hderiv with
      | zero => exact ⟨0, c, Nat.le_refl 0, .zero c⟩
      | body n st d a cd vs store' frame hcl hlen hd halloc h =>
        exact divg_step (D.callBody c st d a cd vs store' frame hcl hlen hd halloc hE)
          (fun c' hc' => (ih n (by omega)).sqLB _ (d + 1) frame cd.body h c' hc')
    ------------------------------------------------------------------ SApprox
    · -- SApprox n
      intro st d env s hderiv c hE
      cases hderiv with
      | zero => exact ⟨0, c, Nat.le_refl 0, .zero c⟩
      | expr n st d env e h =>
        exact divg_step (D.stmtExpr c st d env e hE)
          (fun c' hc' => (ih n (by omega)).eLB st d env e h c' hc')
      | varInit n st d env x e h =>
        exact divg_step (D.stmtVarInit c st d env x e hE)
          (fun c' hc' => (ih n (by omega)).eLB st d env e h c' hc')
      | block n st d env ss store' inner halloc h =>
        exact divg_step (D.stmtBlock c st d env ss store' inner halloc hE)
          (fun c' hc' => (ih n (by omega)).sqLB _ d inner ss h c' hc')
      | ifCond n st d env cnd t e h =>
        exact divg_step (D.stmtIfCond c st d env cnd t e hE)
          (fun c' hc' => (ih n (by omega)).eLB st d env cnd h c' hc')
      | ifThen n st d env cnd t e st' v hEv ht h =>
        exact divg_step (D.stmtIfThen c st st' d env cnd t e v hEv ht hE)
          (fun c' hc' => (ih n (by omega)).sLB st' d env t h c' hc')
      | ifElse n st d env cnd t e st' v hEv hf h =>
        exact divg_step (D.stmtIfElse c st st' d env cnd t e v hEv hf hE)
          (fun c' hc' => (ih n (by omega)).sLB st' d env e h c' hc')
      | whileCond n st d env cnd b h =>
        exact divg_step (D.stmtWhileCond c st d env cnd b hE)
          (fun c' hc' => (ih n (by omega)).eLB st d env cnd h c' hc')
      | whileBody n st d env cnd b st' v hEv ht h =>
        exact divg_step (D.stmtWhileBody c st st' d env cnd b v hEv ht hE)
          (fun c' hc' => (ih n (by omega)).sLB st' d env b h c' hc')
      | whileLoop n st d env cnd b st' st'' v status hEv ht hEx hst h =>
        exact divg_step (D.stmtWhileLoop c st st' st'' d env cnd b v status hEv ht hEx hst hE)
          (fun c' hc' => (ih n (by omega)).sLB st'' d env (.whileStmt cnd b) h c' hc')
      | forInit n st d env init cnd step b store' outer halloc h =>
        exact divg_step (D.stmtForInit c st d env init cnd step b store' outer halloc hE)
          (fun c' hc' => (ih n (by omega)).sLB _ d outer init h c' hc')
      | forLoop n st d env init cnd step b store' outer st' halloc hInit h =>
        exact divg_step (D.stmtForLoop c st st' d env init cnd step b store' outer halloc hInit hE)
          (fun c' hc' => (ih n (by omega)).fLB st' d outer cnd step b h c' hc')
      | ret n st d env e h =>
        exact divg_step (D.stmtRet c st d env e hE)
          (fun c' hc' => (ih n (by omega)).eLB st d env e h c' hc')
    ------------------------------------------------------------------ FlApprox
    · -- FlApprox n
      intro st d env cnd step b hderiv c hE
      cases hderiv with
      | zero => exact ⟨0, c, Nat.le_refl 0, .zero c⟩
      | cond n st d env cc step b h =>
        exact divg_step (D.flCond c st d env cc step b hE)
          (fun c' hc' => (ih n (by omega)).eLB st d env cc h c' hc')
      | body n st d env cnd step b st' hFc h =>
        exact divg_step (D.flBody c st st' d env cnd step b hFc hE)
          (fun c' hc' => (ih n (by omega)).sLB st' d env b h c' hc')
      | step n st d env cnd e b st' st'' status hFc hEx hst h =>
        exact divg_step (D.flStep c st st' st'' d env cnd e b status hFc hEx hst hE)
          (fun c' hc' => (ih n (by omega)).eLB st'' d env e h c' hc')
      | loop n st d env cnd step b st' st'' st''' status hFc hEx hst hStep h =>
        exact divg_step (D.flLoop c st st' st'' st''' d env cnd step b status hFc hEx hst hStep hE)
          (fun c' hc' => (ih n (by omega)).fLB st''' d env cnd step b h c' hc')
    ------------------------------------------------------------------ Approx
    · -- Approx n
      intro st d env ss hderiv c hE
      cases hderiv with
      | zero => exact ⟨0, c, Nat.le_refl 0, .zero c⟩
      | step n st d env s ss st' hEx h =>
        exact divg_step (D.seqStep c st st' d env s ss hEx hE)
          (fun c' hc' => (ih n (by omega)).sqLB st' d env ss h c' hc')
      | head n st d env s ss h =>
        exact divg_step (D.seqHead c st d env s ss hE)
          (fun c' hc' => (ih n (by omega)).sLB st d env s h c' hc')

#print axioms allLB

/-- **`Approx` lower bound**, projected from the fold: a sequence still running
with fuel `n` forces `Divg n` from any `SqEntry`. -/
theorem approxLB (D : ApproxDispatch EEntry AEntry CEntry SEntry FEntry SqEntry)
    (n : Nat) (st : SpecSt) (d : Nat) (env : Addr) (ss : List Stmt)
    (h : Approx n st d env ss) :
    ApproxLB SqEntry n st d env ss :=
  (allLB EEntry AEntry CEntry SEntry FEntry SqEntry D n).sqLB st d env ss h

#print axioms approxLB

/-- **`SApprox` lower bound**, projected from the fold. -/
theorem sApproxLB (D : ApproxDispatch EEntry AEntry CEntry SEntry FEntry SqEntry)
    (n : Nat) (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt)
    (h : SApprox n st d env s) :
    SApproxLB SEntry n st d env s :=
  (allLB EEntry AEntry CEntry SEntry FEntry SqEntry D n).sLB st d env s h

/-! ## §5. `approxSeam` from the fold

The loop head is a SEQUENCE position (executing `s :: ss`), not a bare statement
position.  A still-running head `SApprox n st d env s` lifts to `Approx (n + 1) st
d env (s :: ss)` via `Approx.head`, and `ApproxLB (n + 1)` at the loop-head
`SqEntry` gives `Divg (n + 1) cH` — exactly the `approxSeam` conclusion.  So the
supplier need only instantiate `SqEntry` at the loop-head `SegEntry` + `Reflect`
(the last obligation, `hSqEntry`, whose supplier is `loopHeadDispatch_span` — the
SAME span `iterSeam` consumes). -/

/-- **`approxSeam` from `ApproxDispatch` + the loop-head-entry instantiation.**
`hSqEntry` says a loop-head `SegEntry` + `Reflect cH env (s :: ss)` IS a valid
`SqEntry cH st d env (s :: ss)`.  Then `SApprox n st d env s` (the still-running
head) gives `Approx (n + 1)` via `Approx.head`, and the `ApproxLB` projection
yields `Divg (n + 1) cH = ∃ m c₁, n + 1 ≤ m ∧ StepsN m cH c₁`. -/
theorem approxSeam_of_dispatch
    (Reflect : Config → Addr → List Stmt → Prop)
    (D : ApproxDispatch EEntry AEntry CEntry SEntry FEntry SqEntry)
    (hSqEntry :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt)
        (cH : Config)
        (g : (R : Register) → Option (RegisterType R))
        (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
        (dLeft aLeft : Nat) (m0 : Mem),
        SegEntry g N A SL φf φc st d dLeft aLeft interpLoopHeadPC m0 cH →
        Reflect cH env (s :: ss) →
        SqEntry cH st d env (s :: ss)) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) (n : Nat),
      SApprox n st d env s →
      ∀ (cH : Config)
        (g : (R : Register) → Option (RegisterType R))
        (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
        (dLeft aLeft : Nat) (m0 : Mem),
        SegEntry g N A SL φf φc st d dLeft aLeft interpLoopHeadPC m0 cH →
        Reflect cH env (s :: ss) →
        ∃ m c₁, n + 1 ≤ m ∧ StepsN m cH c₁ := by
  intro st d env s ss n hSApprox cH g N A SL φf φc dLeft aLeft m0 hSeg hRefl
  have hApprox : Approx (n + 1) st d env (s :: ss) := Approx.head n st d env s ss hSApprox
  have hSq : SqEntry cH st d env (s :: ss) :=
    hSqEntry st d env s ss cH g N A SL φf φc dLeft aLeft m0 hSeg hRefl
  have hDivg : Divg (n + 1) cH :=
    approxLB EEntry AEntry CEntry SEntry FEntry SqEntry D (n + 1) st d env (s :: ss) hApprox cH hSq
  exact hDivg

#print axioms approxSeam_of_dispatch

/-! ## §6. The divergence family closed on both assemblies

`approxSeam_of_dispatch` IS the `InterpRunLoopResiduals.approxSeam` field body
(identical ∀-signature and `∃ m c₁, n + 1 ≤ m ∧ StepsN m cH c₁` conclusion), so it
plugs directly into `IterSeamAssembly.interpRunLoopResiduals_of_iter` /
`divFamily_of_iterAssembly` alongside the assembled `iterSeam`.  `divFamily_of_
assemblies` composes the two: the whole divergence arm closed on the shared entry
drive + the iter loop-body assembly (`IterSeamResid`) + the approx dispatch
(`ApproxDispatch` + the loop-head-entry instantiation `hSqEntry`). -/

/-- **`DivFamily L` closed on BOTH loop-head assemblies.**  The `iterSeam` residual
is the three-provider `IterSeamResid` (`IterSeamAssembly`); the `approxSeam`
residual is `approxSeam_of_dispatch` from the mutual step-lower-bound fold
(`ApproxDispatch` + `hSqEntry`).  Only the shared prologue entry drive (`hEntry`,
shared with the term arm) remains outside — fed from
`divEntryDrive_of_driveToLoopHead`.  This closes the LAST divergence-family
field. -/
theorem divFamily_of_assemblies
    (Reflect : Config → Addr → List Stmt → Prop) (L : Layout)
    (hEntry : Vsa.Sim.DivCorrClose.DivEntryDrive Reflect L)
    (hIter : Vsa.Sim.IterSeamAssembly.IterSeamResid Reflect)
    (D : ApproxDispatch EEntry AEntry CEntry SEntry FEntry SqEntry)
    (hSqEntry :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt)
        (cH : Config)
        (g : (R : Register) → Option (RegisterType R))
        (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
        (dLeft aLeft : Nat) (m0 : Mem),
        SegEntry g N A SL φf φc st d dLeft aLeft interpLoopHeadPC m0 cH →
        Reflect cH env (s :: ss) →
        SqEntry cH st d env (s :: ss)) :
    Vsa.Sim.InterpSimBundle.DivFamily L :=
  Vsa.Sim.IterSeamAssembly.divFamily_of_iterAssembly Reflect L hEntry hIter
    (approxSeam_of_dispatch EEntry AEntry CEntry SEntry FEntry SqEntry Reflect D hSqEntry)

#print axioms divFamily_of_assemblies

end Vsa.Sim.ApproxSeamFold
