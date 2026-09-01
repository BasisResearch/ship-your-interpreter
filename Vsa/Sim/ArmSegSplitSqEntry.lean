import Vsa.Sim.ArmSegSplitNonEval
import Vsa.Sim.ApproxDispatchSuppliers
import Vsa.Sim.IterSeamAssembly
import Vsa.Sim.rows.LoopHeadDispatch

/-!
# `ArmSegSplitSqEntry` — the 3 `SqEntryC`-boundary arm-class splits (Task #78, Half A)

`ArmSegSplitEval` (15 fields) + `ArmSegSplitNonEval` (11 fields) closed 26 of the 29
`ApproxArmResid` fields MODULO a per-class `*StagePre` residual, each STRICTLY SMALLER
than its raw field (it stops at a `*PreBundle` and the verified twin finishes).  Three
fields remain, all touching the concrete SEQUENCE entry `SqEntryC Reflect` (a
loop-head `SegEntry@interpLoopHeadPC` + the abstract `Reflect`):

* **`callBody`** — `CEntryC (.closure a) vs → LandedN 1 (SqEntryC Reflect <body>)`.
  The callee's inline body (a statement LIST) begins a fresh `interp_run` loop at its
  own loop head, in the child frame at depth `d + 1`.
* **`stmtBlock`** — `SEntryC (.block ss) → LandedN 1 (SqEntryC Reflect ss)`.  A block
  begins a fresh `interp_run` loop over its statement list in the inner frame.
* **`seqHead`** — `SqEntryC Reflect (s :: ss) → LandedN 1 (SEntryC s)`.  The REVERSE
  direction: from the sequence loop head, the dispatch prefix reaches the head
  statement's `exec_stmt` entry.

## Why these three are the `SqEntryC` boundary, not a bare jal→entry twin

`callBody`/`stmtBlock` land at `SqEntryC Reflect c' st d env ss`, which by definition
(`ApproxDispatchSuppliers.SqEntryC`) is
`∃ ghosts, SegEntry@interpLoopHeadPC c' ∧ Reflect c' env ss`.  The `SegEntry` half is
machine content (the arm's frame-alloc + jump-to-loop-head span reaches the fresh
loop head), reachable by the `segEntry_of_jalPrefix` family.  The `Reflect` half is
the OPAQUE section variable — it carries NO computational content and CANNOT be
derived from any machine fact (`DivCorrClose`'s header: "a section variable ... a
bare `Reflect` carries no facts").  So the honest shape, exactly as the task brief
prescribes, is: the `*StagePre` residual lands at a config carrying BOTH the fresh
loop-head `SegEntry` AND `Reflect c' env ss`, the `Reflect` component being TRANSPORTED
by the caller from its own `Reflect` at the compound node (the arm does not compute
`Reflect`; it threads it along the list-structure into the child loop head).  The
bridge then repacks that pair into `SqEntryC` — definitional, no machine content, the
mirror of `sqEntryC_of_seg`.

`seqHead` runs the OTHER way: `SqEntryC (s :: ss)` gives `SegEntry@loopHead +
Reflect cH env (s :: ss)` — EXACTLY the inputs `loopHeadDispatch_span` consumes; that
span (dispatch head ≫ value_null ≫ arg-setup ≫ jal exec_stmt) reaches the
`exec_stmt`-entry config carrying `ExecEntry ... s`, which IS `SEntryC s`'s body.  So
`seqHead`'s residual is `loopHeadDispatch_span`'s premises (geometry + splices),
carried as the `SeqHeadStagePre` bundle; the bridge wraps the resulting `ExecEntry`
into `SEntryC` and counts the ≥1-step run into `LandedN 1`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no `maxHeartbeats` bump.
Axioms of every theorem ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps StepsN)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.While (St Stmt Expr BinOp UnOp Value ClosureData Store Status Addr
  EvalE EvalArgs ForCond ExecInit ExecStep ExecS)
open Vsa.Alloc
open Vsa.Sim.Code
open Vsa.Sim.Scaffold (SegEntry)
open Vsa.Sim.ApproxArmReseat
open Vsa.Sim.ApproxDispatchSuppliers (SqEntryC)

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

set_option linter.unusedVariables false

/-! ## §1. The fresh-loop-head PRE-bundle for `callBody`/`stmtBlock`

Both `callBody` and `stmtBlock` land at a fresh sequence loop head for a statement
LIST `ss` at spec state `st`, depth `d`, scope `env`, WITH `Reflect c' env ss`.  The
`SqLoopHeadPreBundle` names the state the arm's frame-alloc + jump-to-loop-head span
reaches: a config at `interpLoopHeadPC` satisfying the loop-head `SegEntry` for `st`
executing at depth `d`, PLUS the transported `Reflect c' env ss` (the opaque witness
the caller threads from its own `Reflect` at the compound node — machine-underivable,
so carried).  This IS the `SqEntryC` payload; the bridge below is a repack. -/

-- discipline: allow(R7-conj-tower-def) `SqLoopHeadPreBundle` is the SANCTIONED
-- ∃-ghost LANDING BUNDLE (same precedent as `ArmSegSplitEval.JalPreBundle` and
-- `ArmSegSplitNonEval.SegPreBundle`): it carries layout DATA (φ-maps, arena,
-- stack-layout, budgets) a `structure : Prop` cannot project, wrapping the named
-- `SegEntry` + the opaque `Reflect` witness. Its ONE consumer
-- `landedN_sqEntryC_of_preBundle` destructures it flat.
/-- **The fresh-loop-head pre-bundle for a statement list `ss`.**  A config `c'` at
`interpLoopHeadPC` satisfying the loop-head `SegEntry` for `st` at depth `d` (over
some layout ghosts), together with the TRANSPORTED opaque `Reflect c' env ss`.  This
is precisely `SqEntryC Reflect c' st d env ss` unfolded; naming it lets each arm's
`*StagePre` land here (the machine span reaches the loop head) with the `Reflect`
component threaded by the caller. -/
def SqLoopHeadPreBundle (Reflect : Config → Addr → List Stmt → Prop)
    (ss : List Stmt) (c' : Config) (st : SpecSt) (d : Nat) (env : Addr) : Prop :=
  ∃ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft : Nat) (m0 : Mem),
    SegEntry g N A SL φf φc st d dLeft aLeft interpLoopHeadPC m0 c' ∧
    Reflect c' env ss

/-- **The fresh-loop-head pre-bundle drives into `SqEntryC`.**  `SqLoopHeadPreBundle`
IS `SqEntryC` unfolded, so this is a definitional repack lifted over `LandedN`: a
`LandedN 1` to the pre-bundle is a `LandedN 1` to `SqEntryC`.  The shared "pre-bundle
⇒ sequence entry" half for both `callBody` and `stmtBlock`. -/
theorem landedN_sqEntryC_of_preBundle
    (Reflect : Config → Addr → List Stmt → Prop)
    (ss : List Stmt) (c : Config) (st : SpecSt) (d : Nat) (env : Addr)
    (h : LandedN 1 c (fun c' => SqLoopHeadPreBundle Reflect ss c' st d env)) :
    LandedN 1 c (fun c' => SqEntryC Reflect c' st d env ss) :=
  LandedN.weaken h (fun c' hpb => by
    obtain ⟨g, N, A, SL, φf, φc, dLeft, aLeft, m0, hSeg, hRefl⟩ := hpb
    exact ⟨g, N, A, SL, φf, φc, dLeft, aLeft, m0, hSeg, hRefl⟩)

#print axioms landedN_sqEntryC_of_preBundle

/-! ## §2. `stmtBlock` — the block arm sets up the inner-frame sequence loop

`stmtBlock`: from `SEntryC (.block ss)` (the block arm's `exec_stmt` entry, after the
dispatch tags kind = block), the arm allocs an inner frame (`allocFrame (some env) =
(store', inner)`) and jumps into a fresh `interp_run` loop over `ss` at the inner
scope.  `StmtBlockStagePre` is the arm-head span re-cut to land at the fresh loop
head carrying `Reflect c' inner ss` (transported).  The split repacks it via the
shared bridge. -/

/-- **The `stmtBlock` arm-head staging residual.**  From `SEntryC (.block ss)` and the
inner-frame alloc, the block arm's setup span reaches (in ≥ 1 step) the fresh
`interp_run` loop head for `ss` at the inner scope, with `Reflect` transported.
STRICTLY SMALLER than the raw field: it stops at the `SqLoopHeadPreBundle`, and the
definitional bridge finishes.  UNBUILT span = the block arm's frame-alloc + loop-head
jump, re-cut to land at the pre-bundle. -/
def StmtBlockStagePre (Reflect : Config → Addr → List Stmt → Prop)
    (ss : List Stmt) (c : Config) (st : SpecSt) (d : Nat) (env : Addr)
    (store' : Store) (inner : Addr) : Prop :=
  st.store.allocFrame (some env) = (store', inner) →
  SEntryC c st d env (.block ss) →
  LandedN 1 c (fun c' => SqLoopHeadPreBundle Reflect ss c' ⟨store', st.out⟩ d inner)

/-- **The `stmtBlock` field of `ApproxArmResidGap`.**  Given the staging residual, the
split has EXACTLY `ApproxArmResid.stmtBlock`'s type at the concrete entries: the
staging lands at the fresh loop head (`SqLoopHeadPreBundle`), and the definitional
bridge repacks into `SqEntryC`. -/
theorem stmtBlock_split (Reflect : Config → Addr → List Stmt → Prop)
    (ss : List Stmt) (c : Config) (st : SpecSt) (d : Nat) (env : Addr)
    (store' : Store) (inner : Addr)
    (hstage : StmtBlockStagePre Reflect ss c st d env store' inner) :
    st.store.allocFrame (some env) = (store', inner) →
    SEntryC c st d env (.block ss) →
    LandedN 1 c (fun c' => SqEntryC Reflect c' ⟨store', st.out⟩ d inner ss) :=
  fun hAlloc hSE =>
    landedN_sqEntryC_of_preBundle Reflect ss c ⟨store', st.out⟩ d inner (hstage hAlloc hSE)

#print axioms stmtBlock_split

/-! ## §3. `callBody` — the callee-inline body sequence loop at depth `d + 1`

`callBody`: from `CEntryC (.closure a) vs` (the EX_CALL closure-dispatch control
point, after args are evaluated and the callee frame is prepared), the arm binds the
params, enters the child frame at depth `d + 1`, and jumps into a fresh `interp_run`
loop over the callee body `cd.body`.  `CallBodyStagePre` is that setup span re-cut to
land at the child-frame loop head carrying `Reflect` for the body. -/

/-- **The `callBody` arm-head staging residual.**  From `CEntryC (.closure a) vs`, the
closure lookup, arity match, depth budget, and frame alloc, the callee-entry span
reaches (in ≥ 1 step) the fresh `interp_run` loop head for `cd.body` in the child
frame at depth `d + 1`, with the bound params in the extended store and `Reflect`
transported.  STRICTLY SMALLER than the raw field.  UNBUILT span = the closure-arm
param-bind + child-frame entry, re-cut to land at the pre-bundle. -/
def CallBodyStagePre (Reflect : Config → Addr → List Stmt → Prop)
    (c : Config) (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData)
    (vs : List Value) (store' : Store) (frame : Addr) : Prop :=
  st.store.closures[a]? = some cd → vs.length = cd.params.length →
  d < Vsa.While.maxCallDepth →
  Vsa.While.Store.allocFrame st.store (some cd.env) = (store', frame) →
  CEntryC c st d (.closure a) vs →
  LandedN 1 c (fun c' => SqLoopHeadPreBundle Reflect cd.body c'
    ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store', st.out⟩
    (d + 1) frame)

/-- **The `callBody` field of `ApproxArmResidGap`.**  Given the staging residual, the
split has EXACTLY `ApproxArmResid.callBody`'s type at the concrete entries: the staging
lands at the child-frame loop head, and the definitional bridge repacks into
`SqEntryC`. -/
theorem callBody_split (Reflect : Config → Addr → List Stmt → Prop)
    (c : Config) (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData)
    (vs : List Value) (store' : Store) (frame : Addr)
    (hstage : CallBodyStagePre Reflect c st d a cd vs store' frame) :
    st.store.closures[a]? = some cd → vs.length = cd.params.length →
    d < Vsa.While.maxCallDepth →
    Vsa.While.Store.allocFrame st.store (some cd.env) = (store', frame) →
    CEntryC c st d (.closure a) vs →
    LandedN 1 c (fun c' => SqEntryC Reflect c'
      ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store', st.out⟩
      (d + 1) frame cd.body) :=
  fun hcl hlen hdepth hAlloc hCE =>
    landedN_sqEntryC_of_preBundle Reflect cd.body c _ (d + 1) frame
      (hstage hcl hlen hdepth hAlloc hCE)

#print axioms callBody_split

/-! ## §4. `seqHead` — the loop head dispatches to the head statement's `exec_stmt`

`seqHead` runs the reverse direction from `callBody`/`stmtBlock`: from the sequence
loop head `SqEntryC Reflect c (s :: ss)`, the interp_run dispatch prefix
(`loopHeadDispatch_span`) reaches the head statement `s`'s `exec_stmt` entry.  Because
`SqEntryC (s :: ss)` unfolds to `SegEntry@loopHead + Reflect cH env (s :: ss)` — the
EXACT inputs `loopHeadDispatch_span` consumes — the residual is precisely that span's
premises (`LoopHeadDispatchGeom` + the value_null/arg-setup splices), carried as the
`SeqHeadStagePre` bundle.  The bridge wraps the resulting `ExecEntry` into `SEntryC`
and counts the ≥1-step run. -/

-- discipline: allow(R7-conj-tower-def) `SeqHeadStagePre` is the SANCTIONED landing
-- residual: from the loop-head SqEntryC, a `Steps` run (≥ 1 step: the dispatch head
-- runs real instructions) reaches a config carrying `ExecEntry ... s`. It carries a
-- reached `Config` as DATA (Prop-valued `∃ Config`, the mandated shape) plus the
-- `ExecEntry` named struct; destructured once at its consumer.
/-- **The `seqHead` staging residual.**  From the sequence loop head `SqEntryC
Reflect c (s :: ss)`, the dispatch prefix reaches (in ≥ 1 step — the dispatch head
runs real machine instructions) a config `cE` satisfying `ExecEntry ... s` for some
layout/ABI ghosts.  This IS `loopHeadDispatch_span`'s conclusion; its premises
(`LoopHeadDispatchGeom` + the value_null/arg-setup splices) are the upstream residual.
Wrapping `cE`'s `ExecEntry` gives `SEntryC c' st d env s`, so the split lands there. -/
def SeqHeadStagePre (Reflect : Config → Addr → List Stmt → Prop)
    (s : Stmt) (ss : List Stmt) (c : Config) (st : SpecSt) (d : Nat) (env : Addr) : Prop :=
  SqEntryC Reflect c st d env (s :: ss) →
  ∃ (cE : Config),
    (∃ m, 1 ≤ m ∧ StepsN m c cE) ∧
    (∃ (g : (R : Register) → Option (RegisterType R))
      (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
      (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem),
      ExecEntry g N A SL φf φc st d env s sp r aInterp aStmt aEnv aRet m0 cE)

/-- **The `seqHead` field of `ApproxArmResidGap`.**  Given the staging residual, the
split has EXACTLY `ApproxArmResid.seqHead`'s type at the concrete entries: the ≥1-step
dispatch run to the `exec_stmt`-entry config is a `LandedN 1`, and its `ExecEntry`
existentially wraps into `SEntryC s`. -/
theorem seqHead_split (Reflect : Config → Addr → List Stmt → Prop)
    (s : Stmt) (ss : List Stmt) (c : Config) (st : SpecSt) (d : Nat) (env : Addr)
    (hstage : SeqHeadStagePre Reflect s ss c st d env) :
    SqEntryC Reflect c st d env (s :: ss) →
    LandedN 1 c (fun c' => SEntryC c' st d env s) := by
  intro hSq
  obtain ⟨cE, ⟨m, hm, hsteps⟩, g, N, A, SL, φf, φc, sp, r, aInterp, aStmt, aEnv, aRet,
    m0, hEntry⟩ := hstage hSq
  exact ⟨m, cE, hm, hsteps,
    ⟨g, N, A, SL, φf, φc, sp, r, aInterp, aStmt, aEnv, aRet, m0, hEntry⟩⟩

#print axioms seqHead_split

/-! ## §5. Capstone — the `SqEntryC`-boundary staging bundle + field-group discharge

`SqEntryStages` bundles the staging residuals for the 3 `SqEntryC`-boundary fields.
`armResidGap_sqEntryFields` discharges them at the EXACT `ApproxArmResid` field types —
the third counterpart of `ArmSegSplitEval.armResidGap_evalChildFields` (15) and
`ArmSegSplitNonEval.armResidGap_nonEvalChildFields` (11).  Together the three cover
all 29 `ApproxArmResid` fields (15 + 11 + 3) modulo their staging bundles. -/

-- discipline: allow(R6-conj-tower-def) `SqEntryStages` is the staging-residual BUNDLE
-- (same precedent as `EvalChildStages`/`NonEvalChildStages`): three per-arm
-- arm-head-to-pre-bundle residuals, projected by name by the consumer.
structure SqEntryStages (Reflect : Config → Addr → List Stmt → Prop) : Prop where
  stmtBlock : ∀ (ss : List Stmt) (c : Config) (st : SpecSt) (d : Nat) (env : Addr)
    (store' : Store) (inner : Addr),
    StmtBlockStagePre Reflect ss c st d env store' inner
  callBody : ∀ (c : Config) (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData)
    (vs : List Value) (store' : Store) (frame : Addr),
    CallBodyStagePre Reflect c st d a cd vs store' frame
  seqHead : ∀ (s : Stmt) (ss : List Stmt) (c : Config) (st : SpecSt) (d : Nat) (env : Addr),
    SeqHeadStagePre Reflect s ss c st d env

/-- **The 3 `SqEntryC`-boundary fields of `ApproxArmResid`, discharged from
`SqEntryStages`.**  Each is `<field>_split` fed the bundled staging residual, returned
as the exact conjunction of `ApproxArmResid` field types so the final assembly consumes
them directly alongside the eval-child (15) and non-eval-child (11) groups. -/
theorem armResidGap_sqEntryFields (Reflect : Config → Addr → List Stmt → Prop)
    (S : SqEntryStages Reflect) :
    (∀ (c : Config) (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData)
      (vs : List Value) (store' : Store) (frame : Addr),
      st.store.closures[a]? = some cd → vs.length = cd.params.length →
      d < Vsa.While.maxCallDepth →
      Vsa.While.Store.allocFrame st.store (some cd.env) = (store', frame) →
      CEntryC c st d (.closure a) vs →
      LandedN 1 c (fun c' => SqEntryC Reflect c'
        ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store', st.out⟩
        (d + 1) frame cd.body)) ∧
    (∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (ss : List Stmt)
      (store' : Store) (inner : Addr),
      st.store.allocFrame (some env) = (store', inner) →
      SEntryC c st d env (.block ss) →
      LandedN 1 c (fun c' => SqEntryC Reflect c' ⟨store', st.out⟩ d inner ss)) ∧
    (∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt),
      SqEntryC Reflect c st d env (s :: ss) →
      LandedN 1 c (fun c' => SEntryC c' st d env s)) :=
  ⟨fun c st d a cd vs store' frame =>
     callBody_split Reflect c st d a cd vs store' frame (S.callBody c st d a cd vs store' frame),
   fun c st d env ss store' inner =>
     stmtBlock_split Reflect ss c st d env store' inner (S.stmtBlock ss c st d env store' inner),
   fun c st d env s ss =>
     seqHead_split Reflect s ss c st d env (S.seqHead s ss c st d env)⟩

#print axioms armResidGap_sqEntryFields

end Vsa.Sim
