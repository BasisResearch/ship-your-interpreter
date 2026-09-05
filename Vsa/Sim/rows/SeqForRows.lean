import Vsa.Sim.ExecSeqLoop
import Vsa.Sim.ExecSeqIndexed
import Vsa.Sim.ExecFor
import Vsa.Sim.TermCaseBundle

/-!
# Layer 4 — the `ExecSeq` and `ForLoop` motive rows (`hSeqNil`/`hSeqCons*`/`hFl*`)

The seven mutual-recursion premises of `term_sim_of_cases`/`execSeq_sim_of_cases`
that (before this file) had NO landed `_row` and were carried as whole-premise
`TermResiduals` fields: the three `ExecSeq` constructors (`ExecSeq.nil`,
`ExecSeq.consNormal`, `ExecSeq.consAbrupt`) and the four `ForLoop` constructors
(`condFalse`/`bodyBreak`/`bodyRet`/`loop`).

## The motive shapes (`TermSimAssembly.lean`)

* `mExecSeq st d env ss st' status _ =`
  `∀ g N A SL φf φc dLeft aLeft p q m0, Triple (SegEntry … p) (SegExit … st' q)`
  — the statement-list loop; **entry PC `p` and exit PC `q` are INDEPENDENT**
  (the `block`/`interp_run` consumers need `p = execSeqLoopPC ≠ q = execSeqContPC`).
* `mForLoop st d env cnd step b st' status _ =`
  `∀ g N A SL φf φc dLeft aLeft p m0, Triple (SegEntry … p) (SegExit … st' p)`
  — the for-loop body; **identity-PC** (amended, ledger
  `scaffold-motive-independent-pq`): the loop-structural entry/exit coincide.

## The seam this file crosses (and why the residual is NAMED, not proved)

The landed loop ENGINES speak a DIFFERENT machine contract than these motives:

* `execSeqLoop` (`ExecSeqLoop.lean`) composes `ExecSeqEntry → ExecSeqExit`
  Triples (with `sp`/`r`/`minstret`, NO depth/arena budget), driven by the
  per-iteration `ExecSeqStep` oracle;
* `execForLoopBody` (`ExecFor.lean`) composes `ExecEntry → ExecExit` Triples at
  the child scope `outer`, driven by the `ExecForStep` oracle.

Neither `ExecSeqEntry/ExecSeqExit` nor `ExecEntry/ExecExit` is DEFEQ to the
`SegEntry/SegExit` skeleton the motive demands (the field sets differ:
`SegEntry` carries `depth_budget`/`arena_budget` and no `sp`/`r`; `ExecSeqEntry`
carries `sp`/`r`/`minstret` and no budgets).  So the motive Triple is NOT a free
`rfl`/`.1`-map of the engine's output — a real `SegEntry → ExecSeqEntry` /
`SegExit ← ExecSeqExit` adapter (an ABI + budget reconciliation span) is missing.

Following the `AssignArmSpec`/`ArgsBodyOracle` "row now, arm oracle later"
precedent, each row here is proved from ONE named residual bundle — the motive
Triple itself, ∀-closed as a `*Resid` `Prop` — plus the recursor's sub-IH
consumption pattern made explicit.  The row's VALUE is: (1) it slot-verifies the
`_row` conclusion against the VERBATIM `TermCases` field type (the mechanical fill
point the capstone's `termCases_of_residuals` will use), and (2) it threads the
recursor sub-IHs into named positions so the residual carries EXACTLY the machine
span (empty-seq hop / seq back-edge / for-loop body), not the sub-derivation
correspondences (those are supplied by the recursor).

The genuine open content behind every `*Resid` is the loop body oracle
(`ExecSeqStep`/`ExecForStep`), blocked on `exprRepr_agreeP` per
`experiments/loop-fanout.md` — a Layer-4 semantic gap shared with the already
landed `block`/`while` engines, NOT a combinator gap.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Halts Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code
open Vsa.Sim.TermSimAssembly

namespace Vsa.Sim.Rows

open Vsa.Sim
open Vsa.Sim.Scaffold

local notation "SpecSt" => Vsa.While.St

/-! ## §1. `hSeqNil` — `ExecSeq.nil` -/

/-- The faithful indexed half of `ExecSeq.nil` is unconditional. -/
theorem seqNilIndexed (st : SpecSt) (d : Nat) (env : Addr) :
    SeqIndexedIH st d env [] st Status.normal := by
  intro copy g N A SL φf φc sp aRet m0 hsupport
  exact execSeqNilI copy g N A SL φf φc st d env sp aRet m0 hsupport

#print axioms seqNilIndexed

/-- The indexed sequence motive is closed by one finite, copy-specific step
seam.  This isolates the remaining machine work for both cons constructors. -/
theorem seqIndexed_of_steps
    (st st' : SpecSt) (d : Nat) (env : Addr) (ss : List Stmt)
    (status : Status) (hSeq : ExecSeq st d env ss st' status)
    (hHead : ∀ (stM stM' : SpecSt) (s : Stmt) (headStatus : Status)
      (hS : ExecS stM d env s stM' headStatus),
      ExecIH stM d env s stM' headStatus)
    (hstep : ∀ (copy : ExecSeqCopy)
      (g : (R : Register) → Option (RegisterType R))
      (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
      (sp aRet : BitVec 64) (stM : SpecSt) (s : Stmt) (tail : List Stmt)
      (stM' stFin : SpecSt) (headStatus : Status) (m0 : Mem),
      ExecSeqStepI copy g N A SL φf φc stM d env s tail sp aRet m0
        stM' stFin headStatus (ExecIH stM d env s stM' headStatus)) :
    SeqIndexedIH st d env ss st' status := by
  intro copy g N A SL φf φc sp aRet m0 hsupport
  exact execSeqLoopI copy g N A SL d env sp aRet
    (fun stM s stM' headStatus => ExecIH stM d env s stM' headStatus)
    hHead
    (fun φf₀ φc₀ stM s tail stM' stFin headStatus m00 =>
      hstep copy g N A SL φf₀ φc₀ sp aRet stM s tail stM' stFin headStatus m00)
    ss φf φc st st' status m0 hsupport hSeq

#print axioms seqIndexed_of_steps

/-- The remaining finite machine obligation for sequence constructors.  It has
exactly three physical instantiations, selected by `copy`; the statement IH is
an explicit input rather than being silently omitted from the loop encoding. -/
def SeqStepCopyGeomFamily (copy : ExecSeqCopy) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp aRet : BitVec 64) (st : SpecSt) (d : Nat) (env : Addr)
    (s : Stmt) (ss : List Stmt) (st' stFin : SpecSt)
    (status : Status) (m0 : Mem),
    ExecS st d env s st' status →
    ExecIH st d env s st' status →
    copy.Supports status →
    ExecSeqStepGeomI copy g N A SL φf φc st d env s ss sp aRet m0
      st' stFin status

def SeqStepCopyFamily (copy : ExecSeqCopy) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp aRet : BitVec 64) (st : SpecSt) (d : Nat) (env : Addr)
    (s : Stmt) (ss : List Stmt) (st' stFin : SpecSt)
    (status : Status) (m0 : Mem),
    ExecSeqStepI copy g N A SL φf φc st d env s ss sp aRet m0
      st' stFin status (ExecIH st d env s st' status)

def SeqStepFamily : Prop := ∀ copy, SeqStepCopyFamily copy

/-- Explicit ledger for the three physical copies. Each field contains only
the copy's dispatch and resume machine seams; the recursive statement call is
composed by `execSeqStepI_of_geom`. -/
structure SeqStepResiduals : Prop where
  interpRun : SeqStepCopyGeomFamily .interpRun
  closureBody : SeqStepCopyGeomFamily .closureBody
  blockBody : SeqStepCopyGeomFamily .blockBody

theorem seqStepFamily_of_residuals (R : SeqStepResiduals) : SeqStepFamily := by
  intro copy
  intro g N A SL φf φc sp aRet st d env s ss st' stFin status m0
  intro hS hHead hsupport
  cases copy with
  | interpRun =>
      exact (execSeqInterpRunStepI g N A SL φf φc st d env s ss sp aRet m0
        st' stFin status
        (R.interpRun g N A SL φf φc sp aRet st d env s ss st' stFin status m0
          hS hHead hsupport)) hS hHead hsupport
  | closureBody =>
      exact (execSeqClosureBodyStepI g N A SL φf φc st d env s ss sp aRet m0
        st' stFin status
        (R.closureBody g N A SL φf φc sp aRet st d env s ss st' stFin status m0
          hS hHead hsupport)) hS hHead hsupport
  | blockBody =>
      exact (execSeqBlockBodyStepI g N A SL φf φc st d env s ss sp aRet m0
        st' stFin status
        (R.blockBody g N A SL φf φc sp aRet st d env s ss st' stFin status m0
          hS hHead hsupport)) hS hHead hsupport

#print axioms seqStepFamily_of_residuals

/-- The empty suffix is already parked at each physical copy's exact normal-exit
boundary.  Therefore `hSeqNil` has no residual. -/
theorem hSeqNil_row :
    ∀ (st : SpecSt) (d : Nat) (env : Addr),
      mExecSeq st d env [] st Status.normal (ExecSeq.nil st d env) := by
  intro st d env
  exact seqNilIndexed st d env

#print axioms hSeqNil_row

/-! ## §2. `hSeqConsAbrupt` — `ExecSeq.consAbrupt`

The head statement `s` runs to an ABRUPT status (`≠ .normal`) and short-circuits
the sequence: the tail `ss` is NOT run (the machine `bnez a0` at `0x800041c8`
jumps straight to the continuation `q`).  So the motive `mExecSeq (s::ss) st'
status` is produced from the head `mExecS s st' status` (= `ExecIH s`, the
recursor's sub-derivation) plus the seq loop's ONE-iteration abrupt-exit span.

The residual `SeqConsAbruptResid` carries that span, taking the head `ExecIH` and
the abrupt-status witness as explicit inputs (so it need not re-derive the head). -/

/-- The `hSeqConsAbrupt` residual: the abrupt one-iteration exit span, given the
head statement's `ExecIH` and its abrupt status. -/
def SeqConsAbruptResid
    (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt)
    (st' : SpecSt) (status : Status) : Prop :=
  ExecIH st d env s st' status → status ≠ Status.normal →
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft p q : Nat) (m0 : Mem),
    SeqSpanGround p q m0 →
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft p m0)
      (SegExit g N A SL φf φc st.store.frames.size st.store.closures.size st' q m0)

/-- The abrupt constructor is closed by its head IH and the copy-indexed
one-iteration machine seam. -/
theorem hSeqConsAbrupt_row
    (hSteps : SeqStepFamily) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) (st' : SpecSt)
      (status : Status) (a : ExecS st d env s st' status) (a_1 : status ≠ Status.normal),
      mExecS st d env s st' status a →
      mExecSeq st d env (s :: ss) st' status (ExecSeq.consAbrupt st d env s ss st' status a a_1) := by
  intro st d env s ss st' status a a_1 hHeadIH
  intro copy g N A SL φf φc sp aRet m0 hsupport
  exact execSeqConsAbruptI copy g N A SL φf φc st st' d env s ss status
    sp aRet m0 (ExecIH st d env s st' status) a hHeadIH a_1 hsupport
    (hSteps copy g N A SL φf φc sp aRet st d env s ss st' st' status m0)

#print axioms hSeqConsAbrupt_row

/-! ## §3. `hSeqConsNormal` — `ExecSeq.consNormal`

The head `s` runs to `.normal`; the tail `ss` then runs from the intermediate
state `st'` producing the final `st''`/`status` (the seq back-edge, machine
`blt a5,a4,0x800041a4` at `0x800041dc`).  The motive `mExecSeq (s::ss) st''
status` is produced from BOTH sub-IHs — the head `mExecS s st' .normal`
(= `ExecIH s`) AND the tail `mExecSeq ss st'' status` (the tail motive Triple) —
plus the loop back-edge glue that stitches one iteration to the recursive tail.

The residual `SeqConsNormalResid` carries that stitch, taking both sub-IHs as
explicit inputs.  (The per-iteration body oracle `ExecSeqStep` stays inside the
residual — the `ArgsBodyOracle`/`experiments/loop-fanout.md` precedent: the seq
shape's oracle is itself still open, blocked on `exprRepr_agreeP`.) -/

/-- The `hSeqConsNormal` residual: the seq back-edge span, given the head
statement's `ExecIH` (`.normal`) and the tail sequence's motive Triple. -/
def SeqConsNormalResid
    (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt)
    (st' st'' : SpecSt) (status : Status) : Prop :=
  ExecIH st d env s st' Status.normal →
  (∀ (g : (R : Register) → Option (RegisterType R))
      (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
      (dLeft aLeft p q : Nat) (m0 : Mem),
      SeqSpanGround p q m0 →
      Triple
        (SegEntry g N A SL φf φc st' d dLeft aLeft p m0)
        (SegExit g N A SL φf φc st'.store.frames.size st'.store.closures.size st'' q m0)) →
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft p q : Nat) (m0 : Mem),
    SeqSpanGround p q m0 →
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft p m0)
      (SegExit g N A SL φf φc st.store.frames.size st.store.closures.size st'' q m0)

/-- The normal constructor is closed by the head IH, indexed tail IH, and one
copy-indexed iteration seam. -/
theorem hSeqConsNormal_row
    (hSteps : SeqStepFamily) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) (st' st'' : SpecSt)
      (status : Status) (a : ExecS st d env s st' Status.normal) (a_1 : ExecSeq st' d env ss st'' status),
      mExecS st d env s st' Status.normal a →
      mExecSeq st' d env ss st'' status a_1 →
      mExecSeq st d env (s :: ss) st'' status (ExecSeq.consNormal st d env s ss st' st'' status a a_1) := by
  intro st d env s ss st' st'' status a a_1 hHeadIH hTailIH
  intro copy g N A SL φf φc sp aRet m0 hsupport
  exact execSeqConsNormalI copy g N A SL φf φc st st' st'' d env s ss status
    sp aRet m0 (ExecIH st d env s st' .normal) a hHeadIH
    (execSeq_store_mono a_1)
    (hSteps copy g N A SL φf φc sp aRet st d env s ss st' st'' .normal m0)
    (fun φf' φc' mNow => hTailIH copy g N A SL φf' φc' sp aRet mNow hsupport)

#print axioms hSeqConsNormal_row

/-! ## §4. The context-indexed `ForLoop` family

`mForLoop` is `ForLoopCtxIH`. Each constructor retains its semantic context and
its recursive sub-motives. The former `True` motive was unsound as an induction
boundary because `exec_forStart_row` needs the loop result and store-growth facts.
The four rows below therefore expose exact typed residuals. -/

/-- Route `hFlCondFalse` into the context-indexed loop motive. -/
def FlCondFalseResid
    (st st' : SpecSt) (d : Nat) (env : Addr) (c : Expr)
    (step : Option Expr) (b : Stmt) (v : Value)
    (hC : EvalE st d env c st' v) (hFalse : v.truthy = false) : Prop :=
  mEvalE st d env c st' v hC →
  mForLoop st d env (some c) step b st' Status.normal
    (ForLoop.condFalse st d env c step b st' v hC hFalse)

theorem hFlCondFalse_row
    (hR : ∀ st st' d env c step b v hC hFalse,
      FlCondFalseResid st st' d env c step b v hC hFalse) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (step : Option Expr) (b : Stmt)
      (st' : SpecSt) (v : Value) (a : EvalE st d env c st' v) (a_1 : v.truthy = false),
      mEvalE st d env c st' v a →
      mForLoop st d env (some c) step b st' Status.normal (ForLoop.condFalse st d env c step b st' v a a_1) := by
  intro st d env c step b st' v a a_1 hCondIH
  exact hR st st' d env c step b v a a_1 hCondIH

#print axioms hFlCondFalse_row

/-- Route `hFlBodyBreak` into the context-indexed loop motive. -/
def FlBodyBreakResid
    (st st' st'' : SpecSt) (d : Nat) (env : Addr)
    (cnd step : Option Expr) (b : Stmt)
    (hCond : ForCond st d env cnd st')
    (hBody : ExecS st' d env b st'' Status.brk) : Prop :=
  mForCond st d env cnd st' hCond →
  mExecS st' d env b st'' Status.brk hBody →
  mForLoop st d env cnd step b st'' Status.normal
    (ForLoop.bodyBreak st d env cnd step b st' st'' hCond hBody)

theorem hFlBodyBreak_row
    (hR : ∀ st st' st'' d env cnd step b hCond hBody,
      FlBodyBreakResid st st' st'' d env cnd step b hCond hBody) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd step : Option Expr) (b : Stmt)
      (st' st'' : SpecSt) (a : ForCond st d env cnd st') (a_1 : ExecS st' d env b st'' Status.brk),
      mForCond st d env cnd st' a → mExecS st' d env b st'' Status.brk a_1 →
      mForLoop st d env cnd step b st'' Status.normal (ForLoop.bodyBreak st d env cnd step b st' st'' a a_1) := by
  intro st d env cnd step b st' st'' a a_1 hCondIH hBodyIH
  exact hR st st' st'' d env cnd step b a a_1 hCondIH hBodyIH

#print axioms hFlBodyBreak_row

/-- Route `hFlBodyRet` into the context-indexed loop motive. -/
def FlBodyRetResid
    (st st' st'' : SpecSt) (d : Nat) (env : Addr)
    (cnd step : Option Expr) (b : Stmt) (rv : Value)
    (hCond : ForCond st d env cnd st')
    (hBody : ExecS st' d env b st'' (.ret rv)) : Prop :=
  mForCond st d env cnd st' hCond →
  mExecS st' d env b st'' (.ret rv) hBody →
  mForLoop st d env cnd step b st'' (.ret rv)
    (ForLoop.bodyRet st d env cnd step b st' st'' rv hCond hBody)

theorem hFlBodyRet_row
    (hR : ∀ st st' st'' d env cnd step b rv hCond hBody,
      FlBodyRetResid st st' st'' d env cnd step b rv hCond hBody) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd step : Option Expr) (b : Stmt)
      (st' st'' : SpecSt) (rv : Value) (a : ForCond st d env cnd st')
      (a_1 : ExecS st' d env b st'' (Status.ret rv)),
      mForCond st d env cnd st' a → mExecS st' d env b st'' (Status.ret rv) a_1 →
      mForLoop st d env cnd step b st'' (Status.ret rv) (ForLoop.bodyRet st d env cnd step b st' st'' rv a a_1) := by
  intro st d env cnd step b st' st'' rv a a_1 hCondIH hBodyIH
  exact hR st st' st'' d env cnd step b rv a a_1 hCondIH hBodyIH

#print axioms hFlBodyRet_row

/-- Route `hFlLoop` into the context-indexed loop motive. -/
def FlLoopResid
    (st st' st'' st''' st'''' : SpecSt) (d : Nat) (env : Addr)
    (cnd step : Option Expr) (b : Stmt) (status status' : Status)
    (hCond : ForCond st d env cnd st') (hBody : ExecS st' d env b st'' status)
    (hContinue : status = .normal ∨ status = .cont)
    (hStep : ExecStep st'' d env step st''')
    (hRest : ForLoop st''' d env cnd step b st'''' status') : Prop :=
  mForCond st d env cnd st' hCond →
  mExecS st' d env b st'' status hBody →
  mExecStep st'' d env step st''' hStep →
  mForLoop st''' d env cnd step b st'''' status' hRest →
  mForLoop st d env cnd step b st'''' status'
    (ForLoop.loop st d env cnd step b st' st'' st''' st'''' status status'
      hCond hBody hContinue hStep hRest)

theorem hFlLoop_row
    (hR : ∀ st st' st'' st''' st'''' d env cnd step b status status'
      hCond hBody hContinue hStep hRest,
      FlLoopResid st st' st'' st''' st'''' d env cnd step b status status'
        hCond hBody hContinue hStep hRest) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd step : Option Expr) (b : Stmt)
      (st' st'' st''' st'''' : SpecSt) (status status' : Status) (a : ForCond st d env cnd st')
      (a_1 : ExecS st' d env b st'' status) (a_2 : status = Status.normal ∨ status = Status.cont)
      (a_3 : ExecStep st'' d env step st''') (a_4 : ForLoop st''' d env cnd step b st'''' status'),
      mForCond st d env cnd st' a → mExecS st' d env b st'' status a_1 →
      mExecStep st'' d env step st''' a_3 → mForLoop st''' d env cnd step b st'''' status' a_4 →
      mForLoop st d env cnd step b st'''' status' (ForLoop.loop st d env cnd step b st' st'' st''' st'''' status status' a a_1 a_2 a_3 a_4) := by
  intro st d env cnd step b st' st'' st''' st'''' status status' a a_1 a_2 a_3 a_4
    hCondIH hBodyIH hStepIH hRestIH
  exact hR st st' st'' st''' st'''' d env cnd step b status status'
    a a_1 a_2 a_3 a_4 hCondIH hBodyIH hStepIH hRestIH

#print axioms hFlLoop_row

/-! ## §5. Slot verification against the `TermCaseBundle.TermCases` field types

Each `example` demands the EXACT bundle-field type (copied VERBATIM from
`TermCaseBundle.lean`) and supplies the corresponding `_row` fed a matching
residual `hyp`.  Type-checking these is the machine confirmation that every row
drops into `termCases_of_residuals` with no adapter. -/

/-- Slot check: `hSeqNil` / `hSeqConsAbrupt` / `hSeqConsNormal` fill their bundle
fields. -/
example
    (hStepResiduals : SeqStepResiduals)
    :
    (∀ (st : SpecSt) (d : Nat) (env : Addr),
        mExecSeq st d env [] st Status.normal (ExecSeq.nil st d env)) ∧
    (∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) (st' : SpecSt)
        (status : Status) (a : ExecS st d env s st' status) (a_1 : status ≠ Status.normal),
        mExecS st d env s st' status a →
        mExecSeq st d env (s :: ss) st' status (ExecSeq.consAbrupt st d env s ss st' status a a_1)) ∧
    (∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) (st' st'' : SpecSt)
        (status : Status) (a : ExecS st d env s st' Status.normal) (a_1 : ExecSeq st' d env ss st'' status),
        mExecS st d env s st' Status.normal a →
        mExecSeq st' d env ss st'' status a_1 →
        mExecSeq st d env (s :: ss) st'' status (ExecSeq.consNormal st d env s ss st' st'' status a a_1)) :=
  ⟨hSeqNil_row,
    hSeqConsAbrupt_row (seqStepFamily_of_residuals hStepResiduals),
    hSeqConsNormal_row (seqStepFamily_of_residuals hStepResiduals)⟩

/-- Slot check: the four context-indexed `hFl*` fields. -/
example
    (hFalse : ∀ st st' d env c step b v hC hFalse,
      FlCondFalseResid st st' d env c step b v hC hFalse)
    (hBreak : ∀ st st' st'' d env cnd step b hCond hBody,
      FlBodyBreakResid st st' st'' d env cnd step b hCond hBody)
    (hRet : ∀ st st' st'' d env cnd step b rv hCond hBody,
      FlBodyRetResid st st' st'' d env cnd step b rv hCond hBody)
    (hLoop : ∀ st st' st'' st''' st'''' d env cnd step b status status'
      hCond hBody hContinue hStep hRest,
      FlLoopResid st st' st'' st''' st'''' d env cnd step b status status'
        hCond hBody hContinue hStep hRest) :
    (∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (step : Option Expr) (b : Stmt)
        (st' : SpecSt) (v : Value) (a : EvalE st d env c st' v) (a_1 : v.truthy = false),
        mEvalE st d env c st' v a →
        mForLoop st d env (some c) step b st' Status.normal (ForLoop.condFalse st d env c step b st' v a a_1)) ∧
    (∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd step : Option Expr) (b : Stmt)
        (st' st'' : SpecSt) (a : ForCond st d env cnd st') (a_1 : ExecS st' d env b st'' Status.brk),
        mForCond st d env cnd st' a → mExecS st' d env b st'' Status.brk a_1 →
        mForLoop st d env cnd step b st'' Status.normal (ForLoop.bodyBreak st d env cnd step b st' st'' a a_1)) ∧
    (∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd step : Option Expr) (b : Stmt)
        (st' st'' : SpecSt) (rv : Value) (a : ForCond st d env cnd st')
        (a_1 : ExecS st' d env b st'' (Status.ret rv)),
        mForCond st d env cnd st' a → mExecS st' d env b st'' (Status.ret rv) a_1 →
        mForLoop st d env cnd step b st'' (Status.ret rv) (ForLoop.bodyRet st d env cnd step b st' st'' rv a a_1)) ∧
    (∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd step : Option Expr) (b : Stmt)
        (st' st'' st''' st'''' : SpecSt) (status status' : Status) (a : ForCond st d env cnd st')
        (a_1 : ExecS st' d env b st'' status) (a_2 : status = Status.normal ∨ status = Status.cont)
        (a_3 : ExecStep st'' d env step st''') (a_4 : ForLoop st''' d env cnd step b st'''' status'),
        mForCond st d env cnd st' a → mExecS st' d env b st'' status a_1 →
        mExecStep st'' d env step st''' a_3 → mForLoop st''' d env cnd step b st'''' status' a_4 →
        mForLoop st d env cnd step b st'''' status' (ForLoop.loop st d env cnd step b st' st'' st''' st'''' status status' a a_1 a_2 a_3 a_4)) :=
  ⟨hFlCondFalse_row hFalse, hFlBodyBreak_row hBreak,
    hFlBodyRet_row hRet, hFlLoop_row hLoop⟩

end Vsa.Sim.Rows
