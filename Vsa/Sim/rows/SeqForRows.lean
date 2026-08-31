import Vsa.Sim.ExecSeqLoop
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

/-! ## §1. `hSeqNil` — `ExecSeq.nil`

`mExecSeq st d env [] st .normal` is the empty-sequence loop-head fallthrough:
`SegEntry … p → SegExit … st q` for the SAME state `st` but INDEPENDENT PCs
`p`/`q` (machine `li a0,0 ; j 0x8000409c` from the loop head to the continuation).
Because `q` is universally quantified, this is a genuine `p → q` span, NOT an
identity segment — so it is a named residual, `SeqNilResid` (the empty-seq hop). -/

/-- The `hSeqNil` residual: EXACTLY the `mExecSeq … []` motive Triple, ∀-closed. -/
def SeqNilResid (st : SpecSt) (d : Nat) (env : Addr) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft p q : Nat) (m0 : Mem),
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft p m0)
      (SegExit g N A SL φf φc st.store.frames.size st.store.closures.size st q m0)

/-- Route `hSeqNil` → `SeqNilResid`.  Slot-verifies against the `TermCases.hSeqNil`
field type; the empty-seq hop is the named residual. -/
theorem hSeqNil_row (hR : ∀ st d env, SeqNilResid st d env) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr),
      mExecSeq st d env [] st Status.normal (ExecSeq.nil st d env) := by
  intro st d env
  exact hR st d env

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
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft p m0)
      (SegExit g N A SL φf φc st.store.frames.size st.store.closures.size st' q m0)

/-- Route `hSeqConsAbrupt` → `SeqConsAbruptResid`.  The recursor's head IH
(`mExecS s st' status = ExecIH s`) and the abrupt witness `a_1` feed the residual;
slot-verified against the `TermCases.hSeqConsAbrupt` field type. -/
theorem hSeqConsAbrupt_row
    (hR : ∀ st d env s ss st' status, SeqConsAbruptResid st d env s ss st' status) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) (st' : SpecSt)
      (status : Status) (a : ExecS st d env s st' status) (a_1 : status ≠ Status.normal),
      mExecS st d env s st' status a →
      mExecSeq st d env (s :: ss) st' status (ExecSeq.consAbrupt st d env s ss st' status a a_1) := by
  intro st d env s ss st' status a a_1 hHeadIH
  exact hR st d env s ss st' status hHeadIH a_1

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
      Triple
        (SegEntry g N A SL φf φc st' d dLeft aLeft p m0)
        (SegExit g N A SL φf φc st'.store.frames.size st'.store.closures.size st'' q m0)) →
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft p q : Nat) (m0 : Mem),
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft p m0)
      (SegExit g N A SL φf φc st.store.frames.size st.store.closures.size st'' q m0)

/-- Route `hSeqConsNormal` → `SeqConsNormalResid`.  Both recursor sub-IHs (head
`mExecS = ExecIH s`; tail `mExecSeq` motive Triple) feed the residual;
slot-verified against the `TermCases.hSeqConsNormal` field type. -/
theorem hSeqConsNormal_row
    (hR : ∀ st d env s ss st' st'' status,
      SeqConsNormalResid st d env s ss st' st'' status) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) (st' st'' : SpecSt)
      (status : Status) (a : ExecS st d env s st' Status.normal) (a_1 : ExecSeq st' d env ss st'' status),
      mExecS st d env s st' Status.normal a →
      mExecSeq st' d env ss st'' status a_1 →
      mExecSeq st d env (s :: ss) st'' status (ExecSeq.consNormal st d env s ss st' st'' status a a_1) := by
  intro st d env s ss st' st'' status a a_1 hHeadIH hTailIH
  exact hR st d env s ss st' st'' status hHeadIH hTailIH

#print axioms hSeqConsNormal_row

/-! ## §4. The `ForLoop` family — ONE `ForResid`, four rows

`mForLoop st d env cnd step b st' status` is the IDENTITY-PC span
`SegEntry … st p → SegExit … st' p` (amended motive).  The four constructors
(`condFalse`/`bodyBreak`/`bodyRet`/`loop`) all conclude this SAME motive shape,
differing only in which sub-derivations the recursor threads and the produced
`(st', status)`.  Mirroring the `while` family (`rows/ExecDispatchRows.lean`:
ONE `WhileGeom` + `execWhileIH_of_resid` + three rows), we use ONE `ForResid`
keyed on the loop endpoints `(st, st', status)` and the loop shape `(cnd, step,
b)`, and four rows that consume each constructor's sub-IHs and route to it.

The genuine machine content behind `ForResid` is the `ExecForStep` body oracle
composed by `execForLoopBody` (`ExecFor.lean`) — but that engine speaks
`ExecEntry → ExecExit` at the child scope, not the identity-PC `SegEntry →
SegExit` motive, and no landed adapter bridges them; so `ForResid` carries the
motive Triple directly (the `experiments/loop-fanout.md` oracle-still-open
state).  The rows thread the recursor sub-IHs into named positions. -/

/-- The shared `ForLoop`-family residual: the identity-PC motive Triple, ∀-closed,
keyed on the loop endpoints and shape. -/
def ForResid
    (st : SpecSt) (d : Nat) (env : Addr) (cnd step : Option Expr) (b : Stmt)
    (st' : SpecSt) (status : Status) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft p : Nat) (m0 : Mem),
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft p m0)
      (SegExit g N A SL φf φc st.store.frames.size st.store.closures.size st' p m0)

/-- `ForResid st d env cnd step b st' status` IS `mForLoop … st' status` after
δ-unfolding — the shared dispatcher used by every for-loop row. -/
theorem forLoop_of_resid
    {st : SpecSt} {d : Nat} {env : Addr} {cnd step : Option Expr} {b : Stmt}
    {st' : SpecSt} {status : Status}
    (hFor : ForLoop st d env cnd step b st' status)
    (hR : ForResid st d env cnd step b st' status) :
    mForLoop st d env cnd step b st' status hFor :=
  hR

/-- Route `hFlCondFalse` → `ForResid`.  The recursor gives `mEvalE c` (the cond
sub-IH) and the falsy witness `a_1`; both are absorbed by the residual (the
condition-eval span is inside the for-loop machine iteration).  Slot-verified
against `TermCases.hFlCondFalse`. -/
theorem hFlCondFalse_row
    (hR : ∀ st d env c step b st' (v : Value), v.truthy = false →
      ForResid st d env (some c) step b st' Status.normal) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (step : Option Expr) (b : Stmt)
      (st' : SpecSt) (v : Value) (a : EvalE st d env c st' v) (a_1 : v.truthy = false),
      mEvalE st d env c st' v a →
      mForLoop st d env (some c) step b st' Status.normal (ForLoop.condFalse st d env c step b st' v a a_1) := by
  intro st d env c step b st' v a a_1 _hCondIH
  exact forLoop_of_resid (ForLoop.condFalse st d env c step b st' v a a_1)
    (hR st d env c step b st' v a_1)

#print axioms hFlCondFalse_row

/-- Route `hFlBodyBreak` → `ForResid`.  Sub-IHs: `mForCond cnd` + `mExecS b`
(`.brk`).  Slot-verified against `TermCases.hFlBodyBreak`. -/
theorem hFlBodyBreak_row
    (hR : ∀ st d env cnd step b st'', ForResid st d env cnd step b st'' Status.normal) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd step : Option Expr) (b : Stmt)
      (st' st'' : SpecSt) (a : ForCond st d env cnd st') (a_1 : ExecS st' d env b st'' Status.brk),
      mForCond st d env cnd st' a → mExecS st' d env b st'' Status.brk a_1 →
      mForLoop st d env cnd step b st'' Status.normal (ForLoop.bodyBreak st d env cnd step b st' st'' a a_1) := by
  intro st d env cnd step b st' st'' a a_1 _hCondIH _hBodyIH
  exact forLoop_of_resid (ForLoop.bodyBreak st d env cnd step b st' st'' a a_1)
    (hR st d env cnd step b st'')

#print axioms hFlBodyBreak_row

/-- Route `hFlBodyRet` → `ForResid`.  Sub-IHs: `mForCond cnd` + `mExecS b`
(`.ret rv`).  Slot-verified against `TermCases.hFlBodyRet`. -/
theorem hFlBodyRet_row
    (hR : ∀ st d env cnd step b st'' rv, ForResid st d env cnd step b st'' (Status.ret rv)) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd step : Option Expr) (b : Stmt)
      (st' st'' : SpecSt) (rv : Value) (a : ForCond st d env cnd st')
      (a_1 : ExecS st' d env b st'' (Status.ret rv)),
      mForCond st d env cnd st' a → mExecS st' d env b st'' (Status.ret rv) a_1 →
      mForLoop st d env cnd step b st'' (Status.ret rv) (ForLoop.bodyRet st d env cnd step b st' st'' rv a a_1) := by
  intro st d env cnd step b st' st'' rv a a_1 _hCondIH _hBodyIH
  exact forLoop_of_resid (ForLoop.bodyRet st d env cnd step b st' st'' rv a a_1)
    (hR st d env cnd step b st'' rv)

#print axioms hFlBodyRet_row

/-- Route `hFlLoop` → `ForResid`.  Sub-IHs: `mForCond cnd` + `mExecS b` +
`mExecStep step` + the RECURSIVE `mForLoop` (the back-edge tail).  All four are
absorbed by the residual (the for-loop back-edge span composes one iteration with
the recursive tail inside the machine engine).  Slot-verified against
`TermCases.hFlLoop`. -/
theorem hFlLoop_row
    (hR : ∀ st d env cnd step b st'''' status', ForResid st d env cnd step b st'''' status') :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd step : Option Expr) (b : Stmt)
      (st' st'' st''' st'''' : SpecSt) (status status' : Status) (a : ForCond st d env cnd st')
      (a_1 : ExecS st' d env b st'' status) (a_2 : status = Status.normal ∨ status = Status.cont)
      (a_3 : ExecStep st'' d env step st''') (a_4 : ForLoop st''' d env cnd step b st'''' status'),
      mForCond st d env cnd st' a → mExecS st' d env b st'' status a_1 →
      mExecStep st'' d env step st''' a_3 → mForLoop st''' d env cnd step b st'''' status' a_4 →
      mForLoop st d env cnd step b st'''' status' (ForLoop.loop st d env cnd step b st' st'' st''' st'''' status status' a a_1 a_2 a_3 a_4) := by
  intro st d env cnd step b st' st'' st''' st'''' status status' a a_1 a_2 a_3 a_4
    _hCondIH _hBodyIH _hStepIH _hRestIH
  exact forLoop_of_resid
    (ForLoop.loop st d env cnd step b st' st'' st''' st'''' status status' a a_1 a_2 a_3 a_4)
    (hR st d env cnd step b st'''' status')

#print axioms hFlLoop_row

/-! ## §5. Slot verification against the `TermCaseBundle.TermCases` field types

Each `example` demands the EXACT bundle-field type (copied VERBATIM from
`TermCaseBundle.lean`) and supplies the corresponding `_row` fed a matching
residual `hyp`.  Type-checking these is the machine confirmation that every row
drops into `termCases_of_residuals` with no adapter. -/

/-- Slot check: `hSeqNil` / `hSeqConsAbrupt` / `hSeqConsNormal` fill their bundle
fields. -/
example
    (hNil : ∀ st d env, SeqNilResid st d env)
    (hAbr : ∀ st d env s ss st' status, SeqConsAbruptResid st d env s ss st' status)
    (hNorm : ∀ st d env s ss st' st'' status, SeqConsNormalResid st d env s ss st' st'' status) :
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
  ⟨hSeqNil_row hNil, hSeqConsAbrupt_row hAbr, hSeqConsNormal_row hNorm⟩

/-- Slot check: the four `hFl*` for-loop fields. -/
example
    (hCF : ∀ st d env c step b st' (v : Value), v.truthy = false →
      ForResid st d env (some c) step b st' Status.normal)
    (hBB : ∀ st d env cnd step b st'', ForResid st d env cnd step b st'' Status.normal)
    (hBR : ∀ st d env cnd step b st'' rv, ForResid st d env cnd step b st'' (Status.ret rv))
    (hL : ∀ st d env cnd step b st'''' status', ForResid st d env cnd step b st'''' status') :
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
  ⟨hFlCondFalse_row hCF, hFlBodyBreak_row hBB, hFlBodyRet_row hBR, hFlLoop_row hL⟩

end Vsa.Sim.Rows
