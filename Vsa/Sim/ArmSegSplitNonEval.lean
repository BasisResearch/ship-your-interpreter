import Vsa.Sim.ArmSegSplitExec
import Vsa.Sim.ArmSegSplitSeg
import Vsa.Sim.ApproxArmReseat

/-!
# `ArmSegSplitNonEval` — the non-eval-child arm-class splits (Task #76, Half A.3)

`ArmSegSplitEval` closed the 15 EVAL-child fields of `ApproxArmResidGap` (post =
`EEntryC <child expr>`) through `landedN_eentryC_of_preBundle` (built on
`evalEntry_of_jalPrefix`).  This file closes the remaining fields whose post is a
NON-eval interior entry, using the two twins built in Half A.1/A.2:

* **`execEntry_of_jalPrefix`** (the exec-stmt twin) drives the `SEntryC`-landing
  fields — the statement arms whose recursion goes into a CHILD STATEMENT:
  `stmtIfThen`, `stmtIfElse`, `stmtWhileBody`, `stmtForInit`, `flBody`.
* **`segEntry_of_jalPrefix`** (the light SegEntry twin) drives the `AEntryC` /
  `CEntryC` / `FEntryC`-landing fields — the interior control points with no rich
  struct: `callArgs`, `argsTail` (arg loop), `callC` (callee dispatch), `stmtForLoop`,
  `flLoop` (for re-entry).

Exactly the `ArmSegSplitEval` pattern: a per-class `*StagePre` residual (arm-head +
dispatch re-cut to land at the twin's PRE-bundle, NOT consume the IH), a shared
"pre-bundle ⇒ child entry" bridge (`landedN_sEntryC_of_preBundle` /
`landedN_segEntryC_of_preBundle`), and a generic split combinator
(`execChildSplit_of_stage` / `segChildSplit_of_stage`) that `LandedN.bind`s the two.

The lowered-frame geometry premises (child-frame `stackOK`, child `StmtRepr`/
`StoreRepr` survival, depth/arena budgets) stay NAMED premises of the `*PreBundle`,
carried through — not derived.  Each split is STRICTLY SMALLER than its raw field
(stops at the pre-bundle; the verified twin finishes).

NB fields still requiring their OWN (non-twin) marshalling — `callBody`/`stmtBlock`/
`seqHead` land at `SqEntryC` (a `SegEntry + Reflect`, needing the extra `Reflect`
witness, so NOT a bare jal→SegEntry) — stay named in `ApproxArmResidGap`; they are
the `IterSeamAssembly`/`SqEntryC` boundary, not this file's twins.

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
open Vsa.While (St Stmt Expr BinOp UnOp Value ClosureData Store Status Addr
  EvalE EvalArgs ForCond ExecInit ExecStep ExecS)
open Vsa.Alloc
open Vsa.Sim.Code
open Vsa.Sim.Scaffold (SegEntry)
open Vsa.Sim.ApproxArmReseat

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

set_option linter.unusedVariables false

/-! ## §1. The exec-stmt PRE-bundle and its `SEntryC` bridge -/

-- discipline: allow(R7-conj-tower-def) `ExecStmtPreBundle` is the SANCTIONED
-- ∃-ghost LANDING BUNDLE (same precedent as `ArmSegSplitEval.JalPreBundle`): it
-- carries layout DATA (φ-maps, arena, per-arm callPC/retPC/jalImm/hdrm) a
-- `structure : Prop` cannot project, so it MUST be a `∃` over that data. It IS the
-- `execEntry_of_jalPrefix` named pre-bundle; every consumer goes through the ONE
-- named destructurer `landedN_sEntryC_of_preBundle`.
/-- **The `execEntry_of_jalPrefix` PRE-bundle, as a config predicate over the child
statement `s`.**  State at the recursive `jal exec_stmt` PC with the child's args
staged (`a0`/`a1`/`a2`/`a3`, `sp` lowered by the arm's `hdrm`), all child-frame
geometry.  `d`/`env` carried so the child `SEntryC` inherits the SAME depth/env. -/
def ExecStmtPreBundle (s : Stmt) (c' : Config) (st : SpecSt) (d : Nat)
    (env : Addr) : Prop :=
  ∃ (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (callPC retPC : BitVec 64) (jalImm : BitVec 21) (hdrm : BitVec 64)
    (sp aInterp aStmt aEnv aRet : BitVec 64)
    (out0 : Array String) (mcall : Mem),
    ((callPC + sign_extend (m := 64) jalImm) = BitVec.ofNat 64 execStmtEntry) ∧
    ((BitVec.addInt callPC 4) = retPC) ∧ retPC.toNat % 4 = 0 ∧
    (∀ (σ : MState) (i u : Nat) (vmi : BitVec 64),
      GoodState σ → σ.regs.get? Register.PC = some callPC →
      σ.regs.get? Register.minstret = some vmi → Exec_stmtLoaded σ.mem → i < 2 →
      ∃ (σ' : MState) (i' : Nat),
        Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
        ReadsLikePost σ' (sigmaPost_jal σ callPC vmi jalImm Register.x1 (BitVec.addInt callPC 4))) ∧
    GoodState c'.σ ∧ c'.tick < 2 ∧
    c'.σ.regs.get? Register.PC = some callPC ∧
    c'.σ.regs.get? Register.x10 = some aInterp ∧
    c'.σ.regs.get? Register.x11 = some aStmt ∧
    c'.σ.regs.get? Register.x12 = some aEnv ∧
    c'.σ.regs.get? Register.x13 = some aRet ∧
    c'.σ.regs.get? Register.x2 = some (sp - hdrm) ∧
    (∃ w, c'.σ.regs.get? Register.minstret = some w) ∧
    ((∃ w, c'.σ.regs.get? Register.x8 = some w) ∧
     (∃ w, c'.σ.regs.get? Register.x9 = some w) ∧
     (∃ w, c'.σ.regs.get? Register.x18 = some w) ∧
     (∃ w, c'.σ.regs.get? Register.x19 = some w)) ∧
    c'.σ.sailOutput = out0 ∧
    String.join out0.toList = st.out ∧
    c'.σ.mem = mcall ∧
    Exec_stmtLoaded mcall ∧
    StmtRepr mcall aStmt.toNat s ∧
    StoreRepr mcall N A φf φc st.store ∧
    (∀ m' : Mem,
      (∀ k, ¬ (SL.lo ≤ k ∧ k < (sp - hdrm).toNat) → mcall[k]? = m'[k]?) →
      StoreRepr m' N A φf φc st.store) ∧
    aStmt.toNat % 8 = 0 ∧
    0x80000000 ≤ aStmt.toNat ∧ aStmt.toNat + 16 ≤ 0x100000000 ∧
    tohostAddr + 16 ≤ aStmt.toNat ∧
    (aStmt.toNat + 16 ≤ SL.lo ∨ (sp - hdrm).toNat ≤ aStmt.toNat) ∧
    StackOK SL (sp - hdrm) (176 + 1088) ∧
    0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000 ∧ tohostAddr + 16 ≤ SL.lo ∧
    ((sp - hdrm).toNat ≤ execStmtEntry ∨ execStmtEnd ≤ SL.lo)

/-- **The exec-stmt pre-bundle drives into `SEntryC`.**  A config at
`ExecStmtPreBundle s` lands (`≥ 1` step, the `jal`) at `SEntryC s` — pure
application of `execEntry_of_jalPrefix`, then wrapping the layout ghosts
existentially into the `SEntryC` bundle. -/
theorem landedN_sEntryC_of_preBundle
    (s : Stmt) (c' : Config) (st : SpecSt) (d : Nat) (env : Addr)
    (h : ExecStmtPreBundle s c' st d env) :
    LandedN 1 c' (fun c'' => SEntryC c'' st d env s) := by
  obtain ⟨N, A, SL, φf, φc, callPC, retPC, jalImm, hdrm, sp, aInterp, aStmt, aEnv,
    aRet, out0, mcall, hjaltgt, hlink, hretAl, hjalSite, hrest⟩ := h
  have hEE := execEntry_of_jalPrefix N A SL φf φc st d env s
    callPC retPC jalImm hdrm sp aInterp aStmt aEnv aRet out0 mcall c'
    hjaltgt hlink hretAl hjalSite hrest
  exact LandedN.weaken hEE (fun c'' hEntry =>
    ⟨fun R => c''.σ.regs.get? R, N, A, SL, φf, φc,
      sp - hdrm, retPC, aInterp, aStmt, aEnv, aRet, mcall, hEntry⟩)

#print axioms landedN_sEntryC_of_preBundle

/-! ## §2. The SegEntry PRE-bundle and its `AEntryC`/`CEntryC`/`FEntryC` bridges -/

-- discipline: allow(R7-conj-tower-def) `SegPreBundle` is the SANCTIONED ∃-ghost
-- LANDING BUNDLE for the light SegEntry twin; carries layout DATA a
-- `structure : Prop` cannot project. It IS the `segEntry_of_jalPrefix` pre-bundle;
-- consumers go through the named destructurers below.
/-- **The `segEntry_of_jalPrefix` PRE-bundle, as a config predicate over the
interior control PC.**  State at the recursive `jal <interior>` PC targeting
`entryPC`, with the light `SegEntry` facts (store/out/budgets) available.  `dLeft`/
`aLeft` are the depth/arena budgets the interior control point respects. -/
def SegPreBundle (entryPC : Nat) (c' : Config) (st : SpecSt) (d dLeft aLeft : Nat) : Prop :=
  ∃ (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (callPC : BitVec 64) (jalImm : BitVec 21) (mcall : Mem),
    ((callPC + sign_extend (m := 64) jalImm) = BitVec.ofNat 64 entryPC) ∧
    (∀ (σ : MState) (i u : Nat) (vmi : BitVec 64),
      GoodState σ → σ.regs.get? Register.PC = some callPC →
      σ.regs.get? Register.minstret = some vmi → Exec_stmtLoaded σ.mem → i < 2 →
      ∃ (σ' : MState) (i' : Nat),
        Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
        ReadsLikePost σ' (sigmaPost_jal σ callPC vmi jalImm Register.x1 (BitVec.addInt callPC 4))) ∧
    GoodState c'.σ ∧ c'.tick < 2 ∧
    c'.σ.regs.get? Register.PC = some callPC ∧
    (∃ w, c'.σ.regs.get? Register.minstret = some w) ∧
    c'.σ.mem = mcall ∧
    Exec_stmtLoaded mcall ∧
    StoreRepr mcall N A φf φc st.store ∧
    Machine.output c'.σ = st.out ∧
    d + dLeft = Vsa.While.maxCallDepth ∧
    A.lo + aLeft ≤ A.hi

/-- **The SegEntry pre-bundle drives into a `SegEntry`.**  Reusable core: a config
at `SegPreBundle entryPC` lands (`≥ 1` step) at `SegEntry … entryPC …` for a fresh
`SL` ghost.  The `AEntryC`/`CEntryC`/`FEntryC` bundles are exactly this `SegEntry`
wrapped over their layout ghosts, so each of the three bridges below is this fact
followed by an existential re-pack. -/
theorem landedN_segEntry_of_preBundle
    (entryPC : Nat) (c' : Config) (st : SpecSt) (d dLeft aLeft : Nat)
    (SL : StackLayout)
    (h : ∃ (N : NativeAddrs) (A : Arena) (φf φc : Addr → Nat)
      (callPC : BitVec 64) (jalImm : BitVec 21) (mcall : Mem),
      ((callPC + sign_extend (m := 64) jalImm) = BitVec.ofNat 64 entryPC) ∧
      (∀ (σ : MState) (i u : Nat) (vmi : BitVec 64),
        GoodState σ → σ.regs.get? Register.PC = some callPC →
        σ.regs.get? Register.minstret = some vmi → Exec_stmtLoaded σ.mem → i < 2 →
        ∃ (σ' : MState) (i' : Nat),
          Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
          ReadsLikePost σ' (sigmaPost_jal σ callPC vmi jalImm Register.x1 (BitVec.addInt callPC 4))) ∧
      GoodState c'.σ ∧ c'.tick < 2 ∧
      c'.σ.regs.get? Register.PC = some callPC ∧
      (∃ w, c'.σ.regs.get? Register.minstret = some w) ∧
      c'.σ.mem = mcall ∧
      Exec_stmtLoaded mcall ∧
      StoreRepr mcall N A φf φc st.store ∧
      Machine.output c'.σ = st.out ∧
      d + dLeft = Vsa.While.maxCallDepth ∧
      A.lo + aLeft ≤ A.hi) :
    LandedN 1 c' (fun c'' =>
      ∃ (g : (R : Register) → Option (RegisterType R))
        (N : NativeAddrs) (A : Arena) (φf φc : Addr → Nat) (m0 : Mem),
        SegEntry g N A SL φf φc st d dLeft aLeft entryPC m0 c'') := by
  obtain ⟨N, A, φf, φc, callPC, jalImm, mcall, hjaltgt, hjalSite, hrest⟩ := h
  have hSE := segEntry_of_jalPrefix N A SL φf φc st d dLeft aLeft entryPC
    callPC jalImm mcall c' hjaltgt hjalSite hrest
  exact LandedN.weaken hSE (fun c'' hEntry =>
    ⟨fun R => c''.σ.regs.get? R, N, A, φf, φc, mcall, hEntry⟩)

#print axioms landedN_segEntry_of_preBundle

/-- **The SegEntry pre-bundle drives into `AEntryC`.**  The `SegPreBundle` at the
arg-loop control PC `argLoopPC` lands at `AEntryC es` for the remaining arg list
`es` (the abstract node fact is carried by the ghost interior PC).  Threads
`landedN_segEntry_of_preBundle` and re-packs the `SL`/`dLeft`/`aLeft`/PC ghosts into
the `AEntryC` bundle shape. -/
theorem landedN_aEntryC_of_preBundle
    (es : List Expr) (argLoopPC : Nat) (c' : Config) (st : SpecSt)
    (d dLeft aLeft : Nat) (env : Addr) (SL : StackLayout)
    (h : SegPreBundle argLoopPC c' st d dLeft aLeft) :
    LandedN 1 c' (fun c'' => AEntryC c'' st d env es) := by
  obtain ⟨N, A, SLb, φf, φc, callPC, jalImm, mcall, hrest⟩ := h
  have hSE := landedN_segEntry_of_preBundle argLoopPC c' st d dLeft aLeft SL
    ⟨N, A, φf, φc, callPC, jalImm, mcall, hrest⟩
  exact LandedN.weaken hSE (fun c'' hEntry => by
    obtain ⟨g, N', A', φf', φc', m0, hSeg⟩ := hEntry
    exact ⟨g, N', A', SL, φf', φc', dLeft, aLeft, argLoopPC, m0, hSeg⟩)

#print axioms landedN_aEntryC_of_preBundle

/-- **The SegEntry pre-bundle drives into `CEntryC`.**  The `SegPreBundle` at the
callee-body head PC `calleeBodyPC` lands at `CEntryC fv vs`. -/
theorem landedN_cEntryC_of_preBundle
    (fv : Value) (vs : List Value) (calleeBodyPC : Nat) (c' : Config) (st : SpecSt)
    (d dLeft aLeft : Nat) (SL : StackLayout)
    (h : SegPreBundle calleeBodyPC c' st d dLeft aLeft) :
    LandedN 1 c' (fun c'' => CEntryC c'' st d fv vs) := by
  obtain ⟨N, A, SLb, φf, φc, callPC, jalImm, mcall, hrest⟩ := h
  have hSE := landedN_segEntry_of_preBundle calleeBodyPC c' st d dLeft aLeft SL
    ⟨N, A, φf, φc, callPC, jalImm, mcall, hrest⟩
  exact LandedN.weaken hSE (fun c'' hEntry => by
    obtain ⟨g, N', A', φf', φc', m0, hSeg⟩ := hEntry
    exact ⟨g, N', A', SL, φf', φc', dLeft, aLeft, calleeBodyPC, m0, hSeg⟩)

#print axioms landedN_cEntryC_of_preBundle

/-- **The SegEntry pre-bundle drives into `FEntryC`.**  The `SegPreBundle` at the
for-loop re-entry PC `forCondPC` lands at `FEntryC cnd step b`. -/
theorem landedN_fEntryC_of_preBundle
    (cnd step : Option Expr) (b : Stmt) (forCondPC : Nat) (c' : Config) (st : SpecSt)
    (d dLeft aLeft : Nat) (env : Addr) (SL : StackLayout)
    (h : SegPreBundle forCondPC c' st d dLeft aLeft) :
    LandedN 1 c' (fun c'' => FEntryC c'' st d env cnd step b) := by
  obtain ⟨N, A, SLb, φf, φc, callPC, jalImm, mcall, hrest⟩ := h
  have hSE := landedN_segEntry_of_preBundle forCondPC c' st d dLeft aLeft SL
    ⟨N, A, φf, φc, callPC, jalImm, mcall, hrest⟩
  exact LandedN.weaken hSE (fun c'' hEntry => by
    obtain ⟨g, N', A', φf', φc', m0, hSeg⟩ := hEntry
    exact ⟨g, N', A', SL, φf', φc', dLeft, aLeft, forCondPC, m0, hSeg⟩)

#print axioms landedN_fEntryC_of_preBundle

/-! ## §3. Generic exec/seg-child split combinators (mirror `evalChildSplit_of_stage`) -/

/-- **Generic exec-child split.**  A staging landing to `ExecStmtPreBundle child`
composes with the exec twin bridge to a `LandedN 1` to `SEntryC child`.  Shared body
of every `SEntryC`-landing field (stmtIfThen/stmtIfElse/stmtWhileBody/stmtForInit/
flBody). -/
theorem execChildSplit_of_stage
    (child : Stmt) (c : Config) (st : SpecSt) (d : Nat) (env : Addr)
    (hstaged : LandedN 1 c (fun c' => ExecStmtPreBundle child c' st d env)) :
    LandedN 1 c (fun c' => SEntryC c' st d env child) :=
  LandedN.weakenCount (by omega : 1 ≤ 1 + 1)
    (LandedN.bind hstaged
      (fun c' hpb => landedN_sEntryC_of_preBundle child c' st d env hpb))

#print axioms execChildSplit_of_stage

/-- **Generic args-child split.**  Staging to `SegPreBundle argLoopPC` composes with
the AEntryC bridge to a `LandedN 1` to `AEntryC es`. -/
theorem argsChildSplit_of_stage
    (es : List Expr) (argLoopPC : Nat) (c : Config) (st : SpecSt) (d dLeft aLeft : Nat)
    (env : Addr) (SL : StackLayout)
    (hstaged : LandedN 1 c (fun c' => SegPreBundle argLoopPC c' st d dLeft aLeft)) :
    LandedN 1 c (fun c' => AEntryC c' st d env es) :=
  LandedN.weakenCount (by omega : 1 ≤ 1 + 1)
    (LandedN.bind hstaged
      (fun c' hpb => landedN_aEntryC_of_preBundle es argLoopPC c' st d dLeft aLeft env SL hpb))

#print axioms argsChildSplit_of_stage

/-- **Generic callee-child split.**  Staging to `SegPreBundle calleeBodyPC` composes
with the CEntryC bridge to a `LandedN 1` to `CEntryC fv vs`. -/
theorem calleeChildSplit_of_stage
    (fv : Value) (vs : List Value) (calleeBodyPC : Nat) (c : Config) (st : SpecSt)
    (d dLeft aLeft : Nat) (SL : StackLayout)
    (hstaged : LandedN 1 c (fun c' => SegPreBundle calleeBodyPC c' st d dLeft aLeft)) :
    LandedN 1 c (fun c' => CEntryC c' st d fv vs) :=
  LandedN.weakenCount (by omega : 1 ≤ 1 + 1)
    (LandedN.bind hstaged
      (fun c' hpb => landedN_cEntryC_of_preBundle fv vs calleeBodyPC c' st d dLeft aLeft SL hpb))

#print axioms calleeChildSplit_of_stage

/-- **Generic for-child split.**  Staging to `SegPreBundle forCondPC` composes with
the FEntryC bridge to a `LandedN 1` to `FEntryC cnd step b`. -/
theorem forChildSplit_of_stage
    (cnd step : Option Expr) (b : Stmt) (forCondPC : Nat) (c : Config) (st : SpecSt)
    (d dLeft aLeft : Nat) (env : Addr) (SL : StackLayout)
    (hstaged : LandedN 1 c (fun c' => SegPreBundle forCondPC c' st d dLeft aLeft)) :
    LandedN 1 c (fun c' => FEntryC c' st d env cnd step b) :=
  LandedN.weakenCount (by omega : 1 ≤ 1 + 1)
    (LandedN.bind hstaged
      (fun c' hpb => landedN_fEntryC_of_preBundle cnd step b forCondPC c' st d dLeft aLeft env SL hpb))

#print axioms forChildSplit_of_stage

/-! ## §4. The per-field non-eval-child splits (exact `ApproxArmResid` field types)

Each split takes its per-class arm-head-to-pre-bundle staging residual (`hstage`)
and returns EXACTLY the `ApproxArmResid` field type at the concrete entries.  The
staging residual carries the spec-side hypotheses (`EvalE`/`ForCond`/`ExecS`/… that
pin the store `st'` at which the child runs) so the returned split matches the field
signature verbatim; the verified twin finishes the machine content. -/

-- SEntryC-landing statement arms (via the exec twin) ------------------------------

/-- **`stmtIfThen` field.**  `... → SEntryC (.ifStmt cnd t e) → LandedN 1 (SEntryC t)`. -/
theorem stmtIfThen_split (cnd : Expr) (t : Stmt) (e : Option Stmt) (c : Config)
    (st st' : SpecSt) (d : Nat) (env : Addr) (v : Value)
    (hstage : EvalE st d env cnd st' v → v.truthy = true →
      SEntryC c st d env (.ifStmt cnd t e) →
      LandedN 1 c (fun c' => ExecStmtPreBundle t c' st' d env)) :
    EvalE st d env cnd st' v → v.truthy = true → SEntryC c st d env (.ifStmt cnd t e) →
    LandedN 1 c (fun c' => SEntryC c' st' d env t) :=
  fun hE ht hSE => execChildSplit_of_stage t c st' d env (hstage hE ht hSE)

#print axioms stmtIfThen_split

/-- **`stmtIfElse` field.**  `... → SEntryC (.ifStmt cnd t (some e)) → LandedN 1 (SEntryC e)`. -/
theorem stmtIfElse_split (cnd : Expr) (t e : Stmt) (c : Config)
    (st st' : SpecSt) (d : Nat) (env : Addr) (v : Value)
    (hstage : EvalE st d env cnd st' v → v.truthy = false →
      SEntryC c st d env (.ifStmt cnd t (some e)) →
      LandedN 1 c (fun c' => ExecStmtPreBundle e c' st' d env)) :
    EvalE st d env cnd st' v → v.truthy = false → SEntryC c st d env (.ifStmt cnd t (some e)) →
    LandedN 1 c (fun c' => SEntryC c' st' d env e) :=
  fun hE hf hSE => execChildSplit_of_stage e c st' d env (hstage hE hf hSE)

#print axioms stmtIfElse_split

/-- **`stmtWhileBody` field.**  `... → SEntryC (.whileStmt cnd b) → LandedN 1 (SEntryC b)`. -/
theorem stmtWhileBody_split (cnd : Expr) (b : Stmt) (c : Config)
    (st st' : SpecSt) (d : Nat) (env : Addr) (v : Value)
    (hstage : EvalE st d env cnd st' v → v.truthy = true →
      SEntryC c st d env (.whileStmt cnd b) →
      LandedN 1 c (fun c' => ExecStmtPreBundle b c' st' d env)) :
    EvalE st d env cnd st' v → v.truthy = true → SEntryC c st d env (.whileStmt cnd b) →
    LandedN 1 c (fun c' => SEntryC c' st' d env b) :=
  fun hE ht hSE => execChildSplit_of_stage b c st' d env (hstage hE ht hSE)

#print axioms stmtWhileBody_split

/-- **`stmtWhileLoop` field.**  `... → SEntryC (.whileStmt cnd b) → LandedN 1 (SEntryC
(.whileStmt cnd b))` — the loop re-enters the SAME while node at `st''`. -/
theorem stmtWhileLoop_split (cnd : Expr) (b : Stmt) (c : Config)
    (st st' st'' : SpecSt) (d : Nat) (env : Addr) (v : Value) (status : Status)
    (hstage : EvalE st d env cnd st' v → v.truthy = true →
      ExecS st' d env b st'' status → (status = .normal ∨ status = .cont) →
      SEntryC c st d env (.whileStmt cnd b) →
      LandedN 1 c (fun c' => ExecStmtPreBundle (.whileStmt cnd b) c' st'' d env)) :
    EvalE st d env cnd st' v → v.truthy = true →
    ExecS st' d env b st'' status → (status = .normal ∨ status = .cont) →
    SEntryC c st d env (.whileStmt cnd b) →
    LandedN 1 c (fun c' => SEntryC c' st'' d env (.whileStmt cnd b)) :=
  fun hE ht hEx hst hSE =>
    execChildSplit_of_stage (.whileStmt cnd b) c st'' d env (hstage hE ht hEx hst hSE)

#print axioms stmtWhileLoop_split

/-- **`stmtForInit` field.**  `allocFrame → SEntryC (.forStmt (some init) …) → LandedN 1
(SEntryC init at ⟨store',out⟩)`. -/
theorem stmtForInit_split (init : Stmt) (cnd step : Option Expr) (b : Stmt) (c : Config)
    (st : SpecSt) (d : Nat) (env : Addr) (store' : Store) (outer : Addr)
    (hstage : st.store.allocFrame (some env) = (store', outer) →
      SEntryC c st d env (.forStmt (some init) cnd step b) →
      LandedN 1 c (fun c' => ExecStmtPreBundle init c' ⟨store', st.out⟩ d outer)) :
    st.store.allocFrame (some env) = (store', outer) →
    SEntryC c st d env (.forStmt (some init) cnd step b) →
    LandedN 1 c (fun c' => SEntryC c' ⟨store', st.out⟩ d outer init) :=
  fun hAlloc hSE => execChildSplit_of_stage init c ⟨store', st.out⟩ d outer (hstage hAlloc hSE)

#print axioms stmtForInit_split

/-- **`flBody` field.**  `ForCond → FEntryC cnd step b → LandedN 1 (SEntryC b)`. -/
theorem flBody_split (cnd : Option Expr) (step : Option Expr) (b : Stmt) (c : Config)
    (st st' : SpecSt) (d : Nat) (env : Addr)
    (hstage : ForCond st d env cnd st' → FEntryC c st d env cnd step b →
      LandedN 1 c (fun c' => ExecStmtPreBundle b c' st' d env)) :
    ForCond st d env cnd st' → FEntryC c st d env cnd step b →
    LandedN 1 c (fun c' => SEntryC c' st' d env b) :=
  fun hFC hFE => execChildSplit_of_stage b c st' d env (hstage hFC hFE)

#print axioms flBody_split

-- AEntryC / CEntryC / FEntryC-landing arms (via the light SegEntry twin) -----------

/-- **`callArgs` field.**  `EvalE f → EEntryC (.call f args) → LandedN 1 (AEntryC args)`.
The staging residual supplies the arg-loop control PC and its budgets. -/
theorem callArgs_split (f : Expr) (args : List Expr) (c : Config) (st st' : SpecSt)
    (d : Nat) (env : Addr) (fv : Value) (argLoopPC dLeft aLeft : Nat) (SL : StackLayout)
    (hstage : EvalE st d env f st' fv → EEntryC c st d env (.call f args) →
      LandedN 1 c (fun c' => SegPreBundle argLoopPC c' st' d dLeft aLeft)) :
    EvalE st d env f st' fv → EEntryC c st d env (.call f args) →
    LandedN 1 c (fun c' => AEntryC c' st' d env args) :=
  fun hE hEE => argsChildSplit_of_stage args argLoopPC c st' d dLeft aLeft env SL (hstage hE hEE)

#print axioms callArgs_split

/-- **`argsTail` field.**  `EvalE e → AEntryC (e::es) → LandedN 1 (AEntryC es)`. -/
theorem argsTail_split (e : Expr) (es : List Expr) (c : Config) (st st' : SpecSt)
    (d : Nat) (env : Addr) (v : Value) (argLoopPC dLeft aLeft : Nat) (SL : StackLayout)
    (hstage : EvalE st d env e st' v → AEntryC c st d env (e :: es) →
      LandedN 1 c (fun c' => SegPreBundle argLoopPC c' st' d dLeft aLeft)) :
    EvalE st d env e st' v → AEntryC c st d env (e :: es) →
    LandedN 1 c (fun c' => AEntryC c' st' d env es) :=
  fun hE hAE => argsChildSplit_of_stage es argLoopPC c st' d dLeft aLeft env SL (hstage hE hAE)

#print axioms argsTail_split

/-- **`callC` field.**  `EvalE f → EvalArgs → EEntryC (.call f args) → LandedN 1
(CEntryC fv vs)`. -/
theorem callC_split (f : Expr) (args : List Expr) (c : Config) (st st' st'' : SpecSt)
    (d : Nat) (env : Addr) (fv : Value) (vs : List Value)
    (calleeBodyPC dLeft aLeft : Nat) (SL : StackLayout)
    (hstage : EvalE st d env f st' fv → EvalArgs st' d env args st'' vs →
      EEntryC c st d env (.call f args) →
      LandedN 1 c (fun c' => SegPreBundle calleeBodyPC c' st'' d dLeft aLeft)) :
    EvalE st d env f st' fv → EvalArgs st' d env args st'' vs →
    EEntryC c st d env (.call f args) →
    LandedN 1 c (fun c' => CEntryC c' st'' d fv vs) :=
  fun hE hA hEE => calleeChildSplit_of_stage fv vs calleeBodyPC c st'' d dLeft aLeft SL (hstage hE hA hEE)

#print axioms callC_split

/-- **`stmtForLoop` field.**  `allocFrame → ExecInit → SEntryC (.forStmt …) → LandedN 1
(FEntryC cnd step b)`. -/
theorem stmtForLoop_split (init : Option Stmt) (cnd step : Option Expr) (b : Stmt)
    (c : Config) (st st' : SpecSt) (d : Nat) (env : Addr) (store' : Store) (outer : Addr)
    (forCondPC dLeft aLeft : Nat) (SL : StackLayout)
    (hstage : st.store.allocFrame (some env) = (store', outer) →
      ExecInit ⟨store', st.out⟩ d outer init st' →
      SEntryC c st d env (.forStmt init cnd step b) →
      LandedN 1 c (fun c' => SegPreBundle forCondPC c' st' d dLeft aLeft)) :
    st.store.allocFrame (some env) = (store', outer) →
    ExecInit ⟨store', st.out⟩ d outer init st' →
    SEntryC c st d env (.forStmt init cnd step b) →
    LandedN 1 c (fun c' => FEntryC c' st' d outer cnd step b) :=
  fun hAlloc hInit hSE =>
    forChildSplit_of_stage cnd step b forCondPC c st' d dLeft aLeft outer SL (hstage hAlloc hInit hSE)

#print axioms stmtForLoop_split

/-- **`flLoop` field.**  `ForCond → ExecS → status → ExecStep → FEntryC → LandedN 1
(FEntryC cnd step b)` — the for-loop re-enters at `st'''` with the same cnd/step/b. -/
theorem flLoop_split (cnd : Option Expr) (step : Option Expr) (b : Stmt)
    (c : Config) (st st' st'' st''' : SpecSt) (d : Nat) (env : Addr) (status : Status)
    (forCondPC dLeft aLeft : Nat) (SL : StackLayout)
    (hstage : ForCond st d env cnd st' → ExecS st' d env b st'' status →
      (status = .normal ∨ status = .cont) → ExecStep st'' d env step st''' →
      FEntryC c st d env cnd step b →
      LandedN 1 c (fun c' => SegPreBundle forCondPC c' st''' d dLeft aLeft)) :
    ForCond st d env cnd st' → ExecS st' d env b st'' status →
    (status = .normal ∨ status = .cont) → ExecStep st'' d env step st''' →
    FEntryC c st d env cnd step b →
    LandedN 1 c (fun c' => FEntryC c' st''' d env cnd step b) :=
  fun hFC hEx hst hStep hFE =>
    forChildSplit_of_stage cnd step b forCondPC c st''' d dLeft aLeft env SL
      (hstage hFC hEx hst hStep hFE)

#print axioms flLoop_split

/-! ## §5. Capstone — the non-eval-child staging bundle + field-group discharge

`NonEvalChildStages` bundles the staging residuals for the 11 NON-eval-child fields
of `ApproxArmResidGap` (post = `SEntryC`/`AEntryC`/`CEntryC`/`FEntryC`).  Each residual
is STRICTLY SMALLER than its field: it stops at `ExecStmtPreBundle`/`SegPreBundle`,
and the verified twin bridge finishes.  The five `SEntryC`-landing arms carry the
exec-stmt pre-bundle; the six `AEntryC`/`CEntryC`/`FEntryC`-landing arms carry the
light SegEntry pre-bundle (with their ghost interior PC + budgets `dLeft`/`aLeft`).

`armResidGap_nonEvalChildFields` discharges the 11 fields at the EXACT `ApproxArmResid`
field types from the bundle — the counterpart of `ArmSegSplitEval`'s
`armResidGap_evalChildFields` (which does the 15 eval-child fields).  Together they
cover 26 of the 29 `ApproxArmResid` fields; the remaining 3 (`callBody`/`stmtBlock`/
`seqHead`) land at `SqEntryC` (a `SegEntry + Reflect`), needing the extra `Reflect`
witness — the `IterSeamAssembly`/`SqEntryC` boundary, not a bare jal twin. -/

-- discipline: allow(R6-conj-tower-def) `NonEvalChildStages` is the staging-residual
-- BUNDLE (same precedent as `ArmSegSplitEval.EvalChildStages`): each field is a
-- per-arm arm-head-to-pre-bundle residual, carrying the ghost interior PC + budgets
-- as ∀-bound data. Its consumer `armResidGap_nonEvalChildFields` projects field by
-- name (no positional navigation).
structure NonEvalChildStages : Prop where
  stmtIfThen : ∀ (cnd : Expr) (t : Stmt) (e : Option Stmt) (c : Config) (st st' : SpecSt)
    (d : Nat) (env : Addr) (v : Value),
    EvalE st d env cnd st' v → v.truthy = true → SEntryC c st d env (.ifStmt cnd t e) →
    LandedN 1 c (fun c' => ExecStmtPreBundle t c' st' d env)
  stmtIfElse : ∀ (cnd : Expr) (t e : Stmt) (c : Config) (st st' : SpecSt)
    (d : Nat) (env : Addr) (v : Value),
    EvalE st d env cnd st' v → v.truthy = false → SEntryC c st d env (.ifStmt cnd t (some e)) →
    LandedN 1 c (fun c' => ExecStmtPreBundle e c' st' d env)
  stmtWhileBody : ∀ (cnd : Expr) (b : Stmt) (c : Config) (st st' : SpecSt)
    (d : Nat) (env : Addr) (v : Value),
    EvalE st d env cnd st' v → v.truthy = true → SEntryC c st d env (.whileStmt cnd b) →
    LandedN 1 c (fun c' => ExecStmtPreBundle b c' st' d env)
  stmtWhileLoop : ∀ (cnd : Expr) (b : Stmt) (c : Config) (st st' st'' : SpecSt)
    (d : Nat) (env : Addr) (v : Value) (status : Status),
    EvalE st d env cnd st' v → v.truthy = true → ExecS st' d env b st'' status →
    (status = .normal ∨ status = .cont) → SEntryC c st d env (.whileStmt cnd b) →
    LandedN 1 c (fun c' => ExecStmtPreBundle (.whileStmt cnd b) c' st'' d env)
  stmtForInit : ∀ (init : Stmt) (cnd step : Option Expr) (b : Stmt) (c : Config)
    (st : SpecSt) (d : Nat) (env : Addr) (store' : Store) (outer : Addr),
    st.store.allocFrame (some env) = (store', outer) →
    SEntryC c st d env (.forStmt (some init) cnd step b) →
    LandedN 1 c (fun c' => ExecStmtPreBundle init c' ⟨store', st.out⟩ d outer)
  flBody : ∀ (cnd : Option Expr) (step : Option Expr) (b : Stmt) (c : Config)
    (st st' : SpecSt) (d : Nat) (env : Addr),
    ForCond st d env cnd st' → FEntryC c st d env cnd step b →
    LandedN 1 c (fun c' => ExecStmtPreBundle b c' st' d env)
  callArgs : ∀ (f : Expr) (args : List Expr) (c : Config) (st st' : SpecSt)
    (d : Nat) (env : Addr) (fv : Value),
    EvalE st d env f st' fv → EEntryC c st d env (.call f args) →
    ∃ (argLoopPC dLeft aLeft : Nat),
      LandedN 1 c (fun c' => SegPreBundle argLoopPC c' st' d dLeft aLeft)
  argsTail : ∀ (e : Expr) (es : List Expr) (c : Config) (st st' : SpecSt)
    (d : Nat) (env : Addr) (v : Value),
    EvalE st d env e st' v → AEntryC c st d env (e :: es) →
    ∃ (argLoopPC dLeft aLeft : Nat),
      LandedN 1 c (fun c' => SegPreBundle argLoopPC c' st' d dLeft aLeft)
  callC : ∀ (f : Expr) (args : List Expr) (c : Config) (st st' st'' : SpecSt)
    (d : Nat) (env : Addr) (fv : Value) (vs : List Value),
    EvalE st d env f st' fv → EvalArgs st' d env args st'' vs →
    EEntryC c st d env (.call f args) →
    ∃ (calleeBodyPC dLeft aLeft : Nat),
      LandedN 1 c (fun c' => SegPreBundle calleeBodyPC c' st'' d dLeft aLeft)
  stmtForLoop : ∀ (init : Option Stmt) (cnd step : Option Expr) (b : Stmt) (c : Config)
    (st st' : SpecSt) (d : Nat) (env : Addr) (store' : Store) (outer : Addr),
    st.store.allocFrame (some env) = (store', outer) →
    ExecInit ⟨store', st.out⟩ d outer init st' →
    SEntryC c st d env (.forStmt init cnd step b) →
    ∃ (forCondPC dLeft aLeft : Nat),
      LandedN 1 c (fun c' => SegPreBundle forCondPC c' st' d dLeft aLeft)
  flLoop : ∀ (cnd : Option Expr) (step : Option Expr) (b : Stmt) (c : Config)
    (st st' st'' st''' : SpecSt) (d : Nat) (env : Addr) (status : Status),
    ForCond st d env cnd st' → ExecS st' d env b st'' status →
    (status = .normal ∨ status = .cont) → ExecStep st'' d env step st''' →
    FEntryC c st d env cnd step b →
    ∃ (forCondPC dLeft aLeft : Nat),
      LandedN 1 c (fun c' => SegPreBundle forCondPC c' st''' d dLeft aLeft)

/-- **The 11 non-eval-child fields of `ApproxArmResidGap`, discharged from
`NonEvalChildStages`.**  Each is `<field>_split` fed the bundled staging residual.
Returned as the exact conjunction of `ApproxArmResid` field types so the final
`ApproxArmResidGap` assembly consumes them directly, alongside
`ArmSegSplitEval.armResidGap_evalChildFields`. -/
theorem armResidGap_nonEvalChildFields (S : NonEvalChildStages) :
    (∀ (cnd : Expr) (t : Stmt) (e : Option Stmt) (c : Config) (st st' : SpecSt)
      (d : Nat) (env : Addr) (v : Value),
      EvalE st d env cnd st' v → v.truthy = true → SEntryC c st d env (.ifStmt cnd t e) →
      LandedN 1 c (fun c' => SEntryC c' st' d env t)) ∧
    (∀ (cnd : Expr) (t e : Stmt) (c : Config) (st st' : SpecSt) (d : Nat) (env : Addr) (v : Value),
      EvalE st d env cnd st' v → v.truthy = false → SEntryC c st d env (.ifStmt cnd t (some e)) →
      LandedN 1 c (fun c' => SEntryC c' st' d env e)) ∧
    (∀ (cnd : Expr) (b : Stmt) (c : Config) (st st' : SpecSt) (d : Nat) (env : Addr) (v : Value),
      EvalE st d env cnd st' v → v.truthy = true → SEntryC c st d env (.whileStmt cnd b) →
      LandedN 1 c (fun c' => SEntryC c' st' d env b)) ∧
    (∀ (cnd : Expr) (b : Stmt) (c : Config) (st st' st'' : SpecSt) (d : Nat) (env : Addr)
      (v : Value) (status : Status),
      EvalE st d env cnd st' v → v.truthy = true → ExecS st' d env b st'' status →
      (status = .normal ∨ status = .cont) → SEntryC c st d env (.whileStmt cnd b) →
      LandedN 1 c (fun c' => SEntryC c' st'' d env (.whileStmt cnd b))) ∧
    (∀ (init : Stmt) (cnd step : Option Expr) (b : Stmt) (c : Config) (st : SpecSt)
      (d : Nat) (env : Addr) (store' : Store) (outer : Addr),
      st.store.allocFrame (some env) = (store', outer) →
      SEntryC c st d env (.forStmt (some init) cnd step b) →
      LandedN 1 c (fun c' => SEntryC c' ⟨store', st.out⟩ d outer init)) ∧
    (∀ (cnd : Option Expr) (step : Option Expr) (b : Stmt) (c : Config) (st st' : SpecSt)
      (d : Nat) (env : Addr),
      ForCond st d env cnd st' → FEntryC c st d env cnd step b →
      LandedN 1 c (fun c' => SEntryC c' st' d env b)) ∧
    (∀ (f : Expr) (args : List Expr) (c : Config) (st st' : SpecSt) (d : Nat) (env : Addr)
      (fv : Value),
      EvalE st d env f st' fv → EEntryC c st d env (.call f args) →
      LandedN 1 c (fun c' => AEntryC c' st' d env args)) ∧
    (∀ (e : Expr) (es : List Expr) (c : Config) (st st' : SpecSt) (d : Nat) (env : Addr)
      (v : Value),
      EvalE st d env e st' v → AEntryC c st d env (e :: es) →
      LandedN 1 c (fun c' => AEntryC c' st' d env es)) ∧
    (∀ (f : Expr) (args : List Expr) (c : Config) (st st' st'' : SpecSt) (d : Nat) (env : Addr)
      (fv : Value) (vs : List Value),
      EvalE st d env f st' fv → EvalArgs st' d env args st'' vs →
      EEntryC c st d env (.call f args) →
      LandedN 1 c (fun c' => CEntryC c' st'' d fv vs)) ∧
    (∀ (init : Option Stmt) (cnd step : Option Expr) (b : Stmt) (c : Config) (st st' : SpecSt)
      (d : Nat) (env : Addr) (store' : Store) (outer : Addr),
      st.store.allocFrame (some env) = (store', outer) →
      ExecInit ⟨store', st.out⟩ d outer init st' →
      SEntryC c st d env (.forStmt init cnd step b) →
      LandedN 1 c (fun c' => FEntryC c' st' d outer cnd step b)) ∧
    (∀ (cnd : Option Expr) (step : Option Expr) (b : Stmt) (c : Config)
      (st st' st'' st''' : SpecSt) (d : Nat) (env : Addr) (status : Status),
      ForCond st d env cnd st' → ExecS st' d env b st'' status →
      (status = .normal ∨ status = .cont) → ExecStep st'' d env step st''' →
      FEntryC c st d env cnd step b →
      LandedN 1 c (fun c' => FEntryC c' st''' d env cnd step b)) :=
  ⟨fun cnd t e c st st' d env v => stmtIfThen_split cnd t e c st st' d env v (S.stmtIfThen cnd t e c st st' d env v),
   fun cnd t e c st st' d env v => stmtIfElse_split cnd t e c st st' d env v (S.stmtIfElse cnd t e c st st' d env v),
   fun cnd b c st st' d env v => stmtWhileBody_split cnd b c st st' d env v (S.stmtWhileBody cnd b c st st' d env v),
   fun cnd b c st st' st'' d env v status =>
     stmtWhileLoop_split cnd b c st st' st'' d env v status (S.stmtWhileLoop cnd b c st st' st'' d env v status),
   fun init cnd step b c st d env store' outer =>
     stmtForInit_split init cnd step b c st d env store' outer (S.stmtForInit init cnd step b c st d env store' outer),
   fun cnd step b c st st' d env => flBody_split cnd step b c st st' d env (S.flBody cnd step b c st st' d env),
   fun f args c st st' d env fv hE hEE => by
     obtain ⟨argLoopPC, dLeft, aLeft, hst⟩ := S.callArgs f args c st st' d env fv hE hEE
     exact callArgs_split f args c st st' d env fv argLoopPC dLeft aLeft ⟨0, 0⟩
       (fun _ _ => hst) hE hEE,
   fun e es c st st' d env v hE hAE => by
     obtain ⟨argLoopPC, dLeft, aLeft, hst⟩ := S.argsTail e es c st st' d env v hE hAE
     exact argsTail_split e es c st st' d env v argLoopPC dLeft aLeft ⟨0, 0⟩
       (fun _ _ => hst) hE hAE,
   fun f args c st st' st'' d env fv vs hE hA hEE => by
     obtain ⟨calleeBodyPC, dLeft, aLeft, hst⟩ := S.callC f args c st st' st'' d env fv vs hE hA hEE
     exact callC_split f args c st st' st'' d env fv vs calleeBodyPC dLeft aLeft ⟨0, 0⟩
       (fun _ _ _ => hst) hE hA hEE,
   fun init cnd step b c st st' d env store' outer hAlloc hInit hSE => by
     obtain ⟨forCondPC, dLeft, aLeft, hst⟩ := S.stmtForLoop init cnd step b c st st' d env store' outer hAlloc hInit hSE
     exact stmtForLoop_split init cnd step b c st st' d env store' outer forCondPC dLeft aLeft ⟨0, 0⟩
       (fun _ _ _ => hst) hAlloc hInit hSE,
   fun cnd step b c st st' st'' st''' d env status hFC hEx hst0 hStep hFE => by
     obtain ⟨forCondPC, dLeft, aLeft, hst⟩ := S.flLoop cnd step b c st st' st'' st''' d env status hFC hEx hst0 hStep hFE
     exact flLoop_split cnd step b c st st' st'' st''' d env status forCondPC dLeft aLeft ⟨0, 0⟩
       (fun _ _ _ _ _ => hst) hFC hEx hst0 hStep hFE⟩

#print axioms armResidGap_nonEvalChildFields

end Vsa.Sim
