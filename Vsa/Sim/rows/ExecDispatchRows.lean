import Vsa.Sim.ExecIf
import Vsa.Sim.ExecIf2
import Vsa.Sim.ExecWhile
import Vsa.Sim.ExecWhile2
import Vsa.Sim.ExecBlock2
import Vsa.Sim.ExecForStart
import Vsa.Sim.rows.ExecIHWiden
import Vsa.Sim.TermSimClose

/-!
# Layer 4 — M4 dispatch/loop `ExecS` cases re-landed at `ExecExitD` (the `mExecS` motive)

The dispatch/loop statement-side twin of `rows/ExecRecRows.lean`, built ON the ONE
exit-sim → motive combinator `execIH_of_exitSim` (`rows/ExecIHWiden.lean`).  Each
landed dispatch/loop simulation (`execIfNoneSim`/`execIfTrueSim`/`execIfFalseSim`/
`execWhileFalseSim`/`execWhileSim`/`execBlockSim`/`execForStartSim`) concludes the
packaged shape `ExecExitSim … status` (the `Triple` from `ExecEntry ∧ out=out0` to
plain `ExecExit`); the combinator upgrades it to the `mExecS` motive `ExecIH` (entry
`out0 := c.σ.sailOutput` by `rfl`; exit widened `ExecExit → ExecExitD` by the
parametric `ExecRecWiden`).  So EVERY row here is `execIH_of_exitSim hW hSim` with
ZERO hand-navigated `intro`/`obtain`/`refine` — the widen-and-marshal lives once in
the combinator.

## The residual bundle shape — a named `structure`, projected per call

Each case's residual bundle is a `structure … : Prop where` with named fields (gate
R6/R7: no positional `.2.2` towers) carrying EXACTLY the landed sim's OWN residual
arguments (its `hGlue`/`hslot`/`hmaps`/`hstep`/`hArm`/`hEpi`/branch-IH) plus the
widener `hW`.  A `*Resid` is that structure ∀-closed over the ghosts.  The row projects
`.hW` into the combinator's widener slot and the rest into the sim's argument slots.
Adding a new dispatch/loop case is: one named structure + one `execIH_of_exitSim` line.

## The one structural residual worth flagging: `if`'s branch IH

`execIfTrueSim`/`execIfFalseSim` consume the branch derivation as an
`ExecDispatchIH` (the branch re-enters the shared `if` frame POST-prologue at
`0x80004014` — no second prologue).  The recursor hands the branch sub-derivation as
`mExecS = ExecIH` (the FULL-entry shape through the prologue at `0x80003fe0`).  There
is no `ExecIH → ExecDispatchIH` bridge, and there cannot be a trivial one: the
re-dispatch SKIPS the prologue.  So the `ExecDispatchIH` is a genuine SEPARATE
residual, carried as the field `hBranch` of `IfTrueGeom`/`IfFalseGeom`; the recursor's
`ExecIH` is threaded too (the honest spec witness).  See observations
`if-branch-dispatch-ih`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

-- discipline: allow(R7-conj-tower-def) The `∃`s counted here are NOT new anonymous
-- post-towers: every one is the field TYPE of a named `*Geom` structure, re-stating a
-- LANDED sim post predicate (`SubExecReturn`/`ExecDispatchReady`, whose ∃-shape is
-- fixed by `execIfNoneSim`/`execIfTrueSim`/… signatures) so the residual bundle unifies
-- with the sim it feeds. The bundles ARE named-field structures (R6/R7-compliant); the
-- inner ∃ belongs to the sim's own post, not to this file. Twin of the grandfathered
-- `rows/ExecRecRows.lean` (same `SubExecReturn` field shapes).

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim.Rows

open Vsa.Sim
open Vsa.Sim.TermSimAssembly

local notation "SpecSt" => Vsa.While.St

/-! ## `ifNone` -/

/-- `execIfNoneSim`'s residual bundle (one ghost layout): the `execBlockA` slot pin +
stack-disjointness, the arm-body glue (cond eval ≫ `value_truthy` falsy ≫ else-absent
≫ `SubExecReturn @ 0x800042d4`), and the `.normal` widener. -/
structure IfNoneGeom
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : SpecSt) (d : Nat) (env : Addr) (c : Expr) (t : Stmt) (v : Value)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) : Prop where
  hslot : StmtSlotPinned 3 execArmIf m0
  htableStk : stmtJumpTableBase + 4 * 3 + 4 ≤ SL.lo ∨ sp.toNat ≤ stmtJumpTableBase + 4 * 3
  hGlue : ∀ out0 : Array String,
    EvalIH st d env c st' v →
      Triple
        (fun cfg => ∃ ment v8 v9 v18 v19,
          ExecArmEntryK g N A SL φf φc st execArmIf sp r aInterp aStmt aEnv aRet
            v8 v9 v18 v19 out0 m0 ment cfg)
        (fun cfg => ∃ subsret v1 v8 v9 v18 v19 mcall,
          SubExecReturn g N A SL φf φc st.store.frames.size st.store.closures.size st' v
            sp r aRet subsret (0x800042d4#64) v1 v8 v9 v18 v19 m0 mcall cfg)
  hW : ExecRecWiden g N A SL φf φc st.store.frames.size st.store.closures.size st' .normal sp r aRet m0

/-- The ifNone residual: `IfNoneGeom` ∀-closed over the ghosts. -/
def IfNoneResid (st st' : SpecSt) (d : Nat) (env : Addr) (c : Expr) (t : Stmt) (v : Value) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem),
    IfNoneGeom g N A SL φf φc st st' d env c t v sp r aInterp aStmt aEnv aRet m0

/-- Route `hSIfNone` → `execIH_of_exitSim` over `execIfNoneSim`.  The cond `EvalIH`
passes to the sim's `hIH` by `rfl`; the falsy hypothesis `a_1` is the sim's own spec
premise `hSpec`. -/
theorem exec_ifNone_row
    (hR : ∀ st st' d env c t v, IfNoneResid st st' d env c t v) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (t : Stmt) (st' : SpecSt) (v : Value)
      (a : EvalE st d env c st' v) (a_1 : v.truthy = false),
      mEvalE st d env c st' v a →
      mExecS st d env (Stmt.ifStmt c t none) st' Status.normal (ExecS.ifNone st d env c t st' v a a_1) := by
  intro st d env c t st' v a a_1 hIH
  show ExecIH st d env (.ifStmt c t none) st' .normal
  exact execIH_of_exitSim
    (fun g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 =>
      (hR st st' d env c t v g N A SL φf φc sp r aInterp aStmt aEnv aRet m0).hW)
    (fun g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 out0 =>
      let G := hR st st' d env c t v g N A SL φf φc sp r aInterp aStmt aEnv aRet m0
      execIfNoneSim g N A SL φf φc st st' d env c t v sp r aInterp aStmt aEnv aRet m0
        out0 (ExecS.ifNone st d env c t st' v a a_1) hIH G.hslot G.htableStk (G.hGlue out0))

/-! ## `whileFalse` — `execWhileFalseSim`'s twin at the `whileStmt` arm (kind 4) -/

/-- `execWhileFalseSim`'s residual bundle: as `IfNoneGeom` but at `execArmWhile`
(kind 4, `0x8000403c`, sret buffer `sp'+80`, `SubExecReturn @ 0x80004090`). -/
structure WhileFalseGeom
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : SpecSt) (d : Nat) (env : Addr) (c : Expr) (b : Stmt) (v : Value)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) : Prop where
  hslot : StmtSlotPinned 4 execArmWhile m0
  htableStk : stmtJumpTableBase + 4 * 4 + 4 ≤ SL.lo ∨ sp.toNat ≤ stmtJumpTableBase + 4 * 4
  hGlue : ∀ out0 : Array String,
    EvalIH st d env c st' v →
      Triple
        (fun cfg => ∃ ment v8 v9 v18 v19,
          ExecArmEntryK g N A SL φf φc st execArmWhile sp r aInterp aStmt aEnv aRet
            v8 v9 v18 v19 out0 m0 ment cfg)
        (fun cfg => ∃ subsret v1 v8 v9 v18 v19 mcall,
          SubExecReturn g N A SL φf φc st.store.frames.size st.store.closures.size st' v
            sp r aRet subsret (0x80004090#64) v1 v8 v9 v18 v19 m0 mcall cfg)
  hW : ExecRecWiden g N A SL φf φc st.store.frames.size st.store.closures.size st' .normal sp r aRet m0

/-- The whileFalse residual: `WhileFalseGeom` ∀-closed over the ghosts. -/
def WhileFalseResid (st st' : SpecSt) (d : Nat) (env : Addr) (c : Expr) (b : Stmt) (v : Value) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem),
    WhileFalseGeom g N A SL φf φc st st' d env c b v sp r aInterp aStmt aEnv aRet m0

/-- Route `hSWhileFalse` → `execIH_of_exitSim` over `execWhileFalseSim`. -/
theorem exec_whileFalse_row
    (hR : ∀ st st' d env c b v, WhileFalseResid st st' d env c b v) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (b : Stmt) (st' : SpecSt) (v : Value)
      (a : EvalE st d env c st' v) (a_1 : v.truthy = false),
      mEvalE st d env c st' v a →
      mExecS st d env (Stmt.whileStmt c b) st' Status.normal (ExecS.whileFalse st d env c b st' v a a_1) := by
  intro st d env c b st' v a a_1 hIH
  show ExecIH st d env (.whileStmt c b) st' .normal
  exact execIH_of_exitSim
    (fun g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 =>
      (hR st st' d env c b v g N A SL φf φc sp r aInterp aStmt aEnv aRet m0).hW)
    (fun g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 out0 =>
      let G := hR st st' d env c b v g N A SL φf φc sp r aInterp aStmt aEnv aRet m0
      execWhileFalseSim g N A SL φf φc st st' d env c b v sp r aInterp aStmt aEnv aRet m0
        out0 (ExecS.whileFalse st d env c b st' v a a_1) hIH a_1 G.hslot G.htableStk (G.hGlue out0))

/-! ## `ifTrue` — `execIfTrueSim` (re-dispatch; carries the branch `ExecDispatchIH`) -/

/-- `execIfTrueSim`'s residual bundle: the branch `ExecDispatchIH` (the genuine
separate residual — see module doc), the slot pins, the frame-alloc `hmaps`, the
arm-body glue reaching `ExecDispatchReady` for the `then` branch, and the widener. -/
structure IfTrueGeom
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : SpecSt) (d : Nat) (env : Addr) (c : Expr) (t : Stmt)
    (e : Option Stmt) (v : Value) (status : Status)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) : Prop where
  hBranch : ExecDispatchIH st' d env t st'' status
  hslot : StmtSlotPinned 3 execArmIf m0
  htableStk : stmtJumpTableBase + 4 * 3 + 4 ≤ SL.lo ∨ sp.toNat ≤ stmtJumpTableBase + 4 * 3
  hmaps : ∀ (φfE φcE : Addr → Nat) (cD : Config),
    PhiExtends φf φfE st'.store.frames.size →
    PhiExtends φc φcE st'.store.closures.size →
    ExecExit g N A SL φfE φcE st'.store.frames.size st'.store.closures.size
      st'' status sp r aRet m0 cD →
    ExecExit g N A SL φf φc st.store.frames.size st.store.closures.size
      st'' status sp r aRet m0 cD
  hGlue : ∀ out0 : Array String, EvalIH st d env c st' v →
    Triple
      (fun cfg => ∃ ment v8 v9 v18 v19,
        ExecArmEntryK g N A SL φf φc st execArmIf sp r aInterp aStmt aEnv aRet
          v8 v9 v18 v19 out0 m0 ment cfg)
      (fun cfg => ∃ (φfE φcE : Addr → Nat) (aThen : BitVec 64)
          (ment : Mem) (v8 v9 v18 v19 : BitVec 64),
        PhiExtends φf φfE st'.store.frames.size ∧
        PhiExtends φc φcE st'.store.closures.size ∧
        ExecDispatchReady g N A SL φfE φcE st' t sp r aInterp aThen aEnv aRet
          v8 v9 v18 v19 out0 m0 ment cfg)
  hW : ExecRecWiden g N A SL φf φc st.store.frames.size st.store.closures.size st'' status sp r aRet m0

/-- The ifTrue residual: `IfTrueGeom` ∀-closed over the ghosts. -/
def IfTrueResid (st st' st'' : SpecSt) (d : Nat) (env : Addr) (c : Expr) (t : Stmt)
    (e : Option Stmt) (v : Value) (status : Status) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem),
    IfTrueGeom g N A SL φf φc st st' st'' d env c t e v status sp r aInterp aStmt aEnv aRet m0

/-- Route `hSIfTrue` → `execIH_of_exitSim` over `execIfTrueSim`.  The `hGlue` field is
stated at the per-config `cfg.σ.sailOutput`, matching what `execIfTrueSim` expects
(its `hGlue` is NOT `out0`-quantified — it fires at the sim's chosen entry output). -/
theorem exec_ifTrue_row
    (hR : ∀ st st' st'' d env c t e v status, IfTrueResid st st' st'' d env c t e v status) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (t : Stmt) (e : Option Stmt)
      (st' st'' : SpecSt) (v : Value) (status : Status)
      (a : EvalE st d env c st' v) (a_1 : v.truthy = true) (a_2 : ExecS st' d env t st'' status),
      mEvalE st d env c st' v a →
      mExecS st' d env t st'' status a_2 →
      mExecS st d env (Stmt.ifStmt c t e) st'' status (ExecS.ifTrue st d env c t e st' st'' v status a a_1 a_2) := by
  intro st d env c t e st' st'' v status a a_1 a_2 hIH _hBranch
  show ExecIH st d env (.ifStmt c t e) st'' status
  exact execIH_of_exitSim
    (fun g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 =>
      (hR st st' st'' d env c t e v status g N A SL φf φc sp r aInterp aStmt aEnv aRet m0).hW)
    (fun g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 out0 =>
      let G := hR st st' st'' d env c t e v status g N A SL φf φc sp r aInterp aStmt aEnv aRet m0
      execIfTrueSim g N A SL φf φc st st' st'' d env c t e status v
        sp r aInterp aStmt aEnv aRet m0 out0 (ExecS.ifTrue st d env c t e st' st'' v status a a_1 a_2)
        hIH a_1 G.hBranch G.hslot G.htableStk G.hmaps (G.hGlue out0))

/-! ## `ifFalse` — symmetric to `ifTrue` (else branch, `bnez` taken) -/

/-- `execIfFalseSim`'s residual bundle: the `else`-branch `ExecDispatchIH`, slot pins,
`hmaps`, arm-body glue reaching `ExecDispatchReady` for `e`, widener. -/
structure IfFalseGeom
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : SpecSt) (d : Nat) (env : Addr) (c : Expr) (t e : Stmt)
    (v : Value) (status : Status)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) : Prop where
  hBranch : ExecDispatchIH st' d env e st'' status
  hslot : StmtSlotPinned 3 execArmIf m0
  htableStk : stmtJumpTableBase + 4 * 3 + 4 ≤ SL.lo ∨ sp.toNat ≤ stmtJumpTableBase + 4 * 3
  hmaps : ∀ (φfE φcE : Addr → Nat) (cD : Config),
    PhiExtends φf φfE st'.store.frames.size →
    PhiExtends φc φcE st'.store.closures.size →
    ExecExit g N A SL φfE φcE st'.store.frames.size st'.store.closures.size
      st'' status sp r aRet m0 cD →
    ExecExit g N A SL φf φc st.store.frames.size st.store.closures.size
      st'' status sp r aRet m0 cD
  hGlue : ∀ out0 : Array String, EvalIH st d env c st' v →
    Triple
      (fun cfg => ∃ ment v8 v9 v18 v19,
        ExecArmEntryK g N A SL φf φc st execArmIf sp r aInterp aStmt aEnv aRet
          v8 v9 v18 v19 out0 m0 ment cfg)
      (fun cfg => ∃ (φfE φcE : Addr → Nat) (aElse : BitVec 64)
          (ment : Mem) (v8 v9 v18 v19 : BitVec 64),
        PhiExtends φf φfE st'.store.frames.size ∧
        PhiExtends φc φcE st'.store.closures.size ∧
        ExecDispatchReady g N A SL φfE φcE st' e sp r aInterp aElse aEnv aRet
          v8 v9 v18 v19 out0 m0 ment cfg)
  hW : ExecRecWiden g N A SL φf φc st.store.frames.size st.store.closures.size st'' status sp r aRet m0

/-- The ifFalse residual: `IfFalseGeom` ∀-closed over the ghosts. -/
def IfFalseResid (st st' st'' : SpecSt) (d : Nat) (env : Addr) (c : Expr) (t e : Stmt)
    (v : Value) (status : Status) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem),
    IfFalseGeom g N A SL φf φc st st' st'' d env c t e v status sp r aInterp aStmt aEnv aRet m0

/-- Route `hSIfFalse` → `execIH_of_exitSim` over `execIfFalseSim`. -/
theorem exec_ifFalse_row
    (hR : ∀ st st' st'' d env c t e v status, IfFalseResid st st' st'' d env c t e v status) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (t e : Stmt)
      (st' st'' : SpecSt) (v : Value) (status : Status)
      (a : EvalE st d env c st' v) (a_1 : v.truthy = false) (a_2 : ExecS st' d env e st'' status),
      mEvalE st d env c st' v a →
      mExecS st' d env e st'' status a_2 →
      mExecS st d env (Stmt.ifStmt c t (some e)) st'' status (ExecS.ifFalse st d env c t e st' st'' v status a a_1 a_2) := by
  intro st d env c t e st' st'' v status a a_1 a_2 hIH _hBranch
  show ExecIH st d env (.ifStmt c t (some e)) st'' status
  exact execIH_of_exitSim
    (fun g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 =>
      (hR st st' st'' d env c t e v status g N A SL φf φc sp r aInterp aStmt aEnv aRet m0).hW)
    (fun g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 out0 =>
      let G := hR st st' st'' d env c t e v status g N A SL φf φc sp r aInterp aStmt aEnv aRet m0
      execIfFalseSim g N A SL φf φc st st' st'' d env c t e status v
        sp r aInterp aStmt aEnv aRet m0 out0 (ExecS.ifFalse st d env c t e st' st'' v status a a_1 a_2)
        hIH a_1 G.hBranch G.hslot G.htableStk G.hmaps (G.hGlue out0))

/-! ## `block` — `execBlockSim` (env_new + execSeqLoop + epilogue) -/

/-- `execBlockSim`'s residual bundle: the `execSeqLoop` engine premises (`hstep`
`ExecSeqStep` + `hnil`) and the `hArm`/`hEpi` env_new/allocFrame linkage; the widener
absorbs `allocFrame`'s non-identity φ. -/
structure BlockGeom
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : SpecSt) (d : Nat) (env : Addr) (ss : List Stmt) (status : Status)
    (store' : Store) (inner : Addr)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) : Prop where
  hstep : ∀ (φf₀ φc₀ : Addr → Nat) (stM : SpecSt) (sH : Stmt) (ssH : List Stmt)
      (stM' stFinH : SpecSt) (statusH : Status) (m00 : Mem),
      ExecSeqStep g N A SL φf₀ φc₀ stM d inner sH ssH sp r
        execSeqLoopPC execSeqContPC m00 stM' stFinH statusH
  hnil : ∀ (φf₀ φc₀ : Addr → Nat) (stN : SpecSt) (m00 : Mem),
      Triple
        (ExecSeqEntry g N A SL φf₀ φc₀ stN d inner [] sp r execSeqLoopPC m00)
        (ExecSeqExit g N A SL φf₀ φc₀ stN.store.frames.size stN.store.closures.size
          stN .normal sp r execSeqContPC m00)
  hArm : ∀ out0 : Array String, ∀ (φf' φc' : Addr → Nat),
    Triple
      (fun c => ExecEntry g N A SL φf φc st d env (.block ss) sp r aInterp aStmt aEnv aRet m0 c
        ∧ c.σ.sailOutput = out0)
      (fun c => ∃ m0', PhiExtends φf φf' store'.frames.size ∧
        PhiExtends φc φc' store'.closures.size ∧
        ExecSeqEntry g N A SL φf' φc' ⟨store', st.out⟩ d inner ss sp r execSeqLoopPC m0' c)
  hEpi : ∀ (φf' φc' : Addr → Nat) (m0' : Mem),
    Triple
      (ExecSeqExit g N A SL φf' φc' store'.frames.size store'.closures.size
        st' status sp r execSeqContPC m0')
      (ExecExit g N A SL φf φc st.store.frames.size st.store.closures.size
        st' status sp r aRet m0)
  hW : ExecRecWiden g N A SL φf φc st.store.frames.size st.store.closures.size st' status sp r aRet m0

/-- The block residual: `BlockGeom` ∀-closed over the ghosts.  `store'`/`inner` come
from the derivation's `allocFrame`, so they are parameters of the residual. -/
def BlockResid (st st' : SpecSt) (d : Nat) (env : Addr) (ss : List Stmt) (status : Status)
    (store' : Store) (inner : Addr) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem),
    BlockGeom g N A SL φf φc st st' d env ss status store' inner sp r aInterp aStmt aEnv aRet m0

/-- Route `hSBlock` → `execIH_of_exitSim` over `execBlockSim`.  The inner `mExecSeq`
sub-derivation feeds `execSeqLoop` (driven by `hstep`/`hnil`). -/
theorem exec_block_row
    (hR : ∀ st st' d env ss status store' inner, BlockResid st st' d env ss status store' inner) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (ss : List Stmt) (store' : Store) (inner : Addr)
      (st' : SpecSt) (status : Status) (a : st.store.allocFrame (some env) = (store', inner))
      (a_1 : ExecSeq { store := store', out := st.out } d inner ss st' status),
      mExecSeq { store := store', out := st.out } d inner ss st' status a_1 →
      mExecS st d env (Stmt.block ss) st' status (ExecS.block st d env ss store' inner st' status a a_1) := by
  intro st d env ss store' inner st' status a a_1 _hSeqIH
  show ExecIH st d env (.block ss) st' status
  exact execIH_of_exitSim
    (fun g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 =>
      (hR st st' d env ss status store' inner g N A SL φf φc sp r aInterp aStmt aEnv aRet m0).hW)
    (fun g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 out0 =>
      let G := hR st st' d env ss status store' inner g N A SL φf φc sp r aInterp aStmt aEnv aRet m0
      execBlockSim g N A SL φf φc st st' d env ss status store' inner
        sp r aInterp aStmt aEnv aRet m0 out0 a a_1 G.hstep G.hnil (G.hArm out0) G.hEpi)

/-! ## `forStart` — `execForStartSim` (env_new + ExecInit + execForLoopBody) -/

/-- `execForStartSim`'s residual bundle: the `ExecForStep` oracle `hstep`, the
recursive sub-`for` IH `hForIH`, and the `hArm`/`hEpi` env_new/allocFrame linkage. -/
structure ForStartGeom
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : SpecSt) (d : Nat) (env : Addr)
    (init : Option Stmt) (cnd step : Option Expr) (b : Stmt) (status : Status)
    (store' : Store) (outer : Addr)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) : Prop where
  hstep : ∀ (φf₀ φc₀ : Addr → Nat) (stM stMid stFin : SpecSt)
      (bodyStatus loopStatus : Status) (m00 : Mem) (out00 : Array String),
      ExecForStep g N A SL φf₀ φc₀ stM d outer init cnd step b
        sp r aInterp aStmt aEnv aRet m00 out00 stMid stFin bodyStatus loopStatus
  hForIH : ∀ (φf' φc' : Addr → Nat) (stA stB : SpecSt)
      (status' : Status) (m0' : Mem) (out0' : Array String),
      ForLoop stA d outer cnd step b stB status' →
      Triple
        (fun cfg => ExecEntry g N A SL φf' φc' stA d outer (.forStmt init cnd step b)
          sp r aInterp aStmt aEnv aRet m0' cfg ∧ cfg.σ.sailOutput = out0')
        (ExecExit g N A SL φf' φc' stA.store.frames.size stA.store.closures.size
          stB status' sp r aRet m0')
  hArm : ∀ out0 : Array String, ∀ (φf' φc' : Addr → Nat),
    Triple
      (fun c => ExecEntry g N A SL φf φc st d env (.forStmt init cnd step b)
        sp r aInterp aStmt aEnv aRet m0 c ∧ c.σ.sailOutput = out0)
      (fun c => ∃ m0', PhiExtends φf φf' st'.store.frames.size ∧
        PhiExtends φc φc' st'.store.closures.size ∧
        ExecEntry g N A SL φf' φc' st' d outer (.forStmt init cnd step b)
          sp r aInterp aStmt aEnv aRet m0' c ∧ c.σ.sailOutput = out0)
  hEpi : ∀ (φf' φc' : Addr → Nat) (m0' : Mem),
    Triple
      (ExecExit g N A SL φf' φc' st'.store.frames.size st'.store.closures.size
        st'' status sp r aRet m0')
      (ExecExit g N A SL φf φc st.store.frames.size st.store.closures.size
        st'' status sp r aRet m0)
  hW : ExecRecWiden g N A SL φf φc st.store.frames.size st.store.closures.size st'' status sp r aRet m0

/-- The forStart residual: `ForStartGeom` ∀-closed over the ghosts. -/
def ForStartResid (st st' st'' : SpecSt) (d : Nat) (env : Addr)
    (init : Option Stmt) (cnd step : Option Expr) (b : Stmt) (status : Status)
    (store' : Store) (outer : Addr) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem),
    ForStartGeom g N A SL φf φc st st' st'' d env init cnd step b status
      store' outer sp r aInterp aStmt aEnv aRet m0

/-- Route `hSForStart` → `execIH_of_exitSim` over `execForStartSim`. -/
theorem exec_forStart_row
    (hR : ∀ st st' st'' d env init cnd step b status store' outer,
      ForStartResid st st' st'' d env init cnd step b status store' outer) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (init : Option Stmt) (cnd step : Option Expr) (b : Stmt)
      (store' : Store) (outer : Addr) (st' st'' : SpecSt) (status : Status)
      (a : st.store.allocFrame (some env) = (store', outer))
      (a_1 : ExecInit { store := store', out := st.out } d outer init st')
      (a_2 : ForLoop st' d outer cnd step b st'' status),
      mExecInit { store := store', out := st.out } d outer init st' a_1 →
      mForLoop st' d outer cnd step b st'' status a_2 →
      mExecS st d env (Stmt.forStmt init cnd step b) st'' status
        (ExecS.forStart st d env init cnd step b store' outer st' st'' status a a_1 a_2) := by
  intro st d env init cnd step b store' outer st' st'' status a a_1 a_2 _hInitIH _hForIH
  show ExecIH st d env (.forStmt init cnd step b) st'' status
  exact execIH_of_exitSim
    (fun g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 =>
      (hR st st' st'' d env init cnd step b status store' outer
        g N A SL φf φc sp r aInterp aStmt aEnv aRet m0).hW)
    (fun g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 out0 =>
      let G := hR st st' st'' d env init cnd step b status store' outer
        g N A SL φf φc sp r aInterp aStmt aEnv aRet m0
      execForStartSim g N A SL φf φc st st' st'' d env init cnd step b status store' outer
        sp r aInterp aStmt aEnv aRet m0 out0 a a_1 a_2 G.hstep G.hForIH (G.hArm out0) G.hEpi)

/-! ## `whileBreak` / `whileRet` / `whileLoop` — ONE geom, ONE sim, three rows

`execWhileSim` (`ExecWhile2.lean`) unifies ALL FOUR `whileStmt` constructors into ONE
`Triple (ExecEntry) (ExecExit)`, dispatching on the `ExecS` derivation, taking the
per-iteration `ExecWhileStep` oracle `hstep` (the loop-body machine chain — the
genuine open content per the loop-fanout ledger) and the recursive sub-`while` IH
`hWhileIH` (the recursor's `mExecS = ExecIH` for the `whileLoop` premise, `.1`-mapped
`ExecExitD → ExecExit`).  ONE `WhileGeom` + the combinator serve all three recursive/
exit constructors. -/

/-- `execWhileSim`'s residual bundle: the `ExecWhileStep` oracle + the recursive
sub-`while` IH; the widener upgrades the unified `ExecExit`. -/
structure WhileGeom
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : SpecSt) (d : Nat) (env : Addr) (c : Expr) (b : Stmt) (status : Status)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) : Prop where
  hstep : ∀ (φf₀ φc₀ : Addr → Nat) (stM stMid stFin : SpecSt)
      (bodyStatus loopStatus : Status) (m00 : Mem) (out00 : Array String),
      ExecWhileStep g N A SL φf₀ φc₀ stM d env c b sp r aInterp aStmt aEnv aRet m00 out00
        stMid stFin bodyStatus loopStatus
  hWhileIH : ∀ (φf' φc' : Addr → Nat) (st'' st''' : SpecSt)
      (status' : Status) (m0' : Mem) (out0' : Array String),
      ExecS st'' d env (.whileStmt c b) st''' status' →
      Triple
        (fun cfg => ExecEntry g N A SL φf' φc' st'' d env (.whileStmt c b)
          sp r aInterp aStmt aEnv aRet m0' cfg ∧ cfg.σ.sailOutput = out0')
        (ExecExit g N A SL φf' φc' st''.store.frames.size st''.store.closures.size
          st''' status' sp r aRet m0')
  hW : ExecRecWiden g N A SL φf φc st.store.frames.size st.store.closures.size st' status sp r aRet m0

/-- The while-family residual: `WhileGeom` ∀-closed over the ghosts. -/
def WhileResid (st st' : SpecSt) (d : Nat) (env : Addr) (c : Expr) (b : Stmt) (status : Status) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem),
    WhileGeom g N A SL φf φc st st' d env c b status sp r aInterp aStmt aEnv aRet m0

/-- Shared while-family dispatcher: given the residual and an `ExecS` derivation of
`.whileStmt c b`, produce the `ExecIH`.  All three recursive/exit rows are one
instantiation. -/
theorem execWhileIH_of_resid
    {st st' : SpecSt} {d : Nat} {env : Addr} {c : Expr} {b : Stmt} {status : Status}
    (hExec : ExecS st d env (.whileStmt c b) st' status)
    (hR : WhileResid st st' d env c b status) :
    ExecIH st d env (.whileStmt c b) st' status :=
  execIH_of_exitSim
    (fun g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 =>
      (hR g N A SL φf φc sp r aInterp aStmt aEnv aRet m0).hW)
    (fun g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 out0 =>
      let G := hR g N A SL φf φc sp r aInterp aStmt aEnv aRet m0
      execWhileSim g N A SL d env c b sp r aInterp aStmt aEnv aRet G.hstep G.hWhileIH
        φf φc st st' status m0 out0 hExec)

/-- Route `hSWhileBreak` → `execWhileIH_of_resid`. -/
theorem exec_whileBreak_row
    (hR : ∀ st st' d env c b status, WhileResid st st' d env c b status) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (b : Stmt) (st' st'' : SpecSt) (v : Value)
      (a : EvalE st d env c st' v) (a_1 : v.truthy = true) (a_2 : ExecS st' d env b st'' Status.brk),
      mEvalE st d env c st' v a →
      mExecS st' d env b st'' Status.brk a_2 →
      mExecS st d env (Stmt.whileStmt c b) st'' Status.normal (ExecS.whileBreak st d env c b st' st'' v a a_1 a_2) := by
  intro st d env c b st' st'' v a a_1 a_2 _hCond _hBody
  exact execWhileIH_of_resid (ExecS.whileBreak st d env c b st' st'' v a a_1 a_2)
    (hR st st'' d env c b .normal)

/-- Route `hSWhileRet` → `execWhileIH_of_resid`. -/
theorem exec_whileRet_row
    (hR : ∀ st st' d env c b status, WhileResid st st' d env c b status) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (b : Stmt) (st' st'' : SpecSt) (v rv : Value)
      (a : EvalE st d env c st' v) (a_1 : v.truthy = true) (a_2 : ExecS st' d env b st'' (Status.ret rv)),
      mEvalE st d env c st' v a →
      mExecS st' d env b st'' (Status.ret rv) a_2 →
      mExecS st d env (Stmt.whileStmt c b) st'' (Status.ret rv) (ExecS.whileRet st d env c b st' st'' v rv a a_1 a_2) := by
  intro st d env c b st' st'' v rv a a_1 a_2 _hCond _hBody
  exact execWhileIH_of_resid (ExecS.whileRet st d env c b st' st'' v rv a a_1 a_2)
    (hR st st'' d env c b (.ret rv))

/-- Route `hSWhileLoop` → `execWhileIH_of_resid`.  The recursive sub-`while` IH
(`a_4`'s motive) is carried by `WhileGeom.hWhileIH`. -/
theorem exec_whileLoop_row
    (hR : ∀ st st' d env c b status, WhileResid st st' d env c b status) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (b : Stmt) (st' st'' st''' : SpecSt) (v : Value)
      (status status' : Status)
      (a : EvalE st d env c st' v) (a_1 : v.truthy = true) (a_2 : ExecS st' d env b st'' status)
      (a_3 : status = Status.normal ∨ status = Status.cont)
      (a_4 : ExecS st'' d env (Stmt.whileStmt c b) st''' status'),
      mEvalE st d env c st' v a →
      mExecS st' d env b st'' status a_2 →
      mExecS st'' d env (Stmt.whileStmt c b) st''' status' a_4 →
      mExecS st d env (Stmt.whileStmt c b) st''' status'
        (ExecS.whileLoop st d env c b st' st'' st''' v status status' a a_1 a_2 a_3 a_4) := by
  intro st d env c b st' st'' st''' v status status' a a_1 a_2 a_3 a_4 _hCond _hBody _hRest
  exact execWhileIH_of_resid
    (ExecS.whileLoop st d env c b st' st'' st''' v status status' a a_1 a_2 a_3 a_4)
    (hR st st''' d env c b status')

end Vsa.Sim.Rows

