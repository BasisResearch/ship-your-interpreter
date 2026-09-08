import Vsa.Sim.InductionScaffold
import Vsa.Sim.EvalRecCommon
import Vsa.Sim.EvalReturn
import Vsa.Sim.ExecBlock
import Vsa.Sim.ExecDispatch
import Vsa.Sim.ExecSeqIndexed
import Vsa.Sim.CallEntry
import Vsa.Sim.Code.Interp_run

/-!
# Layer 4 — the M4 CAPSTONE: the mutual-recursor ASSEMBLY (`term_sim_of_cases`)

`Vsa/Sim/InductionScaffold.lean` established and VALIDATED the `@EvalE.rec`
plumbing (nine motives, ~50 minor premises, binder order) against the kernel with
*trivial* (`fun … => True`) motives. This file replaces those with the **REAL**
simulation motives and applies the recursor to assemble the whole mutual
induction, taking the per-constructor case Triples as explicit hypotheses.

## What is real here

* **The nine motives** (`§1`) are the honest simulation projections, using the
  *widened* exit predicates the landed recursive cases actually target:
  - `mEvalE`  = `EvalReturnIH TrivialOwned` (`EvalEntry → EvalReturn`; `.forget` = `EvalIH`),
  - `mExecS`  = `ExecBlock.ExecIH`      (`ExecEntry → ExecExitD`),
  - `mEvalArgs`/`mCall`/`mExecInit`/`mForLoop`/`mForCond`/`mExecStep`/`mExecSeq`
    are the `SegEntry → SegExit` Triples (`InductionScaffold` skeletons), at the
    decoded call/args PCs where those exist (`CallEntry`).
  Every motive ignores the derivation node (its last argument) and is
  ∀-closed over the layout ghosts + budgets, exactly the shape of the landed
  case Triples.

* **`term_sim_of_cases`** (`§2`) is the full nine-motive `@EvalE.rec`
  application. Each of the ~50 minor premises is taken as an EXPLICIT hypothesis
  of the theorem, in the exact ∀-closed shape the recursor demands (constructor
  args, then the sub-derivation IHs in the motive shape, then the motive
  conclusion). The proof is `@EvalE.rec` applied to those hypotheses: it
  type-checks iff the nine real motives compose through every constructor —
  i.e. it is the kernel-checked demonstration that the mutual induction assembles
  with the real simulation motives.

  The hypotheses are exactly the landed case Triples (`evalIntSim`, `evalNegSim`,
  …, `execBlockSim`, `evalCallSim`, …) MODULO their residual bundles: each landed
  theorem discharges its corresponding minor-premise hypothesis (conditionally on
  its named residuals / M6-layout facts / the `Call.closure` crux). The
  case ↔ hypothesis mapping is documented at each premise.

`term_sim` itself (the top-level `BigStep`-level statement) then follows by
instantiating `term_sim_of_cases` at the whole-program entry and discharging the
minor-premise hypotheses from the landed cases once the residual-unification
interface (M6) closes. That last step is future work; what is proved here is that
the induction COMPOSES and pins EXACTLY the per-constructor obligations.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`/`admit`.
-/

namespace Vsa.Sim.TermSimAssembly

open LeanRV64DExecutable Sail
open Register
open Vsa.Machine (MState Config)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim
open Vsa.Sim.Scaffold

local notation "SpecSt" => Vsa.While.St

/-! ## §1. The nine REAL motives

Each `m_R` maps a derivation node (last, ignored argument) to the simulation
`Triple` STATEMENT for that node. `EvalE`/`ExecS` use the widened
`EvalIH`/`ExecIH` (the shape the recursive cases produce and consume — `EvalExit`
upgraded to `EvalExitD` for the presence/survival facts recursive callers need);
the other seven use the `InductionScaffold` `SegEntry → SegExit` skeleton
Triples, at the real decoded PCs where `CallEntry` provides them. -/

/-- `EvalE` motive: the coherent simulation IH (`EvalEntry → EvalReturn`) at the
trivial ownership index `TrivialOwned` — the weakest index every landed
coherent supplier is stated at. `EvalReturn` retains the widened exit
(`EvalExitD`) together with ONE selected map pair for the result, the store, and
its survival, so a child that allocates a closure (a `fn` literal, or a call
returning one) hands its parent a value and store represented at the same maps.
Consumers that need only the widened exit project it with
`EvalReturnIH.forget`. -/
def mEvalE (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt)
    (v : Value) (_h : EvalE st d env e st' v) : Prop :=
  EvalReturnIH TrivialOwned st d env e st' v

/-- `ExecS` motive: the widened statement IH (`ExecEntry → ExecExitD`), i.e.
`ExecBlock.ExecIH`. -/
def mExecS (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (st' : SpecSt)
    (status : Status) (_h : ExecS st d env s st' status) : Prop :=
  ExecIH st d env s st' status

/-! ### Route-indexed statement child interface

The existing `mExecS` is retained while constructor rows are migrated.  The
interface below names the three machine entries a statement child can actually
have: a fresh call, an in-frame dispatch, and a while-arm loop-back. -/

/-- The live-frame state at the while-arm re-entry (`0x80004034`). -/
structure ExecWhileArmReady
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (body : Stmt)
    (bodyStatus : Status)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 ment : Mem)
    (cfg : Config) (liveRA : BitVec 64 := r) : Prop where
  good : GoodState cfg.σ
  tick : cfg.tick < 2
  pc : cfg.σ.regs.get? Register.PC = some (0x80004034#64)
  a0 : cfg.σ.regs.get? Register.x10 = some (StatusCode bodyStatus)
  s0 : cfg.σ.regs.get? Register.x8 = some aStmt
  s1 : cfg.σ.regs.get? Register.x9 = some aInterp
  s2 : cfg.σ.regs.get? Register.x18 = some aRet
  s3 : cfg.σ.regs.get? Register.x19 = some aEnv
  spReg : cfg.σ.regs.get? Register.x2 = some (sp - 176#64)
  parentSp : g Register.x2 = some sp
  ra : cfg.σ.regs.get? Register.x1 = some liveRA
  mem : cfg.σ.mem = ment
  code : Vsa.Sim.Code.Exec_stmtLoaded ment
  code_stack_disjoint : sp.toNat ≤ execStmtEntry ∨ execStmtEnd ≤ SL.lo
  stack_ram : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000
  stack_win : tohostAddr + 16 ≤ SL.lo
  ra_align : r.toNat % 4 = 0
  stmt : StmtRepr ment aStmt.toNat (.whileStmt cnd body)
  env_addr : aEnv = BitVec.ofNat 64 (φf env)
  store : StoreRepr ment N A φf φc st.store
  env_valid : EnvValid st env
  store_survives : ∀ m' : Mem,
    (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → ment[k]? = m'[k]?) →
    StoreRepr m' N A φf φc st.store
  out : OutRepr cfg.σ st
  saved_ra : read64 ment (sp.toNat - 8) = some r.toNat
  saved_s0 : ∃ v, read64 ment (sp.toNat - 16) = some v.toNat ∧
    g Register.x8 = some v
  saved_s1 : ∃ v, read64 ment (sp.toNat - 24) = some v.toNat ∧
    g Register.x9 = some v
  saved_s2 : ∃ v, read64 ment (sp.toNat - 32) = some v.toNat ∧
    g Register.x18 = some v
  saved_s3 : ∃ v, read64 ment (sp.toNat - 40) = some v.toNat ∧
    g Register.x19 = some v
  stack_budget : StackOK SL sp
    ((Stmt.whileStmt cnd body).stackNeed +
      (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088)
  stmt_bodies : Stmt.bodiesBound Vsa.While.perCallBudget (Stmt.whileStmt cnd body) = true
  store_bodies : Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget
  envset_defined : (∃ v, cfg.σ.regs.get? Register.x20 = some v) ∧
    (∃ v, cfg.σ.regs.get? Register.x21 = some v)
  ground : ExecGround ment SL A sp aRet aStmt.toNat (.whileStmt cnd body)
  mem_frame : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) →
    ¬ (A.lo ≤ a ∧ a < A.hi) →
    (aRet.toNat ≤ a ∧ a < aRet.toNat + 24) ∨ ment[a]? = m0[a]?
  mem_extends : MemExtends m0 ment
  frame : ∀ R : Register, AbiPreservedNoise R →
    (R = Register.x8 ∨ R = Register.x9 ∨ R = Register.x18 ∨
      R = Register.x19 ∨ R = Register.x2) ∨ cfg.σ.regs.get? R = g R
  minstret : ∃ v, cfg.σ.regs.get? Register.minstret = some v

/-- While-loop recursive IH at the real in-frame re-entry. -/
def ExecWhileArmIH
    (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (body : Stmt)
    (st' : SpecSt) (status : Status) : Prop :=
  ∀ (bodyStatus : Status),
    bodyStatus = .normal ∨ bodyStatus = .cont →
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 ment : Mem),
    Triple
      (fun cfg => ∃ liveRA,
        ExecWhileArmReady g N A SL φf φc st d env cnd body bodyStatus
          sp r aInterp aStmt aEnv aRet m0 ment cfg (liveRA := liveRA))
      (ExecExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st' status sp r aRet m0)

/-- Product interface for all actual statement-child routes. The while-arm leg
is demanded only for a while statement. -/
structure ExecSRouteIH
    (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt)
    (st' : SpecSt) (status : Status) : Prop where
  fresh : ExecIH st d env s st' status
  dispatch : ExecDispatchIH st d env s st' status
  whileArm : ∀ cnd body, s = .whileStmt cnd body →
    ExecWhileArmIH st d env cnd body st' status

/-- Faithful auxiliary statement motive.  It is kept separate from the legacy
fresh-entry motive while existing leaf rows are migrated. -/
def mExecSRoute (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt)
    (st' : SpecSt) (status : Status) (_h : ExecS st d env s st' status) : Prop :=
  ExecSRouteIH st d env s st' status

/-- Output of the auxiliary context-indexed statement induction. -/
def ExecSRouteFamily : Prop :=
  ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt)
    (st' : SpecSt) (status : Status) (h : ExecS st d env s st' status),
    mExecSRoute st d env s st' status h

/-! ### Context-indexed `for` boundaries

`ExecInit` omits the enclosing `for` node.  `ForLoop` omits its `init` field.
Both machine fragments retain the full `Stmt.forStmt` pointer.  The motives
therefore quantify the missing context instead of erasing it. -/

/-- Machine state after `env_new`, before the optional-init dispatch. -/
structure ExecInitReady
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (outer : Addr)
    (init : Option Stmt) (cnd step : Option Expr) (body : Stmt)
    (sp r aInterp aStmt aOuter aRet : BitVec 64) (m0 ment : Mem)
    (cfg : Config) (liveRA : BitVec 64 := r) : Prop where
  good : GoodState cfg.σ
  tick : cfg.tick < 2
  pc : cfg.σ.regs.get? Register.PC = some (0x8000423c#64)
  s0 : cfg.σ.regs.get? Register.x8 = some aStmt
  s1 : cfg.σ.regs.get? Register.x9 = some aInterp
  s2 : cfg.σ.regs.get? Register.x18 = some aRet
  a0 : cfg.σ.regs.get? Register.x10 = some aOuter
  spReg : cfg.σ.regs.get? Register.x2 = some (sp - 176#64)
  ra : cfg.σ.regs.get? Register.x1 = some liveRA
  mem : cfg.σ.mem = ment
  code : Vsa.Sim.Code.Exec_stmtLoaded ment
  stmt : StmtRepr ment aStmt.toNat (.forStmt init cnd step body)
  outer_addr : φf outer = aOuter.toNat
  store : StoreRepr ment N A φf φc st.store
  env_valid : EnvValid st outer
  /-- The enclosing entry's store stability, retained across initializer setup. -/
  store_survives : ∀ m' : Mem,
    (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → ment[k]? = m'[k]?) →
    StoreRepr m' N A φf φc st.store
  stack_ram : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000
  stack_win : tohostAddr + 16 ≤ SL.lo
  code_stack_disjoint : sp.toNat ≤ execStmtEntry ∨ execStmtEnd ≤ SL.lo
  out : OutRepr cfg.σ st
  saved_ra : read64 ment (sp.toNat - 8) = some r.toNat
  saved_s0 : ∃ v, read64 ment (sp.toNat - 16) = some v.toNat ∧ g Register.x8 = some v
  saved_s1 : ∃ v, read64 ment (sp.toNat - 24) = some v.toNat ∧ g Register.x9 = some v
  saved_s2 : ∃ v, read64 ment (sp.toNat - 32) = some v.toNat ∧ g Register.x18 = some v
  saved_s3 : ∃ v, read64 ment (sp.toNat - 40) = some v.toNat ∧ g Register.x19 = some v
  x20_defined : ∃ v, cfg.σ.regs.get? Register.x20 = some v
  x21_defined : ∃ v, cfg.σ.regs.get? Register.x21 = some v
  stack_budget : StackOK SL sp
    ((Stmt.forStmt init cnd step body).stackNeed +
      (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088)
  stmt_bodies : Stmt.bodiesBound Vsa.While.perCallBudget
    (.forStmt init cnd step body) = true
  store_bodies : Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget
  ground : ExecGround ment SL A sp aRet aStmt.toNat (.forStmt init cnd step body)
  mem_frame : ∀ a, ¬ (SL.lo ≤ a ∧ a < sp.toNat) →
    ¬ (A.lo ≤ a ∧ a < A.hi) →
    (aRet.toNat ≤ a ∧ a < aRet.toNat + 24) ∨ ment[a]? = m0[a]?
  frame : ∀ R, AbiPreservedNoise R →
    (R = Register.x8 ∨ R = Register.x9 ∨ R = Register.x18 ∨
      R = Register.x19 ∨ R = Register.x2) ∨ cfg.σ.regs.get? R = g R
  minstret : ∃ v, cfg.σ.regs.get? Register.minstret = some v
  /-- The parent's stack pointer ghost, restored by the shared epilogue. -/
  parentSp : g Register.x2 = some sp
  /-- The return address the epilogue jumps to is 4-aligned. -/
  ra_align : r.toNat % 4 = 0
  /-- Every byte present at the statement entry is still present. -/
  mem_extends : MemExtends m0 ment

/-- Real loop-head state at `0x8000426c`. -/
structure ForLoopReady
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (outer : Addr)
    (init : Option Stmt) (cnd step : Option Expr) (body : Stmt)
    (sp r aInterp aStmt aOuter aRet : BitVec 64) (m0 ment : Mem)
    (cfg : Config) (liveRA : BitVec 64 := r) : Prop where
  good : GoodState cfg.σ
  tick : cfg.tick < 2
  pc : cfg.σ.regs.get? Register.PC = some (0x8000426c#64)
  s0 : cfg.σ.regs.get? Register.x8 = some aStmt
  s1 : cfg.σ.regs.get? Register.x9 = some aInterp
  s2 : cfg.σ.regs.get? Register.x18 = some aRet
  s3 : cfg.σ.regs.get? Register.x19 = some aOuter
  spReg : cfg.σ.regs.get? Register.x2 = some (sp - 176#64)
  ra : cfg.σ.regs.get? Register.x1 = some liveRA
  mem : cfg.σ.mem = ment
  code : Vsa.Sim.Code.Exec_stmtLoaded ment
  stmt : StmtRepr ment aStmt.toNat (.forStmt init cnd step body)
  outer_addr : φf outer = aOuter.toNat
  store : StoreRepr ment N A φf φc st.store
  env_valid : EnvValid st outer
  /-- Store stability at the selected loop-entry allocation maps. -/
  store_survives : ∀ m' : Mem,
    (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → ment[k]? = m'[k]?) →
    StoreRepr m' N A φf φc st.store
  stack_ram : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000
  stack_win : tohostAddr + 16 ≤ SL.lo
  code_stack_disjoint : sp.toNat ≤ execStmtEntry ∨ execStmtEnd ≤ SL.lo
  out : OutRepr cfg.σ st
  saved_ra : read64 ment (sp.toNat - 8) = some r.toNat
  saved_s0 : ∃ v, read64 ment (sp.toNat - 16) = some v.toNat ∧ g Register.x8 = some v
  saved_s1 : ∃ v, read64 ment (sp.toNat - 24) = some v.toNat ∧ g Register.x9 = some v
  saved_s2 : ∃ v, read64 ment (sp.toNat - 32) = some v.toNat ∧ g Register.x18 = some v
  saved_s3 : ∃ v, read64 ment (sp.toNat - 40) = some v.toNat ∧ g Register.x19 = some v
  x20_defined : ∃ v, cfg.σ.regs.get? Register.x20 = some v
  x21_defined : ∃ v, cfg.σ.regs.get? Register.x21 = some v
  stack_budget : StackOK SL sp
    ((Stmt.forStmt init cnd step body).stackNeed +
      (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088)
  stmt_bodies : Stmt.bodiesBound Vsa.While.perCallBudget
    (.forStmt init cnd step body) = true
  store_bodies : Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget
  ground : ExecGround ment SL A sp aRet aStmt.toNat (.forStmt init cnd step body)
  mem_frame : ∀ a, ¬ (SL.lo ≤ a ∧ a < sp.toNat) →
    ¬ (A.lo ≤ a ∧ a < A.hi) →
    (aRet.toNat ≤ a ∧ a < aRet.toNat + 24) ∨ ment[a]? = m0[a]?
  frame : ∀ R, AbiPreservedNoise R →
    (R = Register.x8 ∨ R = Register.x9 ∨ R = Register.x18 ∨
      R = Register.x19 ∨ R = Register.x2) ∨ cfg.σ.regs.get? R = g R
  minstret : ∃ v, cfg.σ.regs.get? Register.minstret = some v
  /-- The parent's stack pointer ghost, restored by the shared epilogue. -/
  parentSp : g Register.x2 = some sp
  /-- The return address the epilogue jumps to is 4-aligned. -/
  ra_align : r.toNat % 4 = 0
  /-- Every byte present at the statement entry is still present. -/
  mem_extends : MemExtends m0 ment

/-- Initializer continuation at one coherent extension of the entry maps. -/
structure ExecInitExit
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (nf nc : Nat) (st : SpecSt) (d : Nat) (outer : Addr)
    (init : Option Stmt) (cnd step : Option Expr) (body : Stmt)
    (sp r aInterp aStmt aOuter aRet : BitVec 64) (m0 : Mem)
    (cfg : Config) (φf' φc' : Addr → Nat) (liveRA : BitVec 64) : Prop where
  frames : PhiExtends φf φf' nf
  closures : PhiExtends φc φc' nc
  ready : ForLoopReady g N A SL φf' φc' st d outer init cnd step body
    sp r aInterp aStmt aOuter aRet m0 cfg.σ.mem cfg (liveRA := liveRA)

/-- The initializer chooses its post-allocation maps and continuation link. -/
structure ExecInitExitD
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (nf nc : Nat) (st : SpecSt) (d : Nat) (outer : Addr)
    (init : Option Stmt) (cnd step : Option Expr) (body : Stmt)
    (sp r aInterp aStmt aOuter aRet : BitVec 64) (m0 : Mem)
    (cfg : Config) : Prop where
  result : ∃ (φf' φc' : Addr → Nat) (liveRA : BitVec 64),
    ExecInitExit g N A SL φf φc nf nc st d outer init cnd step body
      sp r aInterp aStmt aOuter aRet m0 cfg φf' φc' liveRA

def ExecInitCtxIH
    (st : SpecSt) (d : Nat) (outer : Addr) (init : Option Stmt)
    (st' : SpecSt) : Prop :=
  ∀ (cnd step : Option Expr) (body : Stmt)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r aInterp aStmt aOuter aRet : BitVec 64) (m0 ment : Mem),
    Triple
      (fun cfg => ∃ liveRA,
        ExecInitReady g N A SL φf φc st d outer init cnd step body
          sp r aInterp aStmt aOuter aRet m0 ment cfg (liveRA := liveRA))
      (ExecInitExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st' d outer init cnd step body sp r aInterp aStmt aOuter aRet m0)

def ForLoopCtxIH
    (st : SpecSt) (d : Nat) (outer : Addr) (cnd step : Option Expr)
    (body : Stmt) (st' : SpecSt) (status : Status) : Prop :=
  ∀ (init : Option Stmt)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r aInterp aStmt aOuter aRet : BitVec 64) (m0 ment : Mem),
    Triple
      (fun cfg => ∃ liveRA,
        ForLoopReady g N A SL φf φc st d outer init cnd step body
          sp r aInterp aStmt aOuter aRet m0 ment cfg (liveRA := liveRA))
      (ExecExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st' status sp r aRet m0)

/-- `EvalArgs` motive: the recursive indexed argument ABI.

The prefix quantifiers are essential.  A tail derivation runs at the machine's
current `a6`, not at a fabricated fresh cursor.  The boundary therefore retains
the already-evaluated expression/value prefixes and returns their concatenation
with this derivation's values. -/
def mEvalArgs (st : SpecSt) (d : Nat) (env : Addr) (es : List Expr)
    (st' : SpecSt) (vs : List Value) (_h : EvalArgs st d env es st' vs) : Prop :=
  ∀ (esPrefix : List Expr) (vsPrefix : List Value),
    esPrefix.length = vsPrefix.length →
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft : Nat) (m0 : Mem),
    Triple
      (EvalArgsPrefixEntryI g N A SL φf φc st d env
        esPrefix es vsPrefix dLeft aLeft m0)
      (EvalArgsExitI g N A SL φf φc st.store.frames.size
        st.store.closures.size st' (vsPrefix ++ vs) m0)

/-- `Call` motive: the indexed fval-dispatch ABI.  The entry carries the staged
callee, argument count, and argument vector.  The exit carries the returned
`Value` in the caller's sret buffer. `Call.closure` is where the depth budget
(`d < maxCallDepth`) bites.

**AMENDED (wave 40, ledgers `segentry-no-caller-spill-image` +
`segentry-spillimage-field-blocked-by-frozen-generic-producer`):** the Triple
is guarded by the entry-side spill-image clause
(`Scaffold.EntryImage callDispatchPC g m0` — the table pins the `s7@1016(sp)`
slot, spilled at `0x800031cc` BEFORE this segment): the ret routes restore
`s7` from `1016(sp)`, so for an `(m0, g)`-inconsistent instantiation the exit
`frame` clause is FALSE — the precondition must link them.  Signature-free:
every recursor/`TermCases` reference is fully applied; only the unfolding
producers (`rows/CallRows` native rows, `rows/CallClosureRow`) intro the
hypothesis.  The supplier of an `mCall` IH (the eventual `CallArmSpec`
splice) owns the `0x800031cc` spill and supplies the clause. -/
def mCall (st : SpecSt) (d : Nat) (fv : Value) (vs : List Value)
    (st' : SpecSt) (v : Value) (_h : Call st d fv vs st' v) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft : Nat) (sp sret : BitVec 64) (m0 : Mem),
    Scaffold.EntryImage callDispatchPC g m0 →
    Triple
      (CallEntryI g N A SL φf φc st d fv vs dLeft aLeft sp sret m0)
      (CallExitI g N A SL φf φc st.store.frames.size
        st.store.closures.size st' v sret m0)

/-- `ExecInit` motive.

**Shape (amended 2026-08-31, ledgers `scaffold-motive-independent-pq` then
`scaffold-some-motive-unsatisfiable`).** This motive is now `True`.

History: the motive was first a `SegEntry → SegExit` Triple with INDEPENDENT entry
PC `p` / exit PC `q` (the `.none` obstruction: identity rows give exit = entry, the
motive demanded arbitrary `q`); the first amendment tied both to a single `p`,
fixing `.none` (`LoopScaffoldClose.segIdentity`) but creating the DUAL `.some`
obstruction (`ExecInit.some` mutates the store, `st' ≠ st`, so a same-PC span with a
different store post is unsatisfiable — no store-mutating call returns to the same
abstract PC).  The honest init/cond/step machine work is NOT carried by this motive
anyway: `execForStartSim` (`ExecForStart.lean`) consumes the `ExecInit`/`ForCond`/
`ExecStep` sub-derivations as ignored `_`, and the real per-iteration work flows
through `hArm` + the `ExecForStep` `hstep` oracle.  So this motive is DEAD recursor
plumbing; setting it to `True` makes BOTH the `.none` and `.some` constructors
trivially fillable (`ScaffoldRows.{hInitNone_row,hInitSome_row}` = `trivial`) with
ZERO consumer re-threading (every consumer references it opaquely / as `_`). -/
def mExecInit (st : SpecSt) (d : Nat) (env : Addr) (init : Option Stmt)
    (st' : SpecSt) (_h : ExecInit st d env init st') : Prop :=
  ExecInitCtxIH st d env init st'

/-- `ForLoop` motive.

**Shape (amended, ITEM ZERO / falsity #12, ledger
`forloop-motive-identity-pc-store-mutation`).**  This motive is now `True`,
completing the `mExecInit`/`mForCond`/`mExecStep` scaffold family.

History: the motive was an identity-PC `SegEntry st p → SegExit st' p` span, but
EVERY `ForLoop` constructor mutates the spec state (cond eval / body exec / full
iteration), so a zero-step discharge forces the unchanged entry memory to
represent both `st.store` and `st'.store` (machine-checked by fleet B6,
`zeroStep_forSpan_forces_rerepresentation`) and a stepping discharge is barred by
the code-free `SegEntry` — the DUAL of `scaffold-some-motive-unsatisfiable`.
CONSUMER CENSUS (this amendment): the ONLY consumer of an `mForLoop` IH is
`exec_forStart_row`, which binds it as an IGNORED `_hForIH`; the honest per-
iteration for-loop machine work flows through `execForStartSim`'s
`ExecForStep`/`hForIH` oracles (`ForStartGeom`), exactly as for the other three
`True` scaffold motives.  Setting it to `True` makes all four `ForLoop`
constructors trivially fillable (`ScaffoldRows.hFl*_row`) with zero consumer
re-threading. -/
def mForLoop (st : SpecSt) (d : Nat) (env : Addr) (cnd step : Option Expr)
    (b : Stmt) (st' : SpecSt) (status : Status)
    (_h : ForLoop st d env cnd step b st' status) : Prop :=
  ForLoopCtxIH st d env cnd step b st' status

/-- What the for-loop rows learn from a `ForCond` sub-derivation: the identity
of the state when there is no condition, and the condition's value, truthiness,
derivation, and widened eval IH when there is one. -/
def ForCondIH (st : SpecSt) (d : Nat) (env : Addr) : Option Expr → SpecSt → Prop
  | none, st' => st' = st
  | some c, st' => ∃ v : Value, v.truthy = true ∧ EvalE st d env c st' v ∧ EvalIH st d env c st' v

/-- `ForCond` motive: the condition's eval IH (or the state identity).
Fillable by `ScaffoldRows.{hFcNone_row,hFcSome_row}`. -/
def mForCond (st : SpecSt) (d : Nat) (env : Addr) (cnd : Option Expr)
    (st' : SpecSt) (_h : ForCond st d env cnd st') : Prop :=
  ForCondIH st d env cnd st'

/-- What the for-loop rows learn from an `ExecStep` sub-derivation. -/
def ExecStepIH (st : SpecSt) (d : Nat) (env : Addr) : Option Expr → SpecSt → Prop
  | none, st' => st' = st
  | some e, st' => ∃ v : Value, EvalE st d env e st' v ∧ EvalIH st d env e st' v

/-- `ExecStep` motive: the step's eval IH (or the state identity).
Fillable by `ScaffoldRows.{hEsNone_row,hEsSome_row}`. -/
def mExecStep (st : SpecSt) (d : Nat) (env : Addr) (step : Option Expr)
    (st' : SpecSt) (_h : ExecStep st d env step st') : Prop :=
  ExecStepIH st d env step st'

/-! ### The seq-loop span table + ground (ITEM ZERO / falsity #12, shape 3)

`mExecSeq`'s `∀ p q` is GENUINELY needed by consumers — the statement loop is
compiled at (at least) THREE inlined copies, and landed consumers instantiate
the motive at all three pairs:

* `interp_run`'s top-level statement loop, `0x8000448c → 0x80004514`
  (`EntryHalts.hPrologue_of` / `TermEntry` / `EntrySeams`);
* the closure-body loop inside `eval_expr`'s `EX_CALL` arm,
  `callBodyLoopPC = 0x80003354 → callBodyRetPC = 0x80003378`
  (`rows/CallClosureRow`, the crux);
* the `block` arm's loop inside `exec_stmt`,
  `execSeqLoopPC = 0x800041a4 → execSeqContPC = 0x8000409c`
  (`ExecDispatchRows.BlockGeom`'s `hArm`/`hEpi` seam).

So the B6 "pin both PCs" cure is unavailable; instead the motive gets the
`mCall`/`EntryImage` wave-40 precedent: an entry-side GUARD, table-driven.
`seqLoopImage` maps exactly the legitimate loop-copy PC pairs to the landed
code-image predicate covering that copy's bytes; `SeqSpanGround p q m0`
(named-field, R6/R7) says the pair is TABLED and its image is loaded in `m0`.
Untabled pairs make the motive VACUOUS (`tabled` is unsatisfiable), so a
supplier of `hSeqNil`/`hSeqCons*` owes only the three real loop copies WITH
their code bytes in hand — dissolving fleet B6's code-free-`SegEntry`
obstruction (`seq-motive-independent-pq-no-code`).  Signature-free for every
recursor/`TermCases` reference (all fully applied); only the unfolding
producers/consumers intro/supply the hypothesis. -/

/-- The seq-loop copy table: legitimate `(entryPC, exitPC)` statement-loop
copies → the landed code-image predicate pinning that copy's bytes.  Extending
the proof to a new loop copy = one new table line. -/
def seqLoopImage : Nat → Nat → Option (Mem → Prop)
  | 0x8000448c, 0x80004514 => some Vsa.Sim.Code.Interp_runLoaded
  | 0x80003354, 0x80003378 => some Vsa.Sim.Code.Eval_exprLoaded
  | 0x800041a4, 0x8000409c => some Vsa.Sim.Code.Exec_stmtLoaded
  | _, _ => none

/-- The entry-side ground for a seq-loop span `(p, q)`: the pair is a tabled
loop copy and its code image is loaded in the pre-memory `m0`. -/
structure SeqSpanGround (p q : Nat) (m0 : Mem) : Prop where
  /-- `(p, q)` is one of the binary's statement-loop copies. -/
  tabled : (seqLoopImage p q).isSome
  /-- The copy's code image is loaded in `m0`. -/
  image : ∀ P : Mem → Prop, seqLoopImage p q = some P → P m0

/-- Build the ground from a table hit + the image fact. -/
theorem seqSpanGround_of {p q : Nat} {m0 : Mem} {P : Mem → Prop}
    (h : seqLoopImage p q = some P) (hP : P m0) : SeqSpanGround p q m0 :=
  ⟨by rw [h]; rfl, fun _ h' => by rw [h] at h'; exact (Option.some.inj h') ▸ hP⟩

/-- The seq-loop simulation IH, NAMED (the `mExecSeq` motive body): the guarded
`SegEntry → SegExit` Triple family from spec state `st` at depth `d` to `st'`,
over every tabled loop-copy span.  Named separately so shape-2 consumers
(`BlockResid`) can thread the recursor's seq sub-IH as a hypothesis without
mentioning a derivation node. -/
def SeqLegacyIH (st : SpecSt) (d : Nat) (st' : SpecSt) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft : Nat) (p q : Nat) (m0 : Mem),
    SeqSpanGround p q m0 →
    Triple
      (SegEntry g N A SL φf φc st d dLeft aLeft p m0)
      (SegExit g N A SL φf φc st.store.frames.size st.store.closures.size st' q m0)

/-- Copy-indexed sequence simulation. Unlike the legacy segment family, this
retains the scope, remaining list, final status, cursor, and return slot. -/
def SeqIndexedIH (st : SpecSt) (d : Nat) (env : Addr) (ss : List Stmt)
    (st' : SpecSt) (status : Status) : Prop :=
  ∀ (copy : ExecSeqCopy)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp aRet : BitVec 64) (m0 : Mem),
    copy.Supports status →
    Triple
      (ExecSeqEntryI copy g N A SL φf φc st d env ss sp aRet m0)
      (ExecSeqExitI copy g N A SL φf φc st.store.frames.size
        st.store.closures.size st' status sp aRet m0)

/-- Faithful copy-indexed sequence contract.  The former legacy half quantified
an arbitrary segment state and admitted an empty suffix at a nonempty loop head;
it is not part of the semantic induction boundary. -/
def SeqSegIH (st : SpecSt) (d : Nat) (env : Addr) (ss : List Stmt)
    (st' : SpecSt) (status : Status) : Prop :=
  SeqIndexedIH st d env ss st' status

/-- `ExecSeq` motive at the exact physical loop copy, scope, suffix, status ABI,
and return slot. -/
def mExecSeq (st : SpecSt) (d : Nat) (env : Addr) (ss : List Stmt)
    (st' : SpecSt) (status : Status) (_h : ExecSeq st d env ss st' status) : Prop :=
  SeqSegIH st d env ss st' status

/-! ## §2. The assembled mutual induction — `term_sim_of_cases`

The full nine-motive `@EvalE.rec` application with the REAL simulation motives.
Each of the 50 minor premises is an explicit hypothesis, in the exact ∀-closed
shape the recursor demands: the constructor's arguments (including its
sub-derivation proofs `a`, `a_1`, …), then the sub-derivation induction
hypotheses in the motive shape (`mEvalE …`/`mExecS …`/…), then the motive
conclusion for this node (with the reconstructed derivation term). The body is
the recursor applied to these hypotheses.

This TYPE-CHECKS iff the nine real motives compose through every constructor of
the mutual family — it is the kernel-checked assembly of the whole simulation
induction with real motives (not the `True`-motive plumbing check of
`InductionScaffold`). It concludes `mEvalE … t = EvalReturnIH TrivialOwned …`, the coherent
`EvalE`-simulation Triple, for an arbitrary `EvalE` derivation.

Each hypothesis `h<Ctor>` is discharged — conditionally on that case's named
residuals / M6-layout facts / the `Call.closure` crux — by the correspondingly
named landed case theorem. The case ↔ hypothesis mapping (module doc):

* EvalE: hInt←`evalIntSim`, hStr←`evalStrSim`, hBool←`evalBoolSim`,
  hNull←`evalNullSim`, hVar←`evalVarSim`, hNeg←`evalNegSim`, hNot←`evalNotSim`,
  hBinary←`evalAddSim`/`evalSubSim`/`evalLtSim`/… (per `op`; le/gt/eq/ne/mul/
  div/mod mechanical-pending), hOrTrue←`evalOrTrueSim`, hOrFalse←`evalOrFalseSim`,
  hAndFalse←`evalAndSim`, hAndTrue←`evalAndTrueSim`, hCall←`evalCallSim`,
  hFn←`evalFnSim`; hAssign is a native-store case (pending env_define contract).
* EvalArgs: hArgsNil←`evalArgsNil`, hArgsCons←`evalArgsCons`.
* Call: hCallAssertOk←`callAssertOk`; hCallClosure (crux, env_define-blocked),
  hCallPrint/hCallPrintln (native output-append, template ready) are the open
  minor premises taken as hypotheses.
* ExecS: hSExpr←`execExprSim`, hSVarInit←`envDefineTail_run` (rows/Field_hSVarInitClosed),
  hSVarNull←`varNull_run` (rows/Field_hSVarNullClosed), hSBlock←`execBlockSim`,
  hSIfTrue←`execIfTrueSim`, hSIfFalse←`execIfFalseSim`, hSIfNone←`execIfNoneSim`,
  hSWhile*←`execWhileSim`, hSForStart←`execForStartSim`, hSRet←`execRetSim`,
  hSRetNull←`retNull_run` (rows/Field_hSRetNullClosed), hSBrk←`execBrkSim`,
  hSCont←`execContSim`.
* ExecSeq: hSeqNil←`execSeqNil`, hSeqConsNormal/hSeqConsAbrupt←`execSeqLoop`
  (the per-iteration rule that consumes these).
* ForLoop: hFl*←`execForLoopBody`; ForCond/ExecStep/ExecInit (hFc*/hEs*/hInit*)
  are the loop-scaffold sub-relations (`SegEntry → SegExit`), taken as
  hypotheses pending their per-relation machine proofs.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`/`admit`.  -/

theorem term_sim_of_cases
    (hInt :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (n : Int), mEvalE st d env (Expr.int n) st (Value.int n) (EvalE.int st d env n))
    (hStr :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : String), mEvalE st d env (Expr.str s) st (Value.str s) (EvalE.str st d env s))
    (hBool :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (b : Bool), mEvalE st d env (Expr.bool b) st (Value.bool b) (EvalE.bool st d env b))
    (hNull :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mEvalE st d env Expr.null st Value.null (EvalE.null st d env))
    (hVar :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (v : Value) (a : st.store.get? env x = some v), mEvalE st d env (Expr.var x) st v (EvalE.var st d env x v a))
    (hAssign :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr) (st' : SpecSt) (v : Value) (store'' : Store) (a : EvalE st d env e st' v) (a_1 : st'.store.set? env x v = some store''), mEvalE st d env e st' v a → mEvalE st d env (Expr.assign x e) { store := store'', out := st'.out } v (EvalE.assign st d env x e st' v store'' a a_1))
    (hBinary :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr) (st' st'' : SpecSt) (lv rv v : Value) (a : EvalE st d env l st' lv) (a_1 : EvalE st' d env r st'' rv) (a_2 : binOpSem st''.store op lv rv = some v), mEvalE st d env l st' lv a → mEvalE st' d env r st'' rv a_1 → mEvalE st d env (Expr.binary op l r) st'' v (EvalE.binary st d env op l r st' st'' lv rv v a a_1 a_2))
    (hOrTrue :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' : SpecSt) (lv : Value) (a : EvalE st d env l st' lv) (a_1 : lv.truthy = true), mEvalE st d env l st' lv a → mEvalE st d env (Expr.logical LogOp.or l r) st' (Value.bool true) (EvalE.orTrue st d env l r st' lv a a_1))
    (hOrFalse :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' st'' : SpecSt) (lv rv : Value) (a : EvalE st d env l st' lv) (a_1 : lv.truthy = false) (a_2 : EvalE st' d env r st'' rv), mEvalE st d env l st' lv a → mEvalE st' d env r st'' rv a_2 → mEvalE st d env (Expr.logical LogOp.or l r) st'' (Value.bool rv.truthy) (EvalE.orFalse st d env l r st' st'' lv rv a a_1 a_2))
    (hAndFalse :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' : SpecSt) (lv : Value) (a : EvalE st d env l st' lv) (a_1 : lv.truthy = false), mEvalE st d env l st' lv a → mEvalE st d env (Expr.logical LogOp.and l r) st' (Value.bool false) (EvalE.andFalse st d env l r st' lv a a_1))
    (hAndTrue :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' st'' : SpecSt) (lv rv : Value) (a : EvalE st d env l st' lv) (a_1 : lv.truthy = true) (a_2 : EvalE st' d env r st'' rv), mEvalE st d env l st' lv a → mEvalE st' d env r st'' rv a_2 → mEvalE st d env (Expr.logical LogOp.and l r) st'' (Value.bool rv.truthy) (EvalE.andTrue st d env l r st' st'' lv rv a a_1 a_2))
    (hNeg :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (n : Int) (a : EvalE st d env e st' (Value.int n)), mEvalE st d env e st' (Value.int n) a → mEvalE st d env (Expr.unary UnOp.neg e) st' (Value.int (wrap64 (-n))) (EvalE.neg st d env e st' n a))
    (hNot :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value) (a : EvalE st d env e st' v), mEvalE st d env e st' v a → mEvalE st d env (Expr.unary UnOp.not e) st' (Value.bool !v.truthy) (EvalE.not st d env e st' v a))
    (hCall :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (f : Expr) (args : List Expr) (st' st'' st''' : SpecSt) (fv : Value) (vs : List Value) (v : Value) (a : EvalE st d env f st' fv) (a_1 : args.length ≤ maxArgs) (a_2 : EvalArgs st' d env args st'' vs) (a_3 : Call st'' d fv vs st''' v), mEvalE st d env f st' fv a → mEvalArgs st' d env args st'' vs a_2 → mCall st'' d fv vs st''' v a_3 → mEvalE st d env (f.call args) st''' v (EvalE.call st d env f args st' st'' st''' fv vs v a a_1 a_2 a_3))
    (hFn :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (name : Option String) (params : List String) (body : List Stmt) (store' : Store) (a : Addr) (a_1 : st.store.allocClosure { env := env, name := name, params := params, body := body } = (store', a)), mEvalE st d env (Expr.fn name params body) { store := store', out := st.out } (Value.closure a) (EvalE.fn st d env name params body store' a a_1))
    (hArgsNil :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mEvalArgs st d env [] st [] (EvalArgs.nil st d env))
    (hArgsCons :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (es : List Expr) (st' st'' : SpecSt) (v : Value) (vs : List Value) (a : EvalE st d env e st' v) (a_1 : EvalArgs st' d env es st'' vs), mEvalE st d env e st' v a → mEvalArgs st' d env es st'' vs a_1 → mEvalArgs st d env (e :: es) st'' (v :: vs) (EvalArgs.cons st d env e es st' st'' v vs a a_1))
    (hCallClosure :
      ∀ (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value) (store' : Store) (frame : Addr) (st' : SpecSt) (status : Status) (v : Value) (a_1 : st.store.closures[a]? = some cd) (a_2 : vs.length = cd.params.length) (a_3 : d < maxCallDepth) (a_4 : st.store.allocFrame (some cd.env) = (store', frame)) (a_5 : ExecSeq { store := List.foldl (fun s x => match x with | (x, v) => s.define frame x v) store' (cd.params.zip vs), out := st.out } (d + 1) frame cd.body st' status) (a_6 : status = Status.normal ∧ v = Value.null ∨ status = Status.ret v), mExecSeq { store := List.foldl (fun s x => match x with | (x, v) => s.define frame x v) store' (cd.params.zip vs), out := st.out } (d + 1) frame cd.body st' status a_5 → mCall st d (Value.closure a) vs st' v (Call.closure st d a cd vs store' frame st' status v a_1 a_2 a_3 a_4 a_5 a_6))
    (hCallPrint :
      ∀ (st : SpecSt) (d : Nat) (vs : List Value), mCall st d (Value.native NativeFn.print) vs { store := st.store, out := st.out +++ printArgs st.store vs } Value.null (Call.print st d vs))
    (hCallPrintln :
      ∀ (st : SpecSt) (d : Nat) (vs : List Value), mCall st d (Value.native NativeFn.println) vs { store := st.store, out := st.out +++ printArgs st.store vs +++ "\n" } Value.null (Call.println st d vs))
    (hCallAssertOk :
      ∀ (st : SpecSt) (d : Nat) (vs : List Value) (v m : Value) (a : vs = [v] ∨ vs = [v, m]) (a_1 : v.truthy = true), mCall st d (Value.native NativeFn.assert) vs st Value.null (Call.assertOk st d vs v m a a_1))
    (hSExpr :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value) (a : EvalE st d env e st' v), mEvalE st d env e st' v a → mExecS st d env (Stmt.expr e) st' Status.normal (ExecS.expr st d env e st' v a))
    (hSVarInit :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr) (st' : SpecSt) (v : Value) (a : EvalE st d env e st' v), mEvalE st d env e st' v a → mExecS st d env (Stmt.varDecl x (some e)) { store := st'.store.define env x v, out := st'.out } Status.normal (ExecS.varInit st d env x e st' v a))
    (hSVarNull :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String), mExecS st d env (Stmt.varDecl x none) { store := st.store.define env x Value.null, out := st.out } Status.normal (ExecS.varNull st d env x))
    (hSBlock :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (ss : List Stmt) (store' : Store) (inner : Addr) (st' : SpecSt) (status : Status) (a : st.store.allocFrame (some env) = (store', inner)) (a_1 : ExecSeq { store := store', out := st.out } d inner ss st' status), mExecSeq { store := store', out := st.out } d inner ss st' status a_1 → mExecS st d env (Stmt.block ss) st' status (ExecS.block st d env ss store' inner st' status a a_1))
    (hSIfTrue :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (t : Stmt) (e : Option Stmt) (st' st'' : SpecSt) (v : Value) (status : Status) (a : EvalE st d env c st' v) (a_1 : v.truthy = true) (a_2 : ExecS st' d env t st'' status), mEvalE st d env c st' v a → mExecS st' d env t st'' status a_2 → mExecS st d env (Stmt.ifStmt c t e) st'' status (ExecS.ifTrue st d env c t e st' st'' v status a a_1 a_2))
    (hSIfFalse :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (t e : Stmt) (st' st'' : SpecSt) (v : Value) (status : Status) (a : EvalE st d env c st' v) (a_1 : v.truthy = false) (a_2 : ExecS st' d env e st'' status), mEvalE st d env c st' v a → mExecS st' d env e st'' status a_2 → mExecS st d env (Stmt.ifStmt c t (some e)) st'' status (ExecS.ifFalse st d env c t e st' st'' v status a a_1 a_2))
    (hSIfNone :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (t : Stmt) (st' : SpecSt) (v : Value) (a : EvalE st d env c st' v) (a_1 : v.truthy = false), mEvalE st d env c st' v a → mExecS st d env (Stmt.ifStmt c t none) st' Status.normal (ExecS.ifNone st d env c t st' v a a_1))
    (hSWhileFalse :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (b : Stmt) (st' : SpecSt) (v : Value) (a : EvalE st d env c st' v) (a_1 : v.truthy = false), mEvalE st d env c st' v a → mExecS st d env (Stmt.whileStmt c b) st' Status.normal (ExecS.whileFalse st d env c b st' v a a_1))
    (hSWhileBreak :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (b : Stmt) (st' st'' : SpecSt) (v : Value) (a : EvalE st d env c st' v) (a_1 : v.truthy = true) (a_2 : ExecS st' d env b st'' Status.brk), mEvalE st d env c st' v a → mExecS st' d env b st'' Status.brk a_2 → mExecS st d env (Stmt.whileStmt c b) st'' Status.normal (ExecS.whileBreak st d env c b st' st'' v a a_1 a_2))
    (hSWhileRet :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (b : Stmt) (st' st'' : SpecSt) (v rv : Value) (a : EvalE st d env c st' v) (a_1 : v.truthy = true) (a_2 : ExecS st' d env b st'' (Status.ret rv)), mEvalE st d env c st' v a → mExecS st' d env b st'' (Status.ret rv) a_2 → mExecS st d env (Stmt.whileStmt c b) st'' (Status.ret rv) (ExecS.whileRet st d env c b st' st'' v rv a a_1 a_2))
    (hSWhileLoop :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (b : Stmt) (st' st'' st''' : SpecSt) (v : Value) (status status' : Status) (a : EvalE st d env c st' v) (a_1 : v.truthy = true) (a_2 : ExecS st' d env b st'' status) (a_3 : status = Status.normal ∨ status = Status.cont) (a_4 : ExecS st'' d env (Stmt.whileStmt c b) st''' status'), mEvalE st d env c st' v a → mExecS st' d env b st'' status a_2 → mExecS st'' d env (Stmt.whileStmt c b) st''' status' a_4 → mExecS st d env (Stmt.whileStmt c b) st''' status' (ExecS.whileLoop st d env c b st' st'' st''' v status status' a a_1 a_2 a_3 a_4))
    (hSForStart :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (init : Option Stmt) (cnd step : Option Expr) (b : Stmt) (store' : Store) (outer : Addr) (st' st'' : SpecSt) (status : Status) (a : st.store.allocFrame (some env) = (store', outer)) (a_1 : ExecInit { store := store', out := st.out } d outer init st') (a_2 : ForLoop st' d outer cnd step b st'' status), mExecInit { store := store', out := st.out } d outer init st' a_1 → mForLoop st' d outer cnd step b st'' status a_2 → mExecS st d env (Stmt.forStmt init cnd step b) st'' status (ExecS.forStart st d env init cnd step b store' outer st' st'' status a a_1 a_2))
    (hSRet :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value) (a : EvalE st d env e st' v), mEvalE st d env e st' v a → mExecS st d env (Stmt.ret (some e)) st' (Status.ret v) (ExecS.ret st d env e st' v a))
    (hSRetNull :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mExecS st d env (Stmt.ret none) st (Status.ret Value.null) (ExecS.retNull st d env))
    (hSBrk :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mExecS st d env Stmt.brk st Status.brk (ExecS.brk st d env))
    (hSCont :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mExecS st d env Stmt.cont st Status.cont (ExecS.cont st d env))
    (hInitNone :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mExecInit st d env none st (ExecInit.none st d env))
    (hInitSome :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (st' : SpecSt) (status : Status) (a : ExecS st d env s st' status), mExecS st d env s st' status a → mExecInit st d env (some s) st' (ExecInit.some st d env s st' status a))
    (hFlCondFalse :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (step : Option Expr) (b : Stmt) (st' : SpecSt) (v : Value) (a : EvalE st d env c st' v) (a_1 : v.truthy = false), mEvalE st d env c st' v a → mForLoop st d env (some c) step b st' Status.normal (ForLoop.condFalse st d env c step b st' v a a_1))
    (hFlBodyBreak :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd step : Option Expr) (b : Stmt) (st' st'' : SpecSt) (a : ForCond st d env cnd st') (a_1 : ExecS st' d env b st'' Status.brk), mForCond st d env cnd st' a → mExecS st' d env b st'' Status.brk a_1 → mForLoop st d env cnd step b st'' Status.normal (ForLoop.bodyBreak st d env cnd step b st' st'' a a_1))
    (hFlBodyRet :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd step : Option Expr) (b : Stmt) (st' st'' : SpecSt) (rv : Value) (a : ForCond st d env cnd st') (a_1 : ExecS st' d env b st'' (Status.ret rv)), mForCond st d env cnd st' a → mExecS st' d env b st'' (Status.ret rv) a_1 → mForLoop st d env cnd step b st'' (Status.ret rv) (ForLoop.bodyRet st d env cnd step b st' st'' rv a a_1))
    (hFlLoop :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd step : Option Expr) (b : Stmt) (st' st'' st''' st'''' : SpecSt) (status status' : Status) (a : ForCond st d env cnd st') (a_1 : ExecS st' d env b st'' status) (a_2 : status = Status.normal ∨ status = Status.cont) (a_3 : ExecStep st'' d env step st''') (a_4 : ForLoop st''' d env cnd step b st'''' status'), mForCond st d env cnd st' a → mExecS st' d env b st'' status a_1 → mExecStep st'' d env step st''' a_3 → mForLoop st''' d env cnd step b st'''' status' a_4 → mForLoop st d env cnd step b st'''' status' (ForLoop.loop st d env cnd step b st' st'' st''' st'''' status status' a a_1 a_2 a_3 a_4))
    (hFcNone :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mForCond st d env none st (ForCond.none st d env))
    (hFcSome :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (st' : SpecSt) (v : Value) (a : EvalE st d env c st' v) (a_1 : v.truthy = true), mEvalE st d env c st' v a → mForCond st d env (some c) st' (ForCond.some st d env c st' v a a_1))
    (hEsNone :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mExecStep st d env none st (ExecStep.none st d env))
    (hEsSome :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value) (a : EvalE st d env e st' v), mEvalE st d env e st' v a → mExecStep st d env (some e) st' (ExecStep.some st d env e st' v a))
    (hSeqNil :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mExecSeq st d env [] st Status.normal (ExecSeq.nil st d env))
    (hSeqConsNormal :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) (st' st'' : SpecSt) (status : Status) (a : ExecS st d env s st' Status.normal) (a_1 : ExecSeq st' d env ss st'' status), mExecS st d env s st' Status.normal a → mExecSeq st' d env ss st'' status a_1 → mExecSeq st d env (s :: ss) st'' status (ExecSeq.consNormal st d env s ss st' st'' status a a_1))
    (hSeqConsAbrupt :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) (st' : SpecSt) (status : Status) (a : ExecS st d env s st' status) (a_1 : status ≠ Status.normal), mExecS st d env s st' status a → mExecSeq st d env (s :: ss) st' status (ExecSeq.consAbrupt st d env s ss st' status a a_1))
    {st : SpecSt} {d : Nat} {env : Addr} {e : Expr} {st' : SpecSt} {v : Value}
    (t : EvalE st d env e st' v) : mEvalE st d env e st' v t :=
  @EvalE.rec mEvalE mEvalArgs mCall mExecS mExecInit mForLoop mForCond mExecStep
    mExecSeq
    hInt hStr hBool hNull hVar hAssign hBinary hOrTrue hOrFalse hAndFalse hAndTrue hNeg
    hNot hCall hFn hArgsNil hArgsCons hCallClosure hCallPrint hCallPrintln hCallAssertOk
    hSExpr hSVarInit hSVarNull hSBlock hSIfTrue hSIfFalse hSIfNone hSWhileFalse
    hSWhileBreak hSWhileRet hSWhileLoop hSForStart hSRet hSRetNull hSBrk hSCont hInitNone
    hInitSome hFlCondFalse hFlBodyBreak hFlBodyRet hFlLoop hFcNone hFcSome hEsNone hEsSome
    hSeqNil hSeqConsNormal hSeqConsAbrupt
    st d env e st' v t

end Vsa.Sim.TermSimAssembly
