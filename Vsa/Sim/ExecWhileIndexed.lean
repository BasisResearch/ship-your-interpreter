import Vsa.Sim.ExecWhile2
import Vsa.Sim.InterpEntry
import Vsa.Sim.TermSimAssembly
import Vsa.Sim.TripleCat

namespace Vsa.Sim

open LeanRV64DExecutable Sail
open Register
open Vsa.Machine (Config)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.TermSimAssembly

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

local notation "SpecSt" => Vsa.While.St

/-- Any append-only store extension preserves an already-valid environment. -/
theorem EnvValid.afterStoreLe {st st' : SpecSt} {env : Addr}
    (henv : EnvValid st env) (hle : StoreLe st.store st'.store) :
    EnvValid st' env :=
  henv.mono hle.1

/-- The address returned by `allocFrame` is valid in the resulting store. -/
theorem EnvValid.allocatedFrame {st : SpecSt} {store' : Store}
    {parent : Option Addr} {frame : Addr}
    (halloc : st.store.allocFrame parent = (store', frame)) :
    EnvValid { st with store := store' } frame := by
  have hs : (st.store.allocFrame parent).1 = store' := by
    simpa using congrArg Prod.fst halloc
  have hf : (st.store.allocFrame parent).2 = frame := by
    simpa using congrArg Prod.snd halloc
  change frame < store'.frames.size
  rw [← hs, ← hf]
  simp [Store.allocFrame]

/-- Expression evaluation cannot invalidate the current environment because
the semantic store is append-only. -/
theorem EnvValid.afterEvalE {st st' : SpecSt} {d : Nat} {env : Addr}
    {e : Expr} {v : Value} (henv : EnvValid st env)
    (h : EvalE st d env e st' v) : EnvValid st' env :=
  henv.afterStoreLe (Vsa.While.evalE_store_mono h)

/-- Statement execution cannot invalidate the current environment. -/
theorem EnvValid.afterExecS {st st' : SpecSt} {d : Nat} {env : Addr}
    {s : Stmt} {status : Status} (henv : EnvValid st env)
    (h : ExecS st d env s st' status) : EnvValid st' env :=
  henv.afterStoreLe (Vsa.While.execS_store_mono h)

theorem EnvValid.afterForCond {st st' : SpecSt} {d : Nat} {env : Addr}
    {cnd : Option Expr} (henv : EnvValid st env)
    (h : ForCond st d env cnd st') : EnvValid st' env :=
  henv.afterStoreLe (Vsa.While.forCond_store_mono h)

theorem EnvValid.afterExecStep {st st' : SpecSt} {d : Nat} {env : Addr}
    {step : Option Expr} (henv : EnvValid st env)
    (h : ExecStep st d env step st') : EnvValid st' env :=
  henv.afterStoreLe (Vsa.While.execStep_store_mono h)

/-- Status-indexed result of one physical `while` iteration.  A continuing
body lands at the live frame's `0x80004034` status check.  It does not fabricate
a fresh `exec_stmt` entry. -/
def ExecWhileStepPostI
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st stMid stFin : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (body : Stmt)
    (bodyStatus loopStatus : Status)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (cfg : Config) : Prop :=
  ((bodyStatus = .normal ∨ bodyStatus = .cont) ∧
    ∃ (φf' φc' : Addr → Nat) (ment : Mem) (liveRA : BitVec 64),
      -- Composition starts at the original entry maps.  A body allocation may
      -- choose fresh images beyond the original prefix, so agreement cannot be
      -- demanded through the larger post-state size.
      PhiExtends φf φf' st.store.frames.size ∧
      PhiExtends φc φc' st.store.closures.size ∧
      ExecWhileArmReady g N A SL φf' φc' stMid d env cnd body bodyStatus
        sp r aInterp aStmt aEnv aRet m0 ment cfg (liveRA := liveRA)) ∨
  (¬ (bodyStatus = .normal ∨ bodyStatus = .cont) ∧
    ExecExit g N A SL φf φc st.store.frames.size st.store.closures.size
      stMid loopStatus sp r aRet m0 cfg)

/-- One exact physical `while` iteration.  Its recursive boundary is the
status-indexed in-frame state above. -/
def ExecWhileStepI
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st stMid stFin : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (body : Stmt)
    (bodyStatus loopStatus : Status)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) : Prop :=
  Triple
    (ExecEntry g N A SL φf φc st d env (.whileStmt cnd body)
      sp r aInterp aStmt aEnv aRet m0)
    (ExecWhileStepPostI g N A SL φf φc st stMid stFin d env cnd body
      bodyStatus loopStatus sp r aInterp aStmt aEnv aRet m0)

/-- Static identity carried across the condition IH.  `EvalEntry`/`EvalExitD`
alone intentionally abstract over the caller frame; this token retains the
exact enclosing while frame and its memory geometry without restating either
finite-machine target. -/
structure ExecWhileCondCarrier
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (body : Stmt)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (gCond : (R : Register) → Option (RegisterType R))
    (aCond : BitVec 64) (mCond : Mem) : Prop where
  s0 : gCond Register.x8 = some aStmt
  s1 : gCond Register.x9 = some aInterp
  s2 : gCond Register.x18 = some aRet
  s3 : gCond Register.x19 = some aEnv
  spReg : gCond Register.x2 = some (sp - 176#64)
  code : Vsa.Sim.Code.Exec_stmtLoaded mCond
  code_stack_disjoint : sp.toNat ≤ execStmtEntry ∨ execStmtEnd ≤ SL.lo
  stack_ram : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000
  stack_win : tohostAddr + 16 ≤ SL.lo
  ra_align : r.toNat % 4 = 0
  stmt : StmtRepr mCond aStmt.toNat (.whileStmt cnd body)
  env_addr : aEnv = BitVec.ofNat 64 (φf env)
  store : StoreRepr mCond N A φf φc st.store
  env_valid : EnvValid st env
  store_survives : ∀ m' : Mem,
    (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → mCond[k]? = m'[k]?) →
    StoreRepr m' N A φf φc st.store
  saved_ra : read64 mCond (sp.toNat - 8) = some r.toNat
  saved_s0 : ∃ v, read64 mCond (sp.toNat - 16) = some v.toNat ∧
    g Register.x8 = some v
  saved_s1 : ∃ v, read64 mCond (sp.toNat - 24) = some v.toNat ∧
    g Register.x9 = some v
  saved_s2 : ∃ v, read64 mCond (sp.toNat - 32) = some v.toNat ∧
    g Register.x18 = some v
  saved_s3 : ∃ v, read64 mCond (sp.toNat - 40) = some v.toNat ∧
    g Register.x19 = some v
  stack_budget : StackOK SL sp
    ((Stmt.whileStmt cnd body).stackNeed +
      (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088)
  stmt_bodies : Stmt.bodiesBound Vsa.While.perCallBudget
    (.whileStmt cnd body) = true
  store_bodies : Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget
  envset_defined : (∃ v, gCond Register.x20 = some v) ∧
    (∃ v, gCond Register.x21 = some v)
  ground : ExecGround mCond SL A sp aRet aStmt.toNat (.whileStmt cnd body)
  mem_frame : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) →
    mCond[a]? = m0[a]?
  frame : ∀ R : Register, AbiPreservedNoise R →
    (R = Register.x8 ∨ R = Register.x9 ∨ R = Register.x18 ∨
      R = Register.x19 ∨ R = Register.x2) ∨ gCond R = g R

/-- Exact enclosing-frame identity retained across the body IH.  The child
`ExecEntry` is intentionally not recoverable from `ExecExitD`; this carrier
keeps only the static parent facts needed by the status routes. -/
structure ExecWhileBodyCarrier
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (body : Stmt)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (gBody : (R : Register) → Option (RegisterType R))
    (aBody : BitVec 64) (mBody : Mem) : Prop where
  s0 : gBody Register.x8 = some aStmt
  s1 : gBody Register.x9 = some aInterp
  s2 : gBody Register.x18 = some aRet
  s3 : gBody Register.x19 = some aEnv
  spReg : gBody Register.x2 = some (sp - 176#64)
  code : Vsa.Sim.Code.Exec_stmtLoaded mBody
  code_stack_disjoint : sp.toNat ≤ execStmtEntry ∨ execStmtEnd ≤ SL.lo
  stack_ram : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000
  stack_win : tohostAddr + 16 ≤ SL.lo
  ra_align : r.toNat % 4 = 0
  parent_stmt : StmtRepr mBody aStmt.toNat (.whileStmt cnd body)
  body_stmt : StmtRepr mBody aBody.toNat body
  env_addr : aEnv = BitVec.ofNat 64 (φf env)
  store : StoreRepr mBody N A φf φc st.store
  env_valid : EnvValid st env
  store_survives : ∀ m' : Mem,
    (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → mBody[k]? = m'[k]?) →
    StoreRepr m' N A φf φc st.store
  saved_ra : read64 mBody (sp.toNat - 8) = some r.toNat
  saved_s0 : ∃ v, read64 mBody (sp.toNat - 16) = some v.toNat ∧
    g Register.x8 = some v
  saved_s1 : ∃ v, read64 mBody (sp.toNat - 24) = some v.toNat ∧
    g Register.x9 = some v
  saved_s2 : ∃ v, read64 mBody (sp.toNat - 32) = some v.toNat ∧
    g Register.x18 = some v
  saved_s3 : ∃ v, read64 mBody (sp.toNat - 40) = some v.toNat ∧
    g Register.x19 = some v
  stack_budget : StackOK SL sp
    ((Stmt.whileStmt cnd body).stackNeed +
      (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088)
  stmt_bodies : Stmt.bodiesBound Vsa.While.perCallBudget
    (.whileStmt cnd body) = true
  store_bodies : Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget
  envset_defined : (∃ v, gBody Register.x20 = some v) ∧
    (∃ v, gBody Register.x21 = some v)
  ground : ExecGround mBody SL A sp aRet aStmt.toNat (.whileStmt cnd body)
  mem_frame : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) →
    ¬ (A.lo ≤ a ∧ a < A.hi) → mBody[a]? = m0[a]?
  frame : ∀ R : Register, AbiPreservedNoise R →
    (R = Register.x8 ∨ R = Register.x9 ∨ R = Register.x18 ∨
      R = Register.x19 ∨ R = Register.x2) ∨ gBody R = g R

/-- The finite machine geometry of one `while` iteration.  The condition and
body calls are typed boundaries, not part of the residual.  The three fields
are only the parent-to-condition prefix, condition-to-body bridge, and
body-return status routing. -/
structure ExecWhileStepGeomI
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st stCond stMid stFin : SpecSt) (d : Nat) (env : Addr)
    (cnd : Expr) (body : Stmt) (v : Value)
    (bodyStatus loopStatus : Status)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) : Prop where
  truthy : v.truthy = true
  condDispatch : Triple
    (ExecEntry g N A SL φf φc st d env (.whileStmt cnd body)
      sp r aInterp aStmt aEnv aRet m0)
    (fun cfg => ∃ (gCond : (R : Register) → Option (RegisterType R))
        (aCond : BitVec 64) (mCond : Mem),
      ExecWhileCondCarrier g N A SL φf φc st d env cnd body
        sp r aInterp aStmt aEnv aRet m0 gCond aCond mCond ∧
      EvalEntry gCond N A SL φf φc st d env cnd
        (sp - 176#64) (0x80004050#64) (sp - 96#64) aInterp aCond mCond cfg)
  bodyDispatch :
    ∀ (gCond : (R : Register) → Option (RegisterType R))
      (aCond : BitVec 64) (mCond : Mem),
    ExecWhileCondCarrier g N A SL φf φc st d env cnd body
      sp r aInterp aStmt aEnv aRet m0 gCond aCond mCond →
    Triple
      (EvalExitD gCond N A SL φf φc st.store.frames.size
        st.store.closures.size stCond v (sp - 176#64)
        (0x80004050#64) (sp - 96#64) mCond)
      (fun cfg => ∃ (φfBody φcBody : Addr → Nat)
          (gBody : (R : Register) → Option (RegisterType R))
          (aBody : BitVec 64) (mBody : Mem),
        -- The condition exit extends the original maps only on the original
        -- allocated prefix.  New condition allocations are represented by the
        -- selected post maps, not equated to arbitrary old total-map values.
        PhiExtends φf φfBody st.store.frames.size ∧
        PhiExtends φc φcBody st.store.closures.size ∧
        ExecWhileBodyCarrier g N A SL φfBody φcBody stCond d env cnd body
          sp r aInterp aStmt aEnv aRet m0 gBody aBody mBody ∧
        ExecEntry gBody N A SL φfBody φcBody stCond d env body
          (sp - 176#64) (0x80004088#64) aInterp aBody
          (BitVec.ofNat 64 (φfBody env)) aRet mBody cfg)
  bodyResume :
    ∀ (φfBody φcBody : Addr → Nat)
      (gBody : (R : Register) → Option (RegisterType R))
      (aBody : BitVec 64) (mBody : Mem),
    -- These relate the original maps to the condition-post maps on the
    -- original prefix.  The following `ExecExitD` separately relates the
    -- condition-post maps to the body-post maps on `stCond`'s full prefix.
    PhiExtends φf φfBody st.store.frames.size →
    PhiExtends φc φcBody st.store.closures.size →
    ExecWhileBodyCarrier g N A SL φfBody φcBody stCond d env cnd body
      sp r aInterp aStmt aEnv aRet m0 gBody aBody mBody →
    Triple
      (ExecExitD gBody N A SL φfBody φcBody
        stCond.store.frames.size stCond.store.closures.size
        stMid bodyStatus (sp - 176#64) (0x80004088#64) aRet mBody)
      (ExecWhileStepPostI g N A SL φf φc st stMid stFin d env cnd body
        bodyStatus loopStatus sp r aInterp aStmt aEnv aRet m0)

/-- Splice the exact condition and body induction hypotheses through the three
finite machine segments of an iteration. -/
theorem execWhileStepI_of_geom
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st stCond stMid stFin : SpecSt) (d : Nat) (env : Addr)
    (cnd : Expr) (body : Stmt) (v : Value)
    (bodyStatus loopStatus : Status)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (hCond : EvalIH st d env cnd stCond v)
    (hBody : ExecIH stCond d env body stMid bodyStatus)
    (G : ExecWhileStepGeomI g N A SL φf φc st stCond stMid stFin d env
      cnd body v bodyStatus loopStatus sp r aInterp aStmt aEnv aRet m0) :
    ExecWhileStepI g N A SL φf φc st stMid stFin d env cnd body
      bodyStatus loopStatus sp r aInterp aStmt aEnv aRet m0 := by
  intro cfg hentry
  obtain ⟨cfgC, hsC, gCond, aCond, mCond, hCarrier, hCondEntry⟩ :=
    G.condDispatch cfg hentry
  obtain ⟨cfgCX, hsCX, hCondExit⟩ :=
    hCond gCond N A SL φf φc (sp - 176#64) (0x80004050#64)
      (sp - 96#64) aInterp aCond mCond cfgC hCondEntry
  obtain ⟨cfgB, hsB, φfBody, φcBody, gBody, aBody, mBody,
      hφfBody, hφcBody, hBodyCarrier, hBodyEntry⟩ :=
    G.bodyDispatch gCond aCond mCond hCarrier cfgCX hCondExit
  obtain ⟨cfgBX, hsBX, hBodyExit⟩ :=
    hBody gBody N A SL φfBody φcBody (sp - 176#64) (0x80004088#64)
      aInterp aBody (BitVec.ofNat 64 (φfBody env)) aRet mBody cfgB hBodyEntry
  obtain ⟨cfgR, hsR, hpost⟩ :=
    G.bodyResume φfBody φcBody gBody aBody mBody hφfBody hφcBody
      hBodyCarrier cfgBX hBodyExit
  exact ⟨cfgR, (((hsC.trans hsCX).trans hsB).trans hsBX).trans hsR, hpost⟩

#print axioms execWhileStepI_of_geom

/-- Select the nonrecursive exit of an exact iteration. -/
theorem execWhileExitI
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (body : Stmt)
    (bodyStatus loopStatus : Status)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (hexit : ¬ (bodyStatus = .normal ∨ bodyStatus = .cont))
    (hstep : ExecWhileStepI g N A SL φf φc st st' st' d env cnd body
      bodyStatus loopStatus sp r aInterp aStmt aEnv aRet m0) :
    Triple
      (ExecEntry g N A SL φf φc st d env (.whileStmt cnd body)
        sp r aInterp aStmt aEnv aRet m0)
      (ExecExit g N A SL φf φc st.store.frames.size st.store.closures.size
        st' loopStatus sp r aRet m0) := by
  intro cfg hentry
  obtain ⟨cfg', hs, hpost⟩ := hstep cfg hentry
  rcases hpost with ⟨hcontinue, _⟩ | ⟨_, hexit'⟩
  · exact absurd hcontinue hexit
  · exact ⟨cfg', hs, hexit'⟩

/-- Rebase a widened exit from maps selected after one iteration. -/
theorem execExitD_rebaseMaps
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc φf' φc' : Addr → Nat) (nf nc nf' nc' : Nat)
    (st' : SpecSt) (status : Status) (sp r aRet : BitVec 64)
    (m0 : Mem) (cfg : Config)
    (hsize : nf ≤ nf' ∧ nc ≤ nc')
    (hpf : PhiExtends φf φf' nf) (hpc : PhiExtends φc φc' nc)
    (hExit : ExecExitD g N A SL φf' φc' nf' nc'
      st' status sp r aRet m0 cfg) :
    ExecExitD g N A SL φf φc nf nc st' status sp r aRet m0 cfg := by
  rcases hExit with ⟨hPlain, hMem, φf'', φc'', hpf'', hpc'', hStore⟩
  refine ⟨?_, hMem, φf'', φc'', ?_, ?_, hStore⟩
  · exact execExit_extend g N A SL φf φc φf' φc' nf nc nf' nc'
      st' status sp r aRet m0 m0 cfg
      hpf hpc hsize
      (fun _ _ _ => rfl) hPlain
  · exact hpf.trans (PhiExtends.mono hsize.1 hpf'')
  · exact hpc.trans (PhiExtends.mono hsize.2 hpc'')

/-- Source-level meaning of one continuing while iteration.  Its right index
is the exact semantic midpoint consumed by the recursive while derivation. -/
def ExecWhileContinueRel
    (stCond : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (body : Stmt)
    (v : Value) (bodyStatus : Status) (st stMid : SpecSt) : Prop :=
  EvalE st d env cnd stCond v ∧
  ExecS stCond d env body stMid bodyStatus ∧
  (bodyStatus = .normal ∨ bodyStatus = .cont)

/-- Compose a continuing iteration with the recursive in-frame `while` IH. -/
theorem execWhileLoopI
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st stCond stMid stFin : SpecSt) (d : Nat) (env : Addr)
    (cnd : Expr) (body : Stmt) (v : Value)
    (bodyStatus finalStatus : Status)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (hCond : EvalE st d env cnd stCond v)
    (hBody : ExecS stCond d env body stMid bodyStatus)
    (hContinue : bodyStatus = .normal ∨ bodyStatus = .cont)
    (hRest : ExecS stMid d env (.whileStmt cnd body) stFin finalStatus)
    (hstep : ExecWhileStepI g N A SL φf φc st stMid stFin d env cnd body
      bodyStatus finalStatus sp r aInterp aStmt aEnv aRet m0)
    (hRestIH : ExecWhileArmIH stMid d env cnd body stFin finalStatus) :
    Triple
      (ExecEntry g N A SL φf φc st d env (.whileStmt cnd body)
        sp r aInterp aStmt aEnv aRet m0)
      (ExecExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        stFin finalStatus sp r aRet m0) := by
  have hIteration :
      ExecWhileContinueRel stCond d env cnd body v bodyStatus st stMid :=
    ⟨hCond, hBody, hContinue⟩
  refine (RTriple.seqEvidence
    (S := fun st0 st1 =>
      ExecS st0 d env (.whileStmt cnd body) st1 finalStatus)
    (b := stMid) (c := stFin)
    hIteration hRest hstep ?_ (Ent.refl _)).machine
  intro cfgM hpost
  rcases hpost with
    ⟨_, φf', φc', ment, liveRA, hpf, hpc, hready⟩ | ⟨hstop, _⟩
  · obtain ⟨cfgF, hsF, hexit⟩ :=
      hRestIH bodyStatus hContinue g N A SL φf' φc'
        sp r aInterp aStmt aEnv aRet m0 ment cfgM ⟨liveRA, hready⟩
    have hEntryMid : st.store.frames.size ≤ stMid.store.frames.size ∧
        st.store.closures.size ≤ stMid.store.closures.size :=
      ⟨Nat.le_trans (evalE_store_mono hCond).1 (execS_store_mono hBody).1,
       Nat.le_trans (evalE_store_mono hCond).2 (execS_store_mono hBody).2⟩
    exact ⟨cfgF, hsF, execExitD_rebaseMaps g N A SL φf φc φf' φc'
      st.store.frames.size st.store.closures.size
      stMid.store.frames.size stMid.store.closures.size
      stFin finalStatus sp r aRet m0 cfgF hEntryMid hpf hpc hexit⟩
  · exact absurd hContinue hstop

#print axioms execWhileExitI
#print axioms execExitD_rebaseMaps
#print axioms execWhileLoopI

end Vsa.Sim
