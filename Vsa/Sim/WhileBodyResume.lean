import Vsa.Sim.WhileBodyDispatch
import Vsa.Sim.rows.InitSomeReturnReady

namespace Vsa.Sim

open LeanRV64DExecutable Sail Register
open Vsa.Machine (Config Steps)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Logic (Triple)

/-- Facts needed by the finite status route after the body returns. -/
structure ExecWhileBodyExitKit
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (cnd : Expr) (body : Stmt) (status : Status)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (cfg : Config) : Prop where
  good : GoodState cfg.σ
  tick : cfg.tick < 2
  pc : cfg.σ.regs.get? Register.PC = some 0x80004088#64
  minstret : ∃ v, cfg.σ.regs.get? Register.minstret = some v
  a0 : cfg.σ.regs.get? Register.x10 = some (StatusCode status)
  ra : cfg.σ.regs.get? Register.x1 = some 0x80004088#64
  spReg : cfg.σ.regs.get? Register.x2 = some (sp - 176#64)
  s0 : cfg.σ.regs.get? Register.x8 = some aStmt
  s1 : cfg.σ.regs.get? Register.x9 = some aInterp
  s2 : cfg.σ.regs.get? Register.x18 = some aRet
  s3 : cfg.σ.regs.get? Register.x19 = some aEnv
  code : Code.Exec_stmtLoaded cfg.σ.mem
  ground : ExecGround cfg.σ.mem SL A sp aRet aStmt.toNat (.whileStmt cnd body)
  stmt : StmtRepr cfg.σ.mem aStmt.toNat (.whileStmt cnd body)
  storeSurvives : ∀ m' : Mem,
    (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → cfg.σ.mem[k]? = m'[k]?) →
    StoreRepr m' N A φf φc st.store
  out : OutRepr cfg.σ st
  saved_ra : read64 cfg.σ.mem (sp.toNat - 8) = some r.toNat
  saved_s0 : ∃ v, read64 cfg.σ.mem (sp.toNat - 16) = some v.toNat ∧
    g Register.x8 = some v
  saved_s1 : ∃ v, read64 cfg.σ.mem (sp.toNat - 24) = some v.toNat ∧
    g Register.x9 = some v
  saved_s2 : ∃ v, read64 cfg.σ.mem (sp.toNat - 32) = some v.toNat ∧
    g Register.x18 = some v
  saved_s3 : ∃ v, read64 cfg.σ.mem (sp.toNat - 40) = some v.toNat ∧
    g Register.x19 = some v

/-- Recover the parent's frame from the actual widened body exit. -/
theorem execWhileBodyExitKit_of_exit
    {g gBody : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st st' : Vsa.While.St} {d : Nat} {env : Addr}
    {cnd : Expr} {body : Stmt} {status : Status}
    {sp r aInterp aStmt aEnv aRet aBody : BitVec 64} {m0 mBody : Mem}
    {cfg : Config}
    (h : ExecWhileBodyCarrier g N A SL φf φc st d env cnd body
      sp r aInterp aStmt aEnv aRet m0 gBody aBody mBody)
    (hChild : ExecExitD gBody N A SL φf φc st.store.frames.size
      st.store.closures.size st' status (sp - 176#64) 0x80004088#64 aRet mBody cfg) :
    ∃ φf' φc', PhiExtends φf φf' st.store.frames.size ∧
      PhiExtends φc φc' st.store.closures.size ∧
      ExecWhileBodyExitKit g N A SL φf' φc' st' cnd body status
        sp r aInterp aStmt aEnv aRet cfg := by
  obtain ⟨φf', φc', hc⟩ := ScaffoldRows.initSomeChildExitView_of_exitD hChild
  have hroom := h.stack_budget.1
  have hsp176 : 176 ≤ sp.toNat := by omega
  have hspsub : (sp - 176#64).toNat = sp.toNat - 176 := by
    rw [BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    have := sp.isLt
    omega
  have hframe (a : Nat) (hstk : ¬ (SL.lo ≤ a ∧ a < sp.toNat))
      (hA : ¬ (A.lo ≤ a ∧ a < A.hi)) :=
    hc.exit.memFrame a (by rw [hspsub]; intro hs; exact hstk ⟨hs.1, by omega⟩) hA
  have hground := h.ground.transport_execExit h.stack_budget.2.1
    (fun k hlo hhi => by
      obtain ⟨b, hb⟩ := h.ground.stack_bytes k hlo hhi
      exact hc.memExtends k b hb) hframe
  have hstmt := h.ground.stmtRepr_execExit h.parent_stmt h.stack_budget.2.1 hframe
  have hcode : Code.Exec_stmtLoaded cfg.σ.mem := by
    have hcs := h.code_stack_disjoint
    have hac := h.ground.arena_code
    simp only [execStmtEntry, execStmtEnd] at hcs hac
    apply loaded_exec_stmt_agreeP mBody cfg.σ.mem _ h.code
    intro a ha
    rcases hc.exit.memFrame a
        (by rw [hspsub]; intro hs; rcases hcs with hd | hd <;> omega)
        (by intro hA; rcases hac with hd | hd <;> omega) with hr | heq
    · exfalso
      have hret := h.ground.aret.inSL
      have hwin := h.stack_win
      rw [tohostAddr_val] at hwin
      omega
    · exact heq.symm
  have hag : AgreeP (fun k => sp.toNat - 40 ≤ k ∧ k < sp.toNat)
      mBody cfg.σ.mem := by
    intro k hk
    rcases hc.exit.memFrame k
        (by rw [hspsub]; intro hs; omega)
        (by rcases h.ground.arena_stack with hd | hd <;> omega) with hr | heq
    · exact absurd hr (by
        rcases h.ground.aret.scribble_disjoint with hd | hd <;> omega)
    · exact heq.symm
  obtain ⟨v8, hr8, hg8⟩ := h.saved_s0
  obtain ⟨v9, hr9, hg9⟩ := h.saved_s1
  obtain ⟨v18, hr18, hg18⟩ := h.saved_s2
  obtain ⟨v19, hr19, hg19⟩ := h.saved_s3
  obtain ⟨hra, hs0, hs1, hs2, hs3⟩ := ScaffoldRows.initSomeReturn_saved_reads
    (by omega) hag h.saved_ra hr8 hr9 hr18 hr19
  refine ⟨φf', φc', hc.frames, hc.closures, ?_⟩
  exact
    { good := hc.exit.good
      tick := hc.exit.tick
      pc := by simpa using hc.exit.pc
      minstret := hc.exit.minstret
      a0 := hc.exit.a0
      ra := hc.exit.ra
      spReg := hc.exit.spReg
      s0 := (hc.exit.frame Register.x8 (by decide)).trans h.s0
      s1 := (hc.exit.frame Register.x9 (by decide)).trans h.s1
      s2 := (hc.exit.frame Register.x18 (by decide)).trans h.s2
      s3 := (hc.exit.frame Register.x19 (by decide)).trans h.s3
      code := hcode
      ground := hground
      stmt := hstmt
      storeSurvives := hc.storeSurvives
      out := hc.exit.out
      saved_ra := hra
      saved_s0 := ⟨v8, hs0, hg8⟩
      saved_s1 := ⟨v9, hs1, hg9⟩
      saved_s2 := ⟨v18, hs2, hg18⟩
      saved_s3 := ⟨v19, hs3, hg19⟩ }

/-- Marshal a recovered body exit into the reflected status-route interface. -/
theorem ExecWhileBodyExitKit.routePre
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : Vsa.While.St} {cnd : Expr} {body : Stmt} {status : Status}
    {sp r aInterp aStmt aEnv aRet : BitVec 64} {cfg : Config}
    (h : ExecWhileBodyExitKit g N A SL φf φc st cnd body status
      sp r aInterp aStmt aEnv aRet cfg)
    (bs : List BBlock)
    (hfacts : ChainFacts cfg.σ.mem cfg.σ.mem
      (execWhileRouteL (StatusCode status) (sp - 176#64) 0x80004088#64
        aStmt aInterp aRet aEnv) [] bs) :
    ExecWhileRoutePreF bs (fun R => cfg.σ.regs.get? R)
      (StatusCode status) (sp - 176#64) 0x80004088#64 aStmt aInterp aRet aEnv
      [] 0x80004088#64 cfg.σ.mem cfg.σ.sailOutput cfg := by
  refine ⟨⟨⟨h.good, rfl, h.pc, h.minstret, ?_, ?_, hfacts, h.tick⟩, rfl⟩,
    fun _ _ => rfl⟩
  · simp only [execWhileRouteL, GHolds, gprGet]
    exact ⟨h.a0, h.spReg, h.ra, h.s0, h.s1, h.s2, h.s3, True.intro⟩
  · change KeysOK [10, 2, 1, 8, 9, 18, 19]
    decide

#print axioms execWhileBodyExitKit_of_exit
#print axioms ExecWhileBodyExitKit.routePre

/-- The exact finite route selected by the source body status. -/
def execWhileBodyResumeSegment : Status → List BBlock
  | .brk => execWhileBreakRouteSeg
  | .ret _ => execWhileRetRouteSeg
  | .normal | .cont => execWhileLoopRouteSeg

def execWhileBodyResumePC : Status → BitVec 64
  | .brk => 0x80004090#64
  | .ret _ => 0x80004150#64
  | .normal | .cont => 0x80004034#64

/-- Execute the status route from the recovered body return, retaining its
same-run frame and the control facts needed by the continuation. -/
theorem ExecWhileBodyExitKit.resume
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : Vsa.While.St} {cnd : Expr} {body : Stmt} {status : Status}
    {sp r aInterp aStmt aEnv aRet : BitVec 64} {cfg : Config}
    (h : ExecWhileBodyExitKit g N A SL φf φc st cnd body status
      sp r aInterp aStmt aEnv aRet cfg) :
    ∃ cfg',
      (ExecWhileRoutePost (execWhileBodyResumeSegment status)
        (execWhileBodyResumePC status) (StatusCode status) (sp - 176#64)
        0x80004088#64 aStmt aInterp aRet aEnv [] cfg.σ.mem cfg.σ.sailOutput cfg' ∧
      (∀ R, AbiPreserved R = true → cfg'.σ.regs.get? R = cfg.σ.regs.get? R) ∧
      cfg'.tick < 2 ∧ ∃ w, cfg'.σ.regs.get? Register.minstret = some w) ∧
      FramedSteps execWhileRouteEffect cfg cfg' := by
  have hfacts : ChainFacts cfg.σ.mem cfg.σ.mem
      (execWhileRouteL (StatusCode status) (sp - 176#64) 0x80004088#64
        aStmt aInterp aRet aEnv) [] (execWhileBodyResumeSegment status) := by
    cases status with
    | normal => exact execWhileLoopNormalRoute_facts _ _ _ _ _ _ _ h.code
    | cont => exact execWhileLoopContRoute_facts _ _ _ _ _ _ _ h.code
    | brk => exact execWhileBreakRoute_facts _ _ _ _ _ _ _ h.code
    | ret v => exact execWhileRetRoute_facts _ _ _ _ _ _ _ h.code
  have hpre := h.routePre (execWhileBodyResumeSegment status) hfacts
  cases status with
  | normal => exact (execWhileLoopRouteRow_framed _ _ _ _ _ _ _ _ _ _ _).run cfg hpre
  | cont => exact (execWhileLoopRouteRow_framed _ _ _ _ _ _ _ _ _ _ _).run cfg hpre
  | brk => exact (execWhileBreakRouteRow_framed _ _ _ _ _ _ _ _ _ _ _).run cfg hpre
  | ret v => exact (execWhileRetRouteRow_framed _ _ _ _ _ _ _ _ _ _ _).run cfg hpre

#print axioms ExecWhileBodyExitKit.resume

end Vsa.Sim
