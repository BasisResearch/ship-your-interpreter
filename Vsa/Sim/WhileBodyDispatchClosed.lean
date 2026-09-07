import Vsa.Sim.WhileBodyDispatch
import Vsa.Sim.WhileCondCopyFrame
import Vsa.While.StoreBodiesBoundPreservation

namespace Vsa.Sim

open LeanRV64DExecutable Sail Register
open Vsa.Machine (Config)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Logic (Triple)

/-- Compose the condition return, concrete copy/truthiness route, and body
call. The selected allocation maps and source state remain indexed throughout. -/
theorem execWhileBodyDispatch_closed
    {g gCond : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st stCond : Vsa.While.St} {d : Nat} {env : Addr}
    {cnd : Expr} {body : Stmt} {v : Value}
    {sp r aInterp aStmt aEnv aRet aCond : BitVec 64} {m0 mCond : Mem}
    (hC : EvalE st d env cnd stCond v) (htruthy : v.truthy = true)
    (hCarrier : ExecWhileCondCarrier g N A SL φf φc st d env cnd body
      sp r aInterp aStmt aEnv aRet m0 gCond aCond mCond) :
    Triple
      (EvalExitD gCond N A SL φf φc st.store.frames.size
        st.store.closures.size stCond v (sp - 176#64)
        0x80004050#64 (sp - 96#64) mCond)
      (fun cfg => ∃ (φfBody φcBody : Addr → Nat)
          (gBody : (R : Register) → Option (RegisterType R))
          (aBody : BitVec 64) (mBody : Mem),
        PhiExtends φf φfBody st.store.frames.size ∧
        PhiExtends φc φcBody st.store.closures.size ∧
        ExecWhileBodyCarrier g N A SL φfBody φcBody stCond d env cnd body
          sp r aInterp aStmt aEnv aRet m0 gBody aBody mBody ∧
        ExecEntry gBody N A SL φfBody φcBody stCond d env body
          (sp - 176#64) 0x80004088#64 aInterp aBody
          (BitVec.ofNat 64 (φfBody env)) aRet mBody cfg) := by
  intro cfg hExitD
  obtain ⟨φfBody, φcBody, aBody, hφf, hφc, hStoreSurv, hKit⟩ :=
    execWhileCondExitKit_at_exit g gCond N A SL φf φc st stCond d env
      cnd body v sp r aInterp aStmt aEnv aRet aCond m0 mCond hCarrier cfg hExitD
  obtain ⟨mCopy, cfgCopy, hsCopy, hCopyEq, hCopy⟩ :=
    execWhileCondCopyReady_of_exitKit_exact g gCond N A SL φf φc φfBody φcBody
      st stCond d env cnd body v sp r aInterp aStmt aEnv aRet aCond
      m0 mCond aBody cfg hCarrier hKit
  obtain ⟨cfgHead, hsTruthy, hHead⟩ :=
    execWhileTruthy_of_copyReady gCond N φcBody v (sp - 176#64) aStmt
      aInterp aRet aEnv mCopy cfg.σ.sailOutput cfgCopy hCopy htruthy
  have hExit := hExitD.1
  have hroom := hCarrier.stack_budget.1
  have hspHi := hCarrier.stack_budget.2.1
  have h176 : 176 ≤ sp.toNat := by omega
  have hesp : (sp - 176#64).toNat = sp.toNat - 176 := by
    rw [BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    have := sp.isLt
    omega
  have hsret : (sp - 96#64).toNat = sp.toNat - 96 := by
    rw [BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    have := sp.isLt
    omega
  have hnowrap : (sp - 176#64).toNat + 104 ≤ 0x100000000 := by
    rw [hesp]
    have := hCarrier.stack_budget.2.1
    have := hCarrier.stack_ram.2
    omega
  have hCopyFrame : ∀ k,
      ¬ ((sp - 176#64).toNat + 16 ≤ k ∧ k < (sp - 176#64).toNat + 40) →
      mCopy[k]? = cfg.σ.mem[k]? := by
    intro k hk
    rw [hCopyEq]
    exact execWhileCondCopy_writeLog_frame cfg.σ.mem (sp - 176#64)
      aStmt aInterp aRet aEnv hnowrap k hk
  have hCopyOutside : ∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) →
      mCopy[k]? = cfg.σ.mem[k]? := by
    intro k hk
    apply hCopyFrame k
    rw [hesp]
    intro hw
    exact hk ⟨by omega, by omega⟩
  have hCopyExt : MemExtends cfg.σ.mem mCopy := by
    rw [hCopyEq]
    exact execWhileCondCopy_memExtends cfg.σ.mem (sp - 176#64)
      aStmt aInterp aRet aEnv
  have hPop : StackBytesPresent mCopy SL := by
    intro k hlo hhi
    obtain ⟨b, hb⟩ := hKit.stack_bytes k hlo hhi
    exact hCopyExt k b hb
  have hGround := hKit.ground.transport_offstack hCarrier.stack_budget.2.1
    hPop hCopyOutside
  have hParent := hKit.ground.stmtRepr_offstack hKit.parent_stmt
    hCarrier.stack_budget.2.1 hCopyOutside
  obtain ⟨aBodyCopy, hBodyRead, hBodyRepr⟩ := stmtRepr_while_body_bv hParent
  have hStoreCopy : ∀ m' : Mem,
      (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → mCopy[k]? = m'[k]?) →
      StoreRepr m' N A φfBody φcBody stCond.store := by
    intro m' hag
    apply hStoreSurv m'
    intro k hk
    exact (hCopyOutside k (by
      intro hs
      exact hk ⟨hs.1, Nat.lt_of_lt_of_le hs.2 hCarrier.stack_budget.2.1⟩)).symm.trans
      (hag k hk)
  have hSaved : AgreeP (fun k => sp.toNat - 40 ≤ k ∧ k < sp.toNat)
      mCond mCopy := by
    intro k hk
    rw [hCopyFrame k (by rw [hesp]; omega)]
    rcases hExit.memFrame k
        (by rw [hesp]; intro hs; omega)
        (by rcases hCarrier.ground.arena_stack with hd | hd <;> omega) with hr | heq
    · rw [hsret] at hr
      omega
    · exact heq.symm
  have hSavedRead (off : Nat) (hlo : 8 ≤ off) (hhi : off ≤ 40) :
      read64 mCopy (sp.toNat - off) = read64 mCond (sp.toNat - off) := by
    exact (read64_agreeP hSaved (fun k hk => ⟨by omega, by omega⟩)).symm
  have hEnv : aEnv = BitVec.ofNat 64 (φfBody env) := by
    rw [hφf env hCarrier.env_valid]
    exact hCarrier.env_addr
  have hBodies : StoreBodiesBound stCond.store perCallBudget := by
    apply StoreBodiesBound.afterExecS (ExecS.expr st d env cnd stCond v hC)
      (s := .expr cnd)
    · have hb := hCarrier.stmt_bodies
      simp only [Stmt.bodiesBound, Bool.and_eq_true] at hb ⊢
      exact hb.1
    · exact hCarrier.store_bodies
  have hStage : ExecWhileBodyHeadStage g N A SL φfBody φcBody stCond d env
      cnd body sp r aInterp aStmt aEnv aRet m0 aBodyCopy mCopy cfgHead := by
    refine
      { good := hHead.good
        tick := hHead.tick
        pc := hHead.pc
        minstret := hHead.minstret
        mem := hHead.mem
        out := by
          change String.join cfgHead.σ.sailOutput.toList = stCond.out
          rw [hHead.out]
          exact hKit.out
        carrier := ?_ }
    · refine
        { s0 := (hHead.frame Register.x8 (by decide)).trans hCarrier.s0
          s1 := (hHead.frame Register.x9 (by decide)).trans hCarrier.s1
          s2 := (hHead.frame Register.x18 (by decide)).trans hCarrier.s2
          s3 := (hHead.frame Register.x19 (by decide)).trans hCarrier.s3
          spReg := (hHead.frame Register.x2 (by decide)).trans hCarrier.spReg
          parentSp := hCarrier.parentSp
          code := hCopy.code
          code_stack_disjoint := hCarrier.code_stack_disjoint
          stack_ram := hCarrier.stack_ram
          stack_win := hCarrier.stack_win
          ra_align := hCarrier.ra_align
          parent_stmt := hParent
          body_stmt := hBodyRepr
          env_addr := hEnv
          store := hStoreCopy mCopy (fun _ _ => rfl)
          env_valid := hCarrier.env_valid.afterEvalE hC
          store_survives := hStoreCopy
          saved_ra := (hSavedRead 8 (by omega) (by omega)).trans hCarrier.saved_ra
          saved_s0 := ?_
          saved_s1 := ?_
          saved_s2 := ?_
          saved_s3 := ?_
          stack_budget := hCarrier.stack_budget
          stmt_bodies := hCarrier.stmt_bodies
          store_bodies := hBodies
          envset_defined := ?_
          ground := hGround
          mem_extends := (hCarrier.mem_extends.trans hExitD.2.1).trans hCopyExt
          mem_frame := ?_
          frame := fun R hR => (hCarrier.frame R hR).imp_right
            (fun heq => (hHead.frame R hR.1).trans heq) }
      · obtain ⟨v8, hs8, hg8⟩ := hCarrier.saved_s0
        exact ⟨v8, (hSavedRead 16 (by omega) (by omega)).trans hs8, hg8⟩
      · obtain ⟨v9, hs9, hg9⟩ := hCarrier.saved_s1
        exact ⟨v9, (hSavedRead 24 (by omega) (by omega)).trans hs9, hg9⟩
      · obtain ⟨v18, hs18, hg18⟩ := hCarrier.saved_s2
        exact ⟨v18, (hSavedRead 32 (by omega) (by omega)).trans hs18, hg18⟩
      · obtain ⟨v19, hs19, hg19⟩ := hCarrier.saved_s3
        exact ⟨v19, (hSavedRead 40 (by omega) (by omega)).trans hs19, hg19⟩
      · obtain ⟨⟨v20, hv20⟩, ⟨v21, hv21⟩⟩ := hCarrier.envset_defined
        exact ⟨⟨v20, (hHead.frame Register.x20 (by decide)).trans hv20⟩,
          ⟨v21, (hHead.frame Register.x21 (by decide)).trans hv21⟩⟩
      · intro k hstk hA
        rw [hCopyOutside k hstk]
        rcases hExit.memFrame k
            (by rw [hesp]; intro hs; exact hstk ⟨hs.1, by omega⟩) hA with hr | heq
        · exfalso
          rw [hsret] at hr
          exact hstk ⟨by omega, by omega⟩
        · exact heq.trans (hCarrier.mem_frame k hstk)
  obtain ⟨aChild, cfgChild, hsChild, hBodyCarrier, hBodyEntry⟩ :=
    execWhileBodyEntry_of_stage hStage
  exact ⟨cfgChild, (hsCopy.trans hsTruthy).trans hsChild,
    φfBody, φcBody, (fun R => cfgChild.σ.regs.get? R), aChild, mCopy,
    hφf, hφc, hBodyCarrier, hBodyEntry⟩

#print axioms execWhileBodyDispatch_closed

end Vsa.Sim
