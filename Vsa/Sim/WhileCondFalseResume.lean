import Vsa.Sim.WhileFalsyCopyReady
import Vsa.Sim.WhileNormalExitTail
import Vsa.Sim.WhileCondCopyFrame

namespace Vsa.Sim

open LeanRV64DExecutable Sail Register
open Vsa.Machine (Config)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Logic (Triple)

/-- Resume the reached condition exit through the falsy branch and normal
parent epilogue. The child-selected maps and memory remain attached to the run. -/
theorem execWhileCondResume_false
    {g gCond : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st st' : Vsa.While.St} {d : Nat} {env : Addr}
    {cnd : Expr} {body : Stmt} {v : Value}
    {sp r aInterp aStmt aEnv aRet aCond : BitVec 64} {m0 mCond : Mem}
    (hFalsy : v.truthy = false)
    (hCarrier : ExecWhileCondCarrier g N A SL φf φc st d env cnd body
      sp r aInterp aStmt aEnv aRet m0 gCond aCond mCond) :
    Triple
      (EvalExitD gCond N A SL φf φc st.store.frames.size
        st.store.closures.size st' v (sp - 176#64)
        0x80004050#64 (sp - 96#64) mCond)
      (ExecExitD g N A SL φf φc st.store.frames.size
        st.store.closures.size st' .normal sp r aRet m0) := by
  intro cfg hExitD
  obtain ⟨φfBody, φcBody, aBody, hφf, hφc, hStoreSurv, hKit⟩ :=
    execWhileCondExitKit_at_exit g gCond N A SL φf φc st st' d env
      cnd body v sp r aInterp aStmt aEnv aRet aCond m0 mCond hCarrier cfg hExitD
  obtain ⟨mCopy, cfgCopy, hsCopy, hCopyEq, hCopy⟩ :=
    execWhileCondCopyReady_of_exitKit_exact g gCond N A SL φf φc φfBody φcBody
      st st' d env cnd body v sp r aInterp aStmt aEnv aRet aCond
      m0 mCond aBody cfg hCarrier hKit
  obtain ⟨cfgHead, hsFalsy, hHead⟩ :=
    execWhileFalsy_of_copyReady gCond N φcBody v (sp - 176#64) aStmt
      aInterp aRet aEnv mCopy cfg.σ.sailOutput cfgCopy hCopy hFalsy
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
  have hStoreCopy : ∀ m' : Mem,
      (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → mCopy[k]? = m'[k]?) →
      StoreRepr m' N A φfBody φcBody st'.store := by
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
  have hsp8 : sp.toNat % 8 = 0 := by
    have := hCarrier.stack_budget.2.2
    omega
  have hroom176 : SL.lo + 176 ≤ sp.toNat := by omega
  have hsphi : sp.toNat ≤ 0x100000000 :=
    Nat.le_trans hCarrier.stack_budget.2.1 hCarrier.stack_ram.2
  have hsplo : 0x80000000 ≤ sp.toNat :=
    Nat.le_trans hCarrier.stack_ram.1
      (Nat.le_trans (Nat.le_add_right SL.lo _) hroom)
  have hspwin : tohostAddr + 16 + 176 ≤ sp.toNat :=
    Nat.le_trans (Nat.add_le_add_right hCarrier.stack_win 176) hroom176
  have hTail : WhileNormalExitTailPre g N A SL φf φc φfBody φcBody
      st.store.frames.size st.store.closures.size st' sp r aRet m0 cfgHead := by
    refine
      { good := hHead.good
        tick := hHead.tick
        pc := hHead.pc
        minstret := hHead.minstret
        spReg := (hHead.frame Register.x2 (by decide)).trans hCarrier.spReg
        code := by rw [hHead.mem]; exact hCopy.code
        out := by
          change String.join cfgHead.σ.sailOutput.toList = st'.out
          rw [hHead.out]
          exact hKit.out
        frames := hφf
        closures := hφc
        storeSurvives := by rw [hHead.mem]; exact hStoreCopy
        saved_ra := by
          rw [hHead.mem]
          exact (hSavedRead 8 (by omega) (by omega)).trans hCarrier.saved_ra
        saved_s0 := ?_
        saved_s1 := ?_
        saved_s2 := ?_
        saved_s3 := ?_
        parentSp := hCarrier.parentSp
        frame := ?_
        memExtends := by
          rw [hHead.mem]
          exact (hCarrier.mem_extends.trans hExitD.2.1).trans hCopyExt
        memFrame := ?_
        spRoom := h176
        spHi := hsphi
        spLo := hsplo
        spWin := hspwin
        spAlign := hsp8
        retAlign := hCarrier.ra_align }
    · rw [hHead.mem]
      obtain ⟨v8, hs8, hg8⟩ := hCarrier.saved_s0
      exact ⟨v8, (hSavedRead 16 (by omega) (by omega)).trans hs8, hg8⟩
    · rw [hHead.mem]
      obtain ⟨v9, hs9, hg9⟩ := hCarrier.saved_s1
      exact ⟨v9, (hSavedRead 24 (by omega) (by omega)).trans hs9, hg9⟩
    · rw [hHead.mem]
      obtain ⟨v18, hs18, hg18⟩ := hCarrier.saved_s2
      exact ⟨v18, (hSavedRead 32 (by omega) (by omega)).trans hs18, hg18⟩
    · rw [hHead.mem]
      obtain ⟨v19, hs19, hg19⟩ := hCarrier.saved_s3
      exact ⟨v19, (hSavedRead 40 (by omega) (by omega)).trans hs19, hg19⟩
    · intro R hR he8 he9 he18 he19 he2
      have hg : gCond R = g R := by
        rcases hCarrier.frame R hR with hspecial | heq
        · rcases hspecial with rfl | rfl | rfl | rfl | rfl
          · simp at he8
          · simp at he9
          · simp at he18
          · simp at he19
          · simp at he2
        · exact heq
      exact (hHead.frame R hR.1).trans hg
    · intro k hstk hA
      apply Or.inr
      rw [hHead.mem, hCopyOutside k hstk]
      rcases hExit.memFrame k
          (by rw [hesp]; intro hs; exact hstk ⟨hs.1, by omega⟩) hA with hr | heq
      · exfalso
        rw [hsret] at hr
        exact hstk ⟨by omega, by omega⟩
      · exact heq.trans (hCarrier.mem_frame k hstk)
  obtain ⟨cfgFinal, hsTail, hFinal⟩ := execWhileNormalExitTail cfgHead hTail
  exact ⟨cfgFinal, (hsCopy.trans hsFalsy).trans hsTail, hFinal⟩

#print axioms execWhileCondResume_false

end Vsa.Sim
