import Vsa.Sim.rows.ExecDispatchRows
import Vsa.Sim.rows.SeqForRows
import Vsa.Sim.rows.TruthyCopyFor
import Vsa.Sim.ExecWhileSites

/-!
# `Field_hFlCondFalseClosed` — the for-loop condition-false residual, closed

`hFlCondFalse` composes only parametric pieces: the in-frame condition
dispatch from the loop head (`forCondArm`), the child's exit kit, the copy and
`value_truthy` (`forTruthy`), the reflected falsy route (`beqz a0` taken into
the normal exit), the normal-exit head after the route, the parametric
`li a0,0; j; epilogue` tail at `0x80004090`, and the memory rebase from the
reached loop-head memory to the statement entry memory.
-/

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code
open Vsa.Sim.TermSimAssembly

/-- The `li a0,0` site of the loop-family normal exit. -/
theorem forExit_liSite : LiZeroSite 0x80004090#64 :=
  fun σ i u vmi hG hpc hmi hmem hi =>
    site_80004090_es σ i u _ vmi hG hpc hmi hmem rfl hi

/-- The `j 0x8000409c` site of the loop-family normal exit. -/
theorem forExit_jSite : JumpSite (BitVec.addInt 0x80004090#64 4) (0x000008#21) :=
  fun σ i u vmi hG hpc hmi hmem htgt hi =>
    site_80004094_es σ i u _ vmi hG hpc hmi hmem (by decide) htgt hi

/-- The falsy resume of the for-loop condition from its widened exit, at the
reached loop-head memory. -/
theorem forCondFalse_resume
    {g gC : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st st' : Vsa.While.St} {d : Nat} {outer : Addr}
    {init : Option Stmt} {c : Expr} {step : Option Expr} {body : Stmt} {v : Value}
    {sp r aInterp aStmt aOuter aRet aC : BitVec 64} {ment mC : Mem}
    (hFalsy : v.truthy = false)
    (hCarrier : forCondArm.Carrier (.forStmt init (some c) step body) c g N A SL φf φc st d
      outer sp r aInterp aStmt aOuter aRet ment gC aC mC) :
    Triple
      (EvalExitD gC N A SL φf φc st.store.frames.size st.store.closures.size st' v
        (sp - 176#64) forCondArm.retPC (forCondArm.sret (sp - 176#64)) mC)
      (ExecExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st' .normal sp r aRet ment) := by
  intro cfgX hExit
  obtain ⟨φf', φc', hpf, hpc, hSurv, hKit⟩ :=
    forCondArm.exitKit_at_exit forCondArm_cert hCarrier cfgX hExit
  obtain ⟨mCopy, cfgCopy, hsCopy, hmCopy, hReady⟩ :=
    TruthyCopy.copyReady_of_exitKit forCondArm forCondArm_cert forTruthy forTruthy_cert
      cfgX hCarrier hKit
  obtain ⟨cfgT, hsT, hRet⟩ :=
    TruthyCopy.truthyReturn_of_copyReady forCondArm forTruthy forTruthy_cert N φc' hReady
  rw [hFalsy] at hRet
  obtain ⟨h176, hesp, hsret, hroom, hSLhi, hal⟩ := hCarrier.geom forCondArm_cert
  have hnowrap : (sp - 176#64).toNat + 40 ≤ 0x100000000 := by
    have := hCarrier.stack_ram.2; omega
  have hcopyFrame : ∀ k, ¬ ((sp - 176#64).toNat + 16 ≤ k ∧ k < (sp - 176#64).toNat + 40) →
      mCopy[k]? = cfgX.σ.mem[k]? := by
    rw [hmCopy]
    exact TruthyCopy.writeLog_frame forCondArm forTruthy forTruthy_cert cfgX.σ.mem
      (sp - 176#64) aStmt aInterp aRet aOuter hnowrap
  have hcopyExt : MemExtends cfgX.σ.mem mCopy := by
    rw [hmCopy]
    exact TruthyCopy.memExtends forCondArm forTruthy forTruthy_cert cfgX.σ.mem
      (sp - 176#64) aStmt aInterp aRet aOuter
  obtain ⟨cfgR, hsR, hHead⟩ :=
    TruthyCopy.route_of_truthyReturn forTruthy forFalsySeg 0x80004090#64 [] hRet
      (by change ChainOK forTruthy.retPC [10, 2, 1, 8, 9, 18, 19] forFalsySeg; decide)
      rfl
      (by change WrChainAvoids TruthyCopy.abiButS0 forFalsySeg; decide)
      (forFalsy_facts mCopy (sp - 176#64) aStmt aInterp aRet aOuter hReady.code)
  have hmemR : cfgR.σ.mem = mCopy := by
    rw [hHead.mem]; rfl
  have hPre := TruthyCopy.normalExitPre_of_route forCondArm forCondArm_cert hCarrier cfgX hExit
    hpf hpc hSurv hKit hcopyFrame hcopyExt hReady.code 0x80004090#64 cfgR
    hHead.good hHead.tick hHead.pc hHead.minstret hmemR hHead.out hHead.frame
  obtain ⟨cfgE, hsE, hExitD⟩ :=
    normalExitTail 0x80004090#64 (0x000008#21) forExit_liSite forExit_jSite (by decide) cfgR hPre
  exact ⟨cfgE, ((hsCopy.trans hsT).trans hsR).trans hsE, hExitD⟩

/-- Concrete supplier for the for-loop condition-false residual. -/
theorem ScaffoldRows.field_hFlCondFalse :
    ∀ st st' d env c step b v hC hFalse,
      Rows.FlCondFalseResid st st' d env c step b v hC hFalse := by
  intro st st' d env c step b v hC hFalse hIH
  show ForLoopCtxIH st d env (some c) step b st' .normal
  intro init g N A SL φf φc sp r aInterp aStmt aOuter aRet m0 ment cfg hPre
  obtain ⟨liveRA, hReady⟩ := hPre
  obtain ⟨cfgC, hsC, gC, aC, mC, hCarrier, hCondEntry⟩ := forCond_dispatchFromLoopHead hReady
  obtain ⟨cfgX, hsX, hCondExit⟩ :=
    hIH.forget gC N A SL φf φc (sp - 176#64) forCondArm.retPC
      (forCondArm.sret (sp - 176#64)) aInterp aC mC cfgC hCondEntry
  obtain ⟨cfgE, hsE, hExitD⟩ := forCondFalse_resume hFalse hCarrier cfgX hCondExit
  exact ⟨cfgE, hsC.trans (hsX.trans hsE),
    Rows.execExitD_rebaseMem g N A SL φf φc _ _ st' .normal sp r aRet m0 ment cfgE
      hReady.mem_extends hReady.mem_frame hExitD⟩

#print axioms ScaffoldRows.field_hFlCondFalse

end Vsa.Sim
