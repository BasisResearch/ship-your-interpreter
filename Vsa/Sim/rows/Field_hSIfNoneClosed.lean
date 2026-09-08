import Vsa.Sim.rows.ExecDispatchRows
import Vsa.Sim.rows.TruthyCopyIf
import Vsa.Sim.ExecIfSites

/-!
# `Field_hSIfNoneClosed` — the `if`-without-`else` residual, closed

`hSIfNone` composes only parametric pieces: the arm dispatch (`ifCondArm`),
the child's exit kit, the copy and `value_truthy` (`ifTruthy`), the reflected
falsy-no-`else` route, the normal-exit head after the route, and the
parametric `li a0,0; j; epilogue` tail at `0x800042d4`.
-/

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

/-- The `li a0,0` site of the `if` arm's no-`else` exit. -/
theorem ifNone_liSite : LiZeroSite 0x800042d4#64 :=
  fun σ i u vmi hG hpc hmi hmem hi =>
    site_800042d4_es σ i u _ vmi hG hpc hmi hmem rfl hi

/-- The `j 0x8000409c` site of the `if` arm's no-`else` exit. -/
theorem ifNone_jSite : JumpSite (BitVec.addInt 0x800042d4#64 4) (0x1ffdc4#21) :=
  fun σ i u vmi hG hpc hmi hmem htgt hi =>
    site_800042d8_es σ i u _ vmi hG hpc hmi hmem (by decide) htgt hi

/-- The falsy resume of `ifNone` from the condition's widened exit. -/
theorem ifNone_resume
    {g gC : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st st' : Vsa.While.St} {d : Nat} {env : Addr} {c : Expr} {t : Stmt} {v : Value}
    {sp r aInterp aStmt aEnv aRet aC : BitVec 64} {m0 mC : Mem}
    (hFalsy : v.truthy = false)
    (hCarrier : ifCondArm.Carrier (.ifStmt c t none) c g N A SL φf φc st d env
      sp r aInterp aStmt aEnv aRet m0 gC aC mC) :
    Triple
      (EvalExitD gC N A SL φf φc st.store.frames.size st.store.closures.size st' v
        (sp - 176#64) ifCondArm.retPC (ifCondArm.sret (sp - 176#64)) mC)
      (ExecExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st' .normal sp r aRet m0) := by
  intro cfgX hExit
  obtain ⟨φf', φc', hpf, hpc, hSurv, hKit⟩ :=
    ifCondArm.exitKit_at_exit ifCondArm_cert hCarrier cfgX hExit
  obtain ⟨mCopy, cfgCopy, hsCopy, hmCopy, hReady⟩ :=
    TruthyCopy.copyReady_of_exitKit ifCondArm ifCondArm_cert ifTruthy ifTruthy_cert
      cfgX hCarrier hKit
  obtain ⟨cfgT, hsT, hRet⟩ :=
    TruthyCopy.truthyReturn_of_copyReady ifCondArm ifTruthy ifTruthy_cert N φc' hReady
  rw [hFalsy] at hRet
  obtain ⟨h176, hesp, hsret, hroom, hSLhi, hal⟩ := hCarrier.geom ifCondArm_cert
  have hnowrap : (sp - 176#64).toNat + 40 ≤ 0x100000000 := by
    have := hCarrier.stack_ram.2; omega
  have hcopyFrame : ∀ k, ¬ ((sp - 176#64).toNat + 16 ≤ k ∧ k < (sp - 176#64).toNat + 40) →
      mCopy[k]? = cfgX.σ.mem[k]? := by
    rw [hmCopy]
    exact TruthyCopy.writeLog_frame ifCondArm ifTruthy ifTruthy_cert cfgX.σ.mem
      (sp - 176#64) aStmt aInterp aRet aEnv hnowrap
  have hcopyExt : MemExtends cfgX.σ.mem mCopy := by
    rw [hmCopy]
    exact TruthyCopy.memExtends ifCondArm ifTruthy ifTruthy_cert cfgX.σ.mem
      (sp - 176#64) aStmt aInterp aRet aEnv
  have hCopyOutside : ∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → mCopy[k]? = cfgX.σ.mem[k]? := by
    intro k hk
    apply hcopyFrame k
    rw [hesp]
    intro hw
    exact hk ⟨by omega, by omega⟩
  have hPop : StackBytesPresent mCopy SL := by
    intro k hklo hkhi
    obtain ⟨b, hb⟩ := hKit.stack_bytes k hklo hkhi
    exact hcopyExt k b hb
  have hGroundCopy : ExecGround mCopy SL A sp aRet aStmt.toNat (.ifStmt c t none) :=
    hKit.ground.transport_offstack hSLhi hPop hCopyOutside
  have hStmtCopy : StmtRepr mCopy aStmt.toNat (.ifStmt c t none) :=
    hKit.ground.stmtRepr_offstack hKit.parent_stmt hSLhi hCopyOutside
  have hnull : read64 mCopy (aStmt.toNat + 24) = some 0 := by
    cases hStmtCopy with | ifNoElse _ _ _ _ _ h0 => exact h0
  obtain ⟨cfgR, hsR, hHead⟩ :=
    TruthyCopy.route_of_truthyReturn ifTruthy ifFalsyNoElseSeg 0x800042d4#64
      (ifRouteLds mCopy aStmt 24) hRet
      (by change ChainOK ifTruthy.retPC [10, 2, 1, 8, 9, 18, 19] ifFalsyNoElseSeg; decide)
      rfl
      (by change WrChainAvoids TruthyCopy.abiButS0 ifFalsyNoElseSeg; decide)
      (ifFalsyNoElse_facts hGroundCopy hReady.code hnull (sp - 176#64) aInterp aRet aEnv)
  have hmemR : cfgR.σ.mem = mCopy := by
    rw [hHead.mem]; rfl
  have hPre := TruthyCopy.normalExitPre_of_route ifCondArm ifCondArm_cert hCarrier cfgX hExit
    hpf hpc hSurv hKit hcopyFrame hcopyExt hReady.code 0x800042d4#64 cfgR
    hHead.good hHead.tick hHead.pc hHead.minstret hmemR hHead.out hHead.frame
  obtain ⟨cfgE, hsE, hExitD⟩ :=
    normalExitTail 0x800042d4#64 (0x1ffdc4#21) ifNone_liSite ifNone_jSite (by decide) cfgR hPre
  exact ⟨cfgE, ((hsCopy.trans hsT).trans hsR).trans hsE, hExitD⟩

/-- Concrete supplier for the `if`-without-`else` residual. -/
theorem ScaffoldRows.field_hSIfNone :
    ∀ st st' d env c t v hC, Rows.IfNoneCaseResid st st' d env c t v hC := by
  intro st st' d env c t v hC hFalsy _ g N A SL φf φc sp r aInterp aStmt aEnv aRet m0
  exact
    { dispatch := execIfCondDispatch_generic g N A SL φf φc st d env c t none
        sp r aInterp aStmt aEnv aRet m0
      resume := fun gC aC mC hCarrier => ifNone_resume hFalsy hCarrier }

#print axioms ScaffoldRows.field_hSIfNone

end Vsa.Sim
