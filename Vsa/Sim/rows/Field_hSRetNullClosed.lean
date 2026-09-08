import Vsa.Sim.HelperCallNull
import Vsa.Sim.HelperCallSites
import Vsa.Sim.rows.RetSlotCopy

/-!
# `Field_hSRetNullClosed` — the null return, closed on the helper-call layer

`ret;` (`0x80004120`: `ld a2,8(s0); beqz a2` taken into the bridge
`0x800042f0`: `addi a0,sp,16; jal value_null; j 0x80004138`) composes only
parametric pieces: the prologue to the arm state, the `HelperCall` instance
parked at `value_null`, the `value_null` adapter, the rejoin route, and the
shared retslot copy and status-3 epilogue (`retSlotResume`).
-/

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

-- The `.ret none` path shares the arm head with the value return; the taken
-- branch leaves the child dispatch for the null bridge.
#derive_case retNullBridgeSeg chain
  [(0x80004120#64, 0x00843603#32)]  -- discipline: allow(R10-exec-evalchild-arm) the `.ret none` bridge shares the arm head; the branch is TAKEN, there is no child
    terminator ⟨0x80004124#64, 0x1c060663#32, 0x63#8, 0x06#8, 0x06#8, 0x1c#8,
      .br bop.BEQ true, 12, 0, 0x01cc#13, 0#21, 0#12⟩
  ;;
  [(0x800042f0#64, 0x01010513#32)]  -- discipline: allow(R12-helper-call-arm) the HelperCall instance's own prefix

/-- The null bridge of the return arm. -/
def retNullCall : HelperCall :=
  { headPC := 0x80004120#64
    seg := retNullBridgeSeg
    jalPC := 0x800042f4#64
    jalImm := 0x1fe4f8#21
    entry := 0x800027ec#64 }

theorem retNullCall_cert : retNullCall.Cert where
  ret_align := by decide
  ret_clean := by decide
  jal_tgt := by decide
  avoid_abi := by change WrChainAvoidAbi retNullBridgeSeg; decide
  jal_site := fun σ i u vmi hG hpc hmi hmem hi =>
    site_800042f4_hc σ i u _ vmi hG hpc hmi hmem rfl hi

/-- Chain facts of the bridge: the null expression pointer takes the branch. -/
theorem retNullBridge_facts
    {m : Mem} {SL : StackLayout} {A : Arena} {sp aRet aStmt : BitVec 64}
    (hg : ExecGround m SL A sp aRet aStmt.toNat (.ret none))
    (hcode : Exec_stmtLoaded m)
    (hnull : read64 m (aStmt.toNat + 8) = some 0)
    (esp aInterp aEnv : BitVec 64) :
    ChainFacts m m (EvalChildArm.regs esp aStmt aInterp aRet aEnv)
      [EvalChildArm.wordLds8 m (aStmt.toNat + 8)] retNullBridgeSeg := by
  have hzero := EvalChildArm.bytesVal_ld_wordLds m (aStmt.toNat + 8) 0#64 hnull
  unfold retNullBridgeSeg ChainFacts
  chain_facts hcode with "Vsa.Sim.Code.exec_stmt_at_"
  · exact hg.node_ld_facts (0x008#12) 8 (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  · change (bytesVal MKind.ld (EvalChildArm.wordLds8 m (aStmt.toNat + 8)) == 0#64) = true
    rw [hzero]
    decide

-- After `value_null` returns: jump to the shared copy head.
#derive_case retNullRejoinSeg chain
  []
    terminator ⟨0x800042f8#64, 0xe41ff06f#32, 0x6f#8, 0xf0#8, 0x1f#8, 0xe4#8,
      .j, 0, 0, 0#13, 0x1ffe40#21, 0#12⟩

theorem retNullRejoin_facts (m : Mem) (a0 esp s0 s1 s2 s3 : BitVec 64)
    (hcode : Exec_stmtLoaded m) :
    ChainFacts m m (TruthyCopy.routeL a0 esp retNullCall.retPC s0 s1 s2 s3) [] retNullRejoinSeg := by
  unfold retNullRejoinSeg ChainFacts
  chain_facts hcode with "Vsa.Sim.Code.exec_stmt_at_"

/-- `ret;`: the bridge, the copy, and the epilogue, from the statement entry. -/
theorem retNull_run
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) :
    Triple
      (ExecEntry g N A SL φf φc st d env (.ret none) sp r aInterp aStmt aEnv aRet m0)
      (ExecExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st (.ret .null) sp r aRet m0) := by
  intro cfg hEntry
  obtain ⟨cA, ment, hsA, hA⟩ := armState_of_entry_kind 6 execArmRet (by decide) rfl (by decide)
    (fun _ _ h => by cases h with | retNone hk _ => exact hk) hEntry
  have F := hA.frameFacts
  obtain ⟨h176, hesp, hSLlo, hSLhi, hal⟩ := F.geom
  have hram := F.stack_ram
  have hwin := F.stack_win
  have hnull : read64 ment (aStmt.toNat + 8) = some 0 := by
    cases hA.stmt with | retNone _ h => exact h
  -- park at `value_null`
  obtain ⟨cP, hsP, hP⟩ := retNullCall.parked_of_armState retNullCall_cert hA
    [EvalChildArm.wordLds8 ment (aStmt.toNat + 8)]
    (by change ChainOK 0x80004120#64 [2, 8, 9, 18, 19] retNullBridgeSeg; decide) rfl
    (by change KeysOK [10, 12, 2, 8, 9, 18, 19]; decide)
    (by change ∀ n ∈ [10, 12, 2, 8, 9, 18, 19], n ≠ 1; decide)
    (by show Exec_stmtLoaded (writeLog ment []); exact hA.code)
    (retNullBridge_facts hA.ground hA.code hnull _ _ _)
  -- the helper
  have hbuf : (TruthyCopy.dst (sp - 176#64)).toNat = (sp - 176#64).toNat + 16 :=
    TruthyCopy.dst_toNat (sp - 176#64) (by omega)
  have hregion : NullRegion (TruthyCopy.dst (sp - 176#64)) := by
    refine { align := ?_, lo := ?_, hi := ?_, win := ?_, code_disjoint := ?_ }
    · rw [hbuf]; omega
    · rw [hbuf]; omega
    · rw [hbuf]; omega
    · rw [hbuf]; omega
    · rw [hbuf]; rcases hA.ground.eval_call.vi_stack with hd | hd <;> omega
  have hloaded : Value_nullLoaded ment := by
    obtain ⟨_, _, _, _, hNbs, _⟩ := hA.ground.eval_call.pins ment (fun _ _ => rfl)
    exact hNbs.null_code
  obtain ⟨cN, hsN, hRet, hv⟩ := retNullCall.nullReturn_of_parked retNullCall_cert rfl hP
    (buf := TruthyCopy.dst (sp - 176#64)) rfl rfl rfl rfl rfl rfl hregion
    (by show Value_nullLoaded (writeLog ment []); exact hloaded) N φc
  -- the frame after the helper
  have hfoot : ∀ k, ((TruthyCopy.dst (sp - 176#64)).toNat ≤ k ∧
      k < (TruthyCopy.dst (sp - 176#64)).toNat + 24) → SL.lo ≤ k ∧ k < sp.toNat - 40 := by
    intro k hk
    rw [hbuf, hesp] at hk
    omega
  have hframeN : ∀ k, ¬ ((TruthyCopy.dst (sp - 176#64)).toNat ≤ k ∧
      k < (TruthyCopy.dst (sp - 176#64)).toNat + 24) → cN.σ.mem[k]? = ment[k]? :=
    fun k hk => hRet.mem_frame k hk
  have hextN : MemExtends ment cN.σ.mem := hRet.mem_extends
  have FN := F.afterStackHelper hfoot hframeN hextN
  -- rejoin at the copy head
  obtain ⟨cR, hsR, hHead⟩ := TruthyCopy.route_of_ready retNullRejoinSeg 0x80004138#64 []
    hRet.ready
    (by change ChainOK retNullCall.retPC [10, 2, 1, 8, 9, 18, 19] retNullRejoinSeg; decide)
    rfl
    (by change WrChainAvoids TruthyCopy.abiButS0 retNullRejoinSeg; decide)
    (retNullRejoin_facts cN.σ.mem _ _ _ _ _ _ FN.code)
  have hRR := hHead.toRouteReady rfl rfl rfl rfl rfl rfl rfl rfl FN.s0
  -- the copy and the epilogue
  have hag : AgreeP (fun k => sp.toNat - 40 ≤ k ∧ k < sp.toNat) ment cN.σ.mem :=
    fun k hk => (hframeN k (fun hf => by have := hfoot k hf; omega)).symm
  have hv' : ∃ φcv, PhiExtends φc φcv st.store.closures.size ∧
      ValueRepr cN.σ.mem N φcv ((sp - 176#64).toNat + 16) .null :=
    ⟨φc, PhiExtends.refl φc _, hbuf ▸ hv⟩
  have hpay : PayloadOffWindow cN.σ.mem ((sp - 176#64).toNat + 16) aRet.toNat .null :=
    PayloadOffWindow.of_no_payload (fun _ h => by simp [Vsa.Sim.ValuePayload] at h)
  have hframe0 : ∀ a, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      (aRet.toNat ≤ a ∧ a < aRet.toNat + 24) ∨ cN.σ.mem[a]? = m0[a]? := by
    intro a hstk _
    right
    rw [hframeN a (fun hf => hstk ⟨(hfoot a hf).1, by have := (hfoot a hf).2; omega⟩)]
    exact hA.mem_frame a hstk
  obtain ⟨cD, hsD, hExit⟩ := retSlotResume F hag FN.code hRR (PhiExtends.refl φf _)
    (PhiExtends.refl φc _) FN.store_survives hv' hpay (hA.mem_extends.trans hextN) hframe0
    hA.out
  exact ⟨cD, hsA.trans (hsP.trans (hsN.trans (hsR.trans hsD))), hExit⟩

/-- Concrete supplier for the null-return residual. -/
theorem ScaffoldRows.field_hSRetNull : ∀ st d env, Rows.RetNullResid st d env :=
  fun st d env g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 =>
    retNull_run g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet m0

#print axioms retNullCall_cert
#print axioms retNull_run
#print axioms ScaffoldRows.field_hSRetNull

end Vsa.Sim
