import Vsa.Sim.HelperCallNull
import Vsa.Sim.rows.EnvDefineCall
import Vsa.Sim.rows.ExecRecRows

/-!
# `Field_hSVarNullClosed` — the null declaration on the layer

`var x;` (`0x800040d8`: `ld a2,16(s0); beqz a2` taken into the bridge
`0x800042fc`: `addi a0,sp,104; jal value_null; j 0x800040f0`) composes the
prologue to the arm state, the `HelperCall` instance parked at
`value_null`, the `value_null` adapter, the rejoin route, and the shared
declaration tail (`envDefineTail_run`).  The `env_define` contract is the
one named premise.
-/

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

-- The null declaration shares the arm head with the initialised one; the
-- taken branch leaves the child dispatch for the null bridge.
#derive_case varNullBridgeSeg chain
  [(0x800040d8#64, 0x01043603#32)]  -- discipline: allow(R10-exec-evalchild-arm) the `var x;` bridge shares the arm head; the branch is TAKEN, there is no child
    terminator ⟨0x800040dc#64, 0x22060063#32, 0x63#8, 0x00#8, 0x06#8, 0x22#8,
      .br bop.BEQ true, 12, 0, 0x0220#13, 0#21, 0#12⟩
  ;;
  [(0x800042fc#64, 0x06810513#32)]  -- discipline: allow(R12-helper-call-arm) the HelperCall instance's own prefix

/-- The null bridge of the declaration arm. -/
def varNullCall : HelperCall :=
  { headPC := 0x800040d8#64
    seg := varNullBridgeSeg
    jalPC := 0x80004300#64
    jalImm := 0x1fe4ec#21
    entry := 0x800027ec#64 }

theorem varNullCall_cert : varNullCall.Cert where
  ret_align := by decide
  ret_clean := by decide
  jal_tgt := by decide
  avoid_abi := by change WrChainAvoidAbi varNullBridgeSeg; decide
  jal_site := fun σ i u vmi hG hpc hmi hmem hi =>
    site_80004300_hc σ i u _ vmi hG hpc hmi hmem rfl hi

/-- Chain facts of the bridge: the null initializer pointer takes the branch. -/
theorem varNullBridge_facts
    {m : Mem} {SL : StackLayout} {A : Arena} {sp aRet aStmt : BitVec 64} {x : String}
    (hg : ExecGround m SL A sp aRet aStmt.toNat (.varDecl x none))
    (hcode : Exec_stmtLoaded m)
    (hnull : read64 m (aStmt.toNat + 16) = some 0)
    (esp aInterp aEnv : BitVec 64) :
    ChainFacts m m (EvalChildArm.regs esp aStmt aInterp aRet aEnv)
      [EvalChildArm.wordLds8 m (aStmt.toNat + 16)] varNullBridgeSeg := by
  have hzero := EvalChildArm.bytesVal_ld_wordLds m (aStmt.toNat + 16) 0#64 hnull
  unfold varNullBridgeSeg ChainFacts
  chain_facts hcode with "Vsa.Sim.Code.exec_stmt_at_"
  · exact hg.node_ld_facts (0x010#12) 16 (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  · change (bytesVal MKind.ld (EvalChildArm.wordLds8 m (aStmt.toNat + 16)) == 0#64) = true
    rw [hzero]
    decide

-- After `value_null` returns: jump to the declaration tail.
#derive_case varNullRejoinSeg chain
  []
    terminator ⟨0x80004304#64, 0xdedff06f#32, 0x6f#8, 0xf0#8, 0xdf#8, 0xde#8,
      .j, 0, 0, 0#13, 0x1ffdec#21, 0#12⟩

theorem varNullRejoin_facts (m : Mem) (a0 esp s0 s1 s2 s3 : BitVec 64)
    (hcode : Exec_stmtLoaded m) :
    ChainFacts m m (TruthyCopy.routeL a0 esp varNullCall.retPC s0 s1 s2 s3) [] varNullRejoinSeg := by
  unfold varNullRejoinSeg ChainFacts
  chain_facts hcode with "Vsa.Sim.Code.exec_stmt_at_"

/-- The null buffer of the bridge: the sub-result slot at `esp+104`. -/
def varNullBuf (esp : BitVec 64) : BitVec 64 := esp + sign_extend (m := 64) (0x068#12)

/-- `var x;`: the bridge, the declaration tail, from the statement entry. -/
theorem varNull_run (hED : EnvDefineContract)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (x : String)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) :
    Triple
      (ExecEntry g N A SL φf φc st d env (.varDecl x none) sp r aInterp aStmt aEnv aRet m0)
      (ExecExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        ⟨st.store.define env x .null, st.out⟩ .normal sp r aRet m0) := by
  intro cfg hEntry
  obtain ⟨cA, ment, hsA, hA⟩ := armState_of_entry_kind 1 execArmVarDecl (by decide) rfl
    (by decide) (fun _ _ h => by cases h with | varNull hk _ _ _ => exact hk) hEntry
  have F := hA.frameFacts
  obtain ⟨h176, hesp, hSLlo, hSLhi, hal⟩ := F.geom
  have hram := F.stack_ram
  have hwin := F.stack_win
  have hnull : read64 ment (aStmt.toNat + 16) = some 0 := by
    cases hA.stmt with | varNull _ _ _ h => exact h
  -- park at `value_null`
  obtain ⟨cP, hsP, hP⟩ := varNullCall.parked_of_armState varNullCall_cert hA
    [EvalChildArm.wordLds8 ment (aStmt.toNat + 16)]
    (by change ChainOK 0x800040d8#64 [2, 8, 9, 18, 19] varNullBridgeSeg; decide) rfl
    (by change KeysOK [10, 12, 2, 8, 9, 18, 19]; decide)
    (by change ∀ n ∈ [10, 12, 2, 8, 9, 18, 19], n ≠ 1; decide)
    (by show Exec_stmtLoaded (writeLog ment []); exact hA.code)
    (varNullBridge_facts hA.ground hA.code hnull _ _ _)
  -- the helper
  have hbuf : (varNullBuf (sp - 176#64)).toNat = (sp - 176#64).toNat + 104 :=
    off_toNat _ 0x068#12 104 (by omega) (by rw [hesp]; have := sp.isLt; omega)
      (by apply BitVec.eq_of_toNat_eq; decide)
  have hregion : NullRegion (varNullBuf (sp - 176#64)) := by
    refine { align := ?_, lo := ?_, hi := ?_, win := ?_, code_disjoint := ?_ }
    · rw [hbuf]; omega
    · rw [hbuf]; omega
    · rw [hbuf]; omega
    · rw [hbuf]; omega
    · rw [hbuf]; rcases hA.ground.eval_call.vi_stack with hd | hd <;> omega
  have hloaded : Value_nullLoaded ment := by
    obtain ⟨_, _, _, _, hNbs, _⟩ := hA.ground.eval_call.pins ment (fun _ _ => rfl)
    exact hNbs.null_code
  obtain ⟨cN, hsN, hRet, hv⟩ := varNullCall.nullReturn_of_parked varNullCall_cert rfl hP
    (buf := varNullBuf (sp - 176#64)) rfl rfl rfl rfl rfl rfl hregion
    (by show Value_nullLoaded (writeLog ment []); exact hloaded) N φc
  -- the frame after the helper
  have hfoot : ∀ k, ((varNullBuf (sp - 176#64)).toNat ≤ k ∧
      k < (varNullBuf (sp - 176#64)).toNat + 24) → SL.lo ≤ k ∧ k < sp.toNat - 40 := by
    intro k hk
    rw [hbuf, hesp] at hk
    omega
  have hframeN : ∀ k, ¬ ((varNullBuf (sp - 176#64)).toNat ≤ k ∧
      k < (varNullBuf (sp - 176#64)).toNat + 24) → cN.σ.mem[k]? = ment[k]? :=
    fun k hk => hRet.mem_frame k hk
  have hextN : MemExtends ment cN.σ.mem := hRet.mem_extends
  have FN := F.afterStackHelper hfoot hframeN hextN
  -- rejoin at the declaration tail
  obtain ⟨cR, hsR, hHead⟩ := TruthyCopy.route_of_ready varNullRejoinSeg 0x800040f0#64 []
    hRet.ready
    (by change ChainOK varNullCall.retPC [10, 2, 1, 8, 9, 18, 19] varNullRejoinSeg; decide)
    rfl
    (by change WrChainAvoids TruthyCopy.abiButS0 varNullRejoinSeg; decide)
    (varNullRejoin_facts cN.σ.mem _ _ _ _ _ _ FN.code)
  have hRR := hHead.toRouteReady rfl rfl rfl rfl rfl rfl rfl rfl FN.s0
  -- the declaration tail
  have hframe0 : ∀ a, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      (aRet.toNat ≤ a ∧ a < aRet.toNat + 24) ∨ cN.σ.mem[a]? = m0[a]? := by
    intro a hstk _
    right
    rw [hframeN a (fun hf => hstk ⟨(hfoot a hf).1, by have := (hfoot a hf).2; omega⟩)]
    exact hA.mem_frame a hstk
  obtain ⟨cD, hsD, hExit⟩ := envDefineTail_run hED FN
    (fun _ h => by cases h with | varNull _ hp hc _ => exact ⟨_, hp, hc⟩)
    hRR (PhiExtends.refl φf _) (PhiExtends.refl φc _) (hbuf ▸ hv)
    (PayloadOffWindow.of_no_payload (fun _ h => by simp [Vsa.Sim.ValuePayload] at h))
    (hA.mem_extends.trans hextN) hframe0 hA.out
  exact ⟨cD, hsA.trans (hsP.trans (hsN.trans (hsR.trans hsD))), hExit⟩

/-- Supplier for the null-declaration residual, from the `env_define` contract. -/
theorem ScaffoldRows.field_hSVarNull (hED : EnvDefineContract) :
    ∀ st d env x, Rows.VarNullResid st d env x :=
  fun st d env x g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 =>
    varNull_run hED g N A SL φf φc st d env x sp r aInterp aStmt aEnv aRet m0

#print axioms varNullCall_cert
#print axioms varNull_run
#print axioms ScaffoldRows.field_hSVarNull

end Vsa.Sim
