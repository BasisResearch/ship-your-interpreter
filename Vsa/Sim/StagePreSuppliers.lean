import Vsa.Sim.EvalNegSim
import Vsa.Sim.EvalBinSim
import Vsa.Sim.ArmSegSplitEval
import Vsa.Sim.EntryGroundKit
import Vsa.Sim.BinaryLeftStage

/-!
# Arm entries to staged recursive calls

`blockB_unary_stagePre` stops the unary prefix at its child-call state.
`blockB_binary_leftStagePre` projects `blockB_binary_leftStaged` into the
legacy `JalPreBundle`. The reflected binary prefix retains its four-step
count, fixed call witnesses, memory writes, and register frame.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps StepsN)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim

/-- **The unary arm-head → `JalPreBundle` cut.**  Identical precondition to
`EvalNegSim.blockB_unary` (its `ArmEntryK`-plus-recursive-extras bundle) MINUS the
`hIH`; the two arm-head ALU steps reach the `jal eval_expr` PC `0x800035e8` with the
operand sub-call staged, and that state satisfies `JalPreBundle esub`.  Delivered as
a `LandedN 2` (the two ALU steps) — the divergence-fold consumer only needs `≥ 1`.

This is `blockB_unary` truncated before `armTail_rec`; the pre-bundle it lands at is
precisely the bundle `blockB_unary` fed to `armTail_rec` (lines 349–355), so the
verified `landedN_eentryC_of_preBundle` bridge composes onto it. -/
theorem blockB_unary_stagePre
    (gouter gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (op : UnOp) (esub : Expr)
    (sp r sret aExpr aIn aOperand : BitVec 64) (v8 v9 v18 : BitVec 64)
    (out0 : Array String) (m0 : Mem)
    (c : Config)
    (henvValid : EnvValid st env)
    (henvset : ∃ w19 w20 w21 : BitVec 64,
      gpre Register.x19 = some w19 ∧ gpre Register.x20 = some w20 ∧
      gpre Register.x21 = some w21)
    (hpre : ∃ ment,
        ArmEntryK gouter N A SL φf φc st (0x800035e0#64) UnaryArmCallee (.unary op esub)
          sp r sret aExpr aIn v8 v9 v18 out0 m0 ment c ∧
        c.σ.regs.get? Register.x11 = some aIn ∧
        c.σ.regs.get? Register.x13 = some (BitVec.ofNat 64 (φf env)) ∧
        (∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = gpre R) ∧
        (∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w) ∧
        read64 ment (aExpr.toNat + 16) = some aOperand.toNat ∧
        ExprRepr ment aOperand.toNat esub ∧
        -- WAVE 47i: the child's entry-ground bundle (kit-derived at the sim).
        EvalGround ment SL A (sp - 1088#64)
          ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)) aOperand.toNat esub ∧
        aExpr.toNat + 24 ≤ 0x100000000 ∧
        0x80000000 ≤ aOperand.toNat ∧ aOperand.toNat + 16 ≤ 0x100000000 ∧
        tohostAddr + 16 ≤ aOperand.toNat ∧
        (aOperand.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ aOperand.toNat) ∧
        SL.lo + 3264 ≤ sp.toNat ∧ sp.toNat ≤ SL.hi ∧ sp.toNat % 16 = 0 ∧
        SL.hi ≤ 0x100000000 ∧
        (sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo) ∧
        ((0x8000282c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x800027ec) ∧
        ((0x80019f58 : Nat) + 44 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58) ∧
        (A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo) ∧
        (A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo) ∧
        -- ITEM ZERO B1: the operand's recursion-sound budget at `sp - 1088`, its
        -- `.fn`-bodies bound, and the store-bodies invariant (the amended
        -- `JalPreBundle` tail; mirrors `blockB_unary`'s amended pre).
        StackOK SL (sp - 1088#64)
          (esub.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget esub = true ∧
        Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget) :
    LandedN 2 c (fun c' => JalPreBundle esub c' st d env) := by
  obtain ⟨ment, hArm, hx11, hx13, hgframe, hg8, hg18, hpay, hsubexpr, hground, hexprHi24,
    hopLo, hopHi, hopWin, hopStk,
    hsproom, hspSLhi, hsp16, hSLhiRam,
    hcodeStk, hviStk, htableStk, harenaStk, harenaCode,
    hstackBudget, hexprBodies, hstoreBodies⟩ := hpre
  obtain ⟨hG, htick, hpc, ha0, hs1, ha2, hsp, hra, ⟨vmi, hmi⟩, hout, hmem, hcode, hviCode,
    hexpr, houtStr, hexprLo, hexprHi, hexprWin,
    hslotRa, hslotS0, hslotS1, hslotS2, hmemframe_m0,
    hgx8, hgx9, hgx18, hgx2, hstore, hstoreSurv, hframe,
    hsretAl, hsretLo, hsretHi, hsretWin, hsretVi, hsretStk, hsretEvalCode,
    hsp1088, hsphi, hsplo, hspwin, hsp8, hSLlo, hSLwin, hSLloSp, hraAl,
    _hAEx11, _hAEx8, _hAEx18⟩ := hArm
  have htoh : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨hviInt, hviSlot, hnbs⟩ : Value_intLoaded ment ∧ IntSlotPinned ment ∧ NBSPins ment := hviCode
  have h16 : (sign_extend (m := 64) (0x010#12) : BitVec 64) = 16#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  have haddr16 : (aExpr + sign_extend (m := 64) (0x010#12)).toNat = aExpr.toNat + 16 := by
    rw [h16, BitVec.toNat_add]
    have hv : (16#64 : BitVec 64).toNat = 16 := by decide
    rw [hv]; omega
  obtain ⟨pb0, pb1, pb2, pb3, pb4, pb5, pb6, pb7, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hpsext⟩ :=
    spill_roundtrip_ee ment (aExpr.toNat + 16) aOperand hpay
  -- ============ 0x800035e0: ld a2,16(a2) → x12 := aOperand ============
  obtain ⟨σ1, i1, hs1', hi1, hG1, hmem1, hobs1⟩ :=
    site_800035e0_ee c.σ c.tick c.steps (0x800035e0#64) vmi aExpr pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7
      hG hpc hmi ha2 (hmem ▸ hcode) rfl
      (by rw [haddr16]; omega) (by rw [haddr16]; omega)
      (by rw [haddr16, htoh]; right; omega)
      (by rw [haddr16, hmem]; exact hp0) (by rw [haddr16, hmem]; exact hp1)
      (by rw [haddr16, hmem]; exact hp2) (by rw [haddr16, hmem]; exact hp3)
      (by rw [haddr16, hmem]; exact hp4) (by rw [haddr16, hmem]; exact hp5)
      (by rw [haddr16, hmem]; exact hp6) (by rw [haddr16, hmem]; exact hp7) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1'
  have hmem1e : σ1.mem = ment := by rw [hmem1]; exact hmem
  have hpc1 : σ1.regs.get? Register.PC = some (0x800035e4#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x800035e0#64) 4 = (0x800035e4#64 : BitVec 64) from by decide] at this
  have hx12_1 : σ1.regs.get? Register.x12 = some aOperand := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hpsext] at this
  have ha0_1 : σ1.regs.get? Register.x10 = some sret := obs_alu_other' hobs1 Register.x10 (by decide) ha0
  have hs1_1 : σ1.regs.get? Register.x9 = some sret := obs_alu_other' hobs1 Register.x9 (by decide) hs1
  have hx11_1 : σ1.regs.get? Register.x11 = some aIn := obs_alu_other' hobs1 Register.x11 (by decide) hx11
  have hx13_1 : σ1.regs.get? Register.x13 = some (BitVec.ofNat 64 (φf env)) :=
    obs_alu_other' hobs1 Register.x13 (by decide) hx13
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other' hobs1 Register.x2 (by decide) hsp
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hout1 : σ1.sailOutput = out0 := by
    rw [hobs1.out, sailOutput_sigmaPost_alu]; exact hout
  have hcode1 : Eval_exprLoaded σ1.mem := by rw [hmem1e]; exact hcode
  -- ============ 0x800035e4: addi a0,sp,144 → x10 := (sp-1088) + 144 ============
  obtain ⟨σ2, i2, hs2', hi2, hG2, hmem2, hobs2⟩ :=
    site_800035e4_ee σ1 i1 (c.steps + 1) (0x800035e4#64) vmi1 (sp - 1088#64)
      hG1 hpc1 hmi1 hsp_1 hcode1 rfl hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2'
  have hmem2e : σ2.mem = ment := by rw [hmem2]; exact hmem1e
  have hpc2 : σ2.regs.get? Register.PC = some (0x800035e8#64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x800035e4#64) 4 = (0x800035e8#64 : BitVec 64) from by decide] at this
  have hx10_2 : σ2.regs.get? Register.x10
      = some ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)) :=
    obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hs1_2 : σ2.regs.get? Register.x9 = some sret := obs_alu_other' hobs2 Register.x9 (by decide) hs1_1
  have hx11_2 : σ2.regs.get? Register.x11 = some aIn := obs_alu_other' hobs2 Register.x11 (by decide) hx11_1
  have hx13_2 : σ2.regs.get? Register.x13 = some (BitVec.ofNat 64 (φf env)) :=
    obs_alu_other' hobs2 Register.x13 (by decide) hx13_1
  have hx12_2 : σ2.regs.get? Register.x12 = some aOperand := obs_alu_other' hobs2 Register.x12 (by decide) hx12_1
  have hsp_2 : σ2.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other' hobs2 Register.x2 (by decide) hsp_1
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hout2 : σ2.sailOutput = out0 := by
    rw [hobs2.out, sailOutput_sigmaPost_alu]; exact hout1
  -- the call-point ghost frame: `gpre` survives the two ALU writes (x12, x10)
  have abi_ne' : ∀ {X R : Register}, AbiPreserved X = false → AbiPreserved R = true →
      (X == R) = false := by
    intro X R hX hR
    rcases hXR : (X == R) with _ | _
    · rfl
    · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hR; exact absurd hR (by decide)
  have hframeB : ∀ R : Register, AbiPreservedNoise R → σ2.regs.get? R = gpre R := by
    intro R hR
    obtain ⟨hab, hpcR, hnpcR, hmiR, hmiiR, hmcR, hmtR, hmipR⟩ := hR
    have hR' : AbiPreservedNoise R := ⟨hab, hpcR, hnpcR, hmiR, hmiiR, hmcR, hmtR, hmipR⟩
    have h12R : (Register.x12 == R) = false := abi_ne' (by decide) hab
    have h10R : (Register.x10 == R) = false := abi_ne' (by decide) hab
    have f1 : σ1.regs.get? R = c.σ.regs.get? R :=
      (hobs1.1 R hmcR hmtR hmipR).trans
        (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR h12R hnpcR hmiiR)
    have f2 : σ2.regs.get? R = σ1.regs.get? R :=
      (hobs2.1 R hmcR hmtR hmipR).trans
        (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR h10R hnpcR hmiiR)
    rw [f2, f1]; exact hgframe R hR'
  have hsub944 : ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)).toNat = sp.toNat - 944 :=
    spill_addr sp (0x090#12) 944 (by decide) (by omega) hsp1088
  -- ============ land at σ2 (the jal PC) as `JalPreBundle esub` ============
  refine ⟨2, ⟨σ2, i2, c.steps + 1 + 1⟩, Nat.le_refl _,
    StepsN.succ hstep1 (StepsN.succ hstep2 (StepsN.zero _)), ?_⟩
  · -- the JalPreBundle at σ2: exactly the bundle `blockB_unary` fed to `armTail_rec`.
    exact ⟨gpre, N, A, SL, φf, φc, (0x800035e8#64), (0x800035ec#64), (0x1ffb7c#21),
      sp, r, sret, ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)), aIn, aOperand,
      v8, v9, v18, out0, ment, henvValid,
      (by apply BitVec.eq_of_toNat_eq; simp only [evalExprEntry]; decide),
      (by apply BitVec.eq_of_toNat_eq; decide),
      (by decide),
      (fun σ i u vmiσ hGσ hpcσ hmiσ hcodeσ hiσ =>
        site_800035e8_ee σ i u (0x800035e8#64) vmiσ hGσ hpcσ hmiσ hcodeσ rfl
          (by
            rw [show ((0x800035e8#64 : BitVec 64) + sign_extend (m := 64) (0x1ffb7c#21))
              = (0x80003164#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide]
            decide) hiσ),
      hG2, hi2, hpc2, hx10_2, hs1_2, hx11_2, hx13_2, hx12_2, hsp_2, ⟨vmi2, hmi2⟩, hout2, houtStr,
      hmem2e, hground.valueWordsTotal
        (by rw [hsub944]; omega) (by rw [hsub944]; omega),
      hcode, hviInt, hviSlot, hnbs, hground, hsubexpr, hstore, hstoreSurv, hframeB,
      (by obtain ⟨w19, w20, w21, h19, h20, h21⟩ := henvset
          exact ⟨hg8, hg18, ⟨w19, h19⟩, ⟨w20, h20⟩, ⟨w21, h21⟩⟩),
      hslotRa, hslotS0, hslotS1, hslotS2,
      hopLo, hopHi, hopWin, hopStk,
      (by rw [hsub944]; omega), (by rw [hsub944]; omega), (by rw [hsub944]; omega),
      hsproom, hspSLhi, hsp16, hsphi, hSLlo, hSLhiRam, hSLwin,
      hcodeStk, hviStk, htableStk, harenaStk, harenaCode,
      hstackBudget, hexprBodies, hstoreBodies⟩

#print axioms blockB_unary_stagePre

/-! ## `blockB_binary_leftStagePre` — the binary-left cut (the 10-op payoff)

`EvalBinSim.blockB_binary` shares the kind-generic binary arm head across all TEN
binary operators (`+`/`-`/`*`/`/`/`%`/`==`/`≠`/`<`/`≤`/… — the arm PC `0x800034e8`
is op-independent; the op only matters at the value-combine tail AFTER both operands
return).  Its LEFT operand span is FOUR machine steps — `ld a2,16(a2)` (left operand
pointer) ≫ `addi a0,sp,120` (left sub-buffer `sp-968`) ≫ `sd s3,1048(sp)` ≫
`sd a3,0(sp)` (spilling the env-reg through the left call) — reaching `σ4` at
`0x800034f8`, the LEFT `jal eval_expr` PC, with the left sub-call staged; that state
is fed to `armTail_rec` (lines 512–531 of `EvalBinSim.blockB_binary`).

`blockB_binary_leftStagePre` reuses those four steps and stops at `σ4`, packaging it
as `JalPreBundle el` — so the ONE verified marshalling bridge finishes the left
operand for EVERY binary operator (the `binaryL` field is op-generic).  The
lowered-frame geometry rides through `BinExtras` (`hBE`) exactly as the arm uses it. -/
theorem blockB_binary_leftStagePre
    (gouter gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr)
    (op : BinOp) (el er : Expr)
    (sp r sret aExpr aEnv aLOp aROp aEnvReg : BitVec 64) (v8 v9 v18 v19 : BitVec 64)
    (out0 : Array String) (m0 : Mem)
    (c : Config)
    (hRec : BinaryRecContext gpre φf st env aEnvReg)
    (hpre : ∃ ment,
        ArmEntryK gouter N A SL φf φc st (0x800034e8#64) UnaryArmCallee (.binary op el er)
          sp r sret aExpr aEnv v8 v9 v18 out0 m0 ment c ∧
        BinExtras N A SL el er ment sp sret aExpr aLOp aROp ∧
        c.σ.regs.get? Register.x11 = some aEnv ∧
        c.σ.regs.get? Register.x13 = some aEnvReg ∧
        aEnvReg = BitVec.ofNat 64 (φf env) ∧
        c.σ.regs.get? Register.x19 = some v19 ∧
        (∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = gpre R) ∧
        (∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w) ∧
        gpre Register.x8 = some aExpr ∧ gpre Register.x18 = some aEnv ∧
        gpre Register.x19 = some v19 ∧
        read64 ment (aExpr.toNat + 16) = some aLOp.toNat ∧
        ExprRepr ment aLOp.toNat el ∧
        read64 ment (aExpr.toNat + 24) = some aROp.toNat ∧
        ExprRepr ment aROp.toNat er ∧
        MemExtends m0 ment ∧
        -- WAVE 47i: the parent node's entry-ground bundle (pass-through from
        -- `blockA_binaryArm`).
        EvalGround ment SL A sp sret aExpr.toNat (.binary op el er) ∧
        -- ITEM ZERO B1: the LEFT operand's recursion-sound budget at `sp - 1088`,
        -- its `.fn`-bodies bound, and the store-bodies invariant (the amended
        -- `JalPreBundle` tail; mirrors `blockB_binary`'s amended pre).
        StackOK SL (sp - 1088#64)
          (el.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget el = true ∧
        Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget) :
    LandedN 4 c (fun c' => JalPreBundle el c' st d env) := by
  have staged := blockB_binary_leftStaged gouter gpre N A SL φf φc st d env op el er
    sp r sret aExpr aEnv aLOp aROp aEnvReg v8 v9 v18 v19 out0 m0 c hRec hpre
  exact staged.weaken (fun after h =>
    ⟨gpre, N, A, SL, φf, φc, 0x800034f8#64, 0x800034fc#64, 0x1ffc6c#21,
      sp, r, sret, ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)),
      aEnv, aLOp, v8, v9, v18, out0, after.σ.mem, h.call⟩)

#print axioms blockB_binary_leftStagePre

end Vsa.Sim
