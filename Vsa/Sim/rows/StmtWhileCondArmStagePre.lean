import Vsa.Sim.ArmSegSplitExecEval
import Vsa.Sim.EvalChildFieldCombinator
import Vsa.Sim.ExecBrkCont
import Vsa.Sim.ExecCondArmSites

/-!
# `StmtWhileCondArmStagePre` — the exec-`whileStmt cnd b`-arm-head → `ExecJalPreBundle`
cut (Wave 41)

The `stmtWhileCond` twin of the wave-40 model `StmtExprArmStagePre`.  The
`.whileStmt cnd b` arm (`0x8000403c`) head is `ld a2,8(s0); mv a3,s3; addi a0,sp,80;
mv a1,s1; jal eval_expr@0x80003164` — FIVE instructions (no null-check branch; the
`addi` is BEFORE the final `mv a1,s1`, and the sret buffer is `sp+80`).  Everything
else is the model.  Reuses the `_es` site battery `site_8000403c..4c` from
`ExecCondArmSites`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no `maxHeartbeats` bump.
Axioms of every theorem ⊆ {propext, Classical.choice, Quot.sound}.
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
open Vsa.Sim.ApproxArmReseat

namespace Vsa.Sim

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
set_option linter.unusedVariables false

-- discipline: allow(R7-conj-tower-def) the ∃-towers here are the ESTABLISHED landing
-- bundle `ExecJalPreBundle` + the exec-arm-head entry bundle mirroring the landed
-- `blockB_stmtExpr_stagePre` `hpre`; consumed through `stmtWhileCond_field_of_dispatch`.

/-! ## §1. `blockB_stmtWhileCond_stagePre` — the exec-`whileStmt` arm-head cut -/

/-- **The exec-`whileStmt cnd b` arm-head → `ExecJalPreBundle` cut.**  From the
`ExecArmEntryK`-at-`0x8000403c` bundle plus the cond-expr payload and eval-side code /
wide-window survival, the four head steps `ld a2,8(s0)`/`mv a3,s3`/`addi a0,sp,80`/
`mv a1,s1` reach the `jal eval_expr` PC `0x8000404c` with the sub-call staged,
satisfying `ExecJalPreBundle cnd` with the ghost `sp := esp+1088`. -/
theorem blockB_stmtWhileCond_stagePre
    (g gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (e : Expr)
    (sp r aInterp aStmt aEnv aRet aExprChild : BitVec 64)
    (v8 v9 v18 v19 : BitVec 64)
    (out0 : Array String) (m0 ment : Mem)
    (c : Config)
    (hpre :
        ExecArmEntryK g N A SL φf φc st (0x8000403c#64)
          sp r aInterp aStmt aEnv aRet v8 v9 v18 v19 out0 m0 ment c ∧
        read64 ment (aStmt.toNat + 8) = some aExprChild.toNat ∧
        ExprRepr ment aExprChild.toNat e ∧
        aStmt.toNat % 8 = 0 ∧
        0x80000000 ≤ aStmt.toNat ∧ aStmt.toNat + 16 ≤ 0x100000000 ∧
        (aStmt.toNat + 16 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aStmt.toNat) ∧
        Eval_exprLoaded ment ∧ Value_intLoaded ment ∧ IntSlotPinned ment ∧
        (∀ m' : Mem,
          (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) →
            ¬ (aInterp.toNat ≤ k ∧ k < aInterp.toNat + 24) →
            ment[k]? = m'[k]?) →
          StoreRepr m' N A φf φc st.store) ∧
        aExprChild.toNat % 8 = 0 ∧
        0x80000000 ≤ aExprChild.toNat ∧ aExprChild.toNat + 16 ≤ 0x100000000 ∧
        tohostAddr + 16 ≤ aExprChild.toNat ∧
        (aExprChild.toNat + 16 ≤ SL.lo ∨ (sp.toNat - 176) ≤ aExprChild.toNat) ∧
        SL.lo + 3264 ≤ sp.toNat - 176 ∧
        sp.toNat % 16 = 0 ∧
        0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000 ∧ tohostAddr + 16 ≤ SL.lo ∧
        ((sp.toNat - 176) + 1088 ≤ SL.hi) ∧
        (((sp.toNat - 176) + 1088) ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo) ∧
        ((0x8000281c : Nat) ≤ SL.lo ∨ ((sp.toNat - 176) + 1088) ≤ 0x8000280c) ∧
        ((0x80019f58 : Nat) + 4 ≤ SL.lo ∨ ((sp.toNat - 176) + 1088) ≤ 0x80019f58) ∧
        (A.hi ≤ SL.lo ∨ (sp.toNat - 176) + 1088 ≤ A.lo) ∧
        (A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo) ∧
        (∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = gpre R) ∧
        (∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w) ∧
        -- ITEM ZERO B1: the child expression's budget at the statement
        -- frame `sp - 176`, `.fn`-bodies bound, store-bodies invariant.
        StackOK SL (sp - 176#64)
          (e.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget e = true ∧
        Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget) :
    LandedN 4 c (fun c' => ExecJalPreBundle e c' st d env) := by
  obtain ⟨hArm, hpay, hExprChild, hstmtAl, hstmtLo, hstmtRam, hstmtWin,
    hEvCode, hViInt, hViSlot, hStoreSurvJ,
    hopAl, hopLo, hopHi, hopWin, hopStk, hsproom, hsp16pre,
    hSLlo, hSLhiRam, hSLwin,
    hjspSLhi, hcodeStkJ, htableStkJ1, htableStkJ2, harenaStkJ, harenaCode,
    hgframe, hg8, hg18, hstackBudget, hexprBodies, hstoreBodies⟩ := hpre
  obtain ⟨hG, htick, hpc, hs0, hs1, hs3, hs2, hsp, hra, ⟨vmi, hmi⟩,
    hout, houtStr, hmem, hcode, hstore,
    hslotRa, hslotS0, hslotS1, hslotS2, hslotS3,
    hgx8, hgx9, hgx18, hgx19, hgx2, hframeK, hmemframeK,
    hsp176, hsphi, hsplo, hspwin, hsp8, hraAl⟩ := hArm
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hespN : (sp - 176#64).toNat = sp.toNat - 176 := by
    rw [BitVec.toNat_sub]
    have h176 : (176#64 : BitVec 64).toNat = 176 := by decide
    rw [h176]; have := sp.isLt; omega
  have h8 : (sign_extend (m := 64) (0x008#12) : BitVec 64) = 8#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  have haddr8 : (aStmt + sign_extend (m := 64) (0x008#12)).toNat = aStmt.toNat + 8 := by
    rw [h8, BitVec.toNat_add]; have hv : (8#64 : BitVec 64).toNat = 8 := by decide
    rw [hv]; omega
  obtain ⟨pb0, pb1, pb2, pb3, pb4, pb5, pb6, pb7, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hpsext⟩ :=
    spill_roundtrip_ee ment (aStmt.toNat + 8) aExprChild hpay
  -- sub-sret buffer addr = esp + 80
  have hsub80 : ((sp - 176#64) + sign_extend (m := 64) (0x050#12)).toNat = (sp.toNat - 176) + 80 := by
    have h80 : (sign_extend (m := 64) (0x050#12) : BitVec 64) = 80#64 := by
      apply BitVec.eq_of_toNat_eq; decide
    rw [h80, BitVec.toNat_add]; have hv : (80#64 : BitVec 64).toNat = 80 := by decide
    rw [hv, hespN]; omega
  -- ============ 0x8000403c: ld a2,8(s0) → x12 := aExprChild ============
  obtain ⟨σ1, i1, hs1', hi1, hG1, hmem1, hobs1⟩ :=
    site_8000403c_es c.σ c.tick c.steps (0x8000403c#64) vmi aStmt pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7
      hG hpc hmi hs0 (hmem ▸ hcode) rfl
      (by rw [haddr8]; omega) (by rw [haddr8]; omega)
      (by rw [haddr8, htoh]; rcases hstmtWin with h | h
          · left; rw [htoh] at h; omega
          · right; rw [htoh] at h; omega) (by rw [haddr8]; omega)
      (by rw [haddr8, hmem]; exact hp0) (by rw [haddr8, hmem]; exact hp1)
      (by rw [haddr8, hmem]; exact hp2) (by rw [haddr8, hmem]; exact hp3)
      (by rw [haddr8, hmem]; exact hp4) (by rw [haddr8, hmem]; exact hp5)
      (by rw [haddr8, hmem]; exact hp6) (by rw [haddr8, hmem]; exact hp7) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1'
  have hmem1e : σ1.mem = ment := by rw [hmem1]; exact hmem
  have hpc1 : σ1.regs.get? Register.PC = some (0x80004040#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x8000403c#64) 4 = (0x80004040#64 : BitVec 64) from by decide] at this
  have hx12_1 : σ1.regs.get? Register.x12 = some aExprChild := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hpsext] at this
  have hs1_1 : σ1.regs.get? Register.x9 = some aInterp := obs_alu_other' hobs1 Register.x9 (by decide) hs1
  have hs3_1 : σ1.regs.get? Register.x19 = some aEnv := obs_alu_other' hobs1 Register.x19 (by decide) hs3
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp - 176#64) := obs_alu_other' hobs1 Register.x2 (by decide) hsp
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hout1 : σ1.sailOutput = out0 := by rw [hobs1.out, sailOutput_sigmaPost_alu]; exact hout
  have hcode1 : Exec_stmtLoaded σ1.mem := by rw [hmem1e]; exact hcode
  -- ============ 0x80004040: mv a3,s3 (addi x13,x19,0) → x13 := aEnv ============
  obtain ⟨σ2, i2, hs2', hi2, hG2, hmem2, hobs2⟩ :=
    site_80004040_es σ1 i1 (c.steps + 1) (0x80004040#64) vmi1 aEnv hG1 hpc1 hmi1 hs3_1 hcode1 rfl hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2'
  have hmem2e : σ2.mem = ment := by rw [hmem2]; exact hmem1e
  have hpc2 : σ2.regs.get? Register.PC = some (0x80004044#64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x80004040#64) 4 = (0x80004044#64 : BitVec 64) from by decide] at this
  have hx13_2 : σ2.regs.get? Register.x13 = some (aEnv + sign_extend (m := 64) (0x000#12)) :=
    obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hs1_2 : σ2.regs.get? Register.x9 = some aInterp := obs_alu_other' hobs2 Register.x9 (by decide) hs1_1
  have hx12_2 : σ2.regs.get? Register.x12 = some aExprChild := obs_alu_other' hobs2 Register.x12 (by decide) hx12_1
  have hsp_2 : σ2.regs.get? Register.x2 = some (sp - 176#64) := obs_alu_other' hobs2 Register.x2 (by decide) hsp_1
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hout2 : σ2.sailOutput = out0 := by rw [hobs2.out, sailOutput_sigmaPost_alu]; exact hout1
  have hcode2 : Exec_stmtLoaded σ2.mem := by rw [hmem2e]; exact hcode
  -- ============ 0x80004044: addi a0,sp,80 → x10 := esp + 80 ============
  obtain ⟨σ3, i3, hs3', hi3, hG3, hmem3, hobs3⟩ :=
    site_80004044_es σ2 i2 (c.steps + 1 + 1) (0x80004044#64) vmi2 (sp - 176#64) hG2 hpc2 hmi2 hsp_2 hcode2 rfl hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3'
  have hmem3e : σ3.mem = ment := by rw [hmem3]; exact hmem2e
  have hpc3 : σ3.regs.get? Register.PC = some (0x80004048#64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x80004044#64) 4 = (0x80004048#64 : BitVec 64) from by decide] at this
  have hx10_3 : σ3.regs.get? Register.x10 = some ((sp - 176#64) + sign_extend (m := 64) (0x050#12)) :=
    obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hs1_3 : σ3.regs.get? Register.x9 = some aInterp := obs_alu_other' hobs3 Register.x9 (by decide) hs1_2
  have hx12_3 : σ3.regs.get? Register.x12 = some aExprChild := obs_alu_other' hobs3 Register.x12 (by decide) hx12_2
  have hx13_3 : σ3.regs.get? Register.x13 = some (aEnv + sign_extend (m := 64) (0x000#12)) :=
    obs_alu_other' hobs3 Register.x13 (by decide) hx13_2
  have hsp_3 : σ3.regs.get? Register.x2 = some (sp - 176#64) := obs_alu_other' hobs3 Register.x2 (by decide) hsp_2
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hout3 : σ3.sailOutput = out0 := by rw [hobs3.out, sailOutput_sigmaPost_alu]; exact hout2
  have hcode3 : Exec_stmtLoaded σ3.mem := by rw [hmem3e]; exact hcode
  -- ============ 0x80004048: mv a1,s1 (addi x11,x9,0) → x11 := aInterp ============
  obtain ⟨σ4, i4, hs4', hi4, hG4, hmem4, hobs4⟩ :=
    site_80004048_es σ3 i3 (c.steps + 1 + 1 + 1) (0x80004048#64) vmi3 aInterp hG3 hpc3 hmi3 hs1_3 hcode3 rfl hi3
  have hstep4 : Step ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ := hs4'
  have hmem4e : σ4.mem = ment := by rw [hmem4]; exact hmem3e
  have hpc4 : σ4.regs.get? Register.PC = some (0x8000404c#64) := by
    have := obs_alu_pc hobs4
    rwa [show BitVec.addInt (0x80004048#64) 4 = (0x8000404c#64 : BitVec 64) from by decide] at this
  have hx11_4 : σ4.regs.get? Register.x11 = some (aInterp + sign_extend (m := 64) (0x000#12)) :=
    obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx10_4 : σ4.regs.get? Register.x10 = some ((sp - 176#64) + sign_extend (m := 64) (0x050#12)) :=
    obs_alu_other' hobs4 Register.x10 (by decide) hx10_3
  have hx12_4 : σ4.regs.get? Register.x12 = some aExprChild := obs_alu_other' hobs4 Register.x12 (by decide) hx12_3
  have hx13_4 : σ4.regs.get? Register.x13 = some (aEnv + sign_extend (m := 64) (0x000#12)) :=
    obs_alu_other' hobs4 Register.x13 (by decide) hx13_3
  have hsp_4 : σ4.regs.get? Register.x2 = some (sp - 176#64) := obs_alu_other' hobs4 Register.x2 (by decide) hsp_3
  obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
  have hout4 : σ4.sailOutput = out0 := by rw [hobs4.out, sailOutput_sigmaPost_alu]; exact hout3
  have hx11_val : σ4.regs.get? Register.x11 = some aInterp := by
    rw [hx11_4, sext_zero, BitVec.add_zero]
  have hx13_val : σ4.regs.get? Register.x13 = some aEnv := by
    rw [hx13_4, sext_zero, BitVec.add_zero]
  have abi_ne' : ∀ {X R : Register}, AbiPreserved X = false → AbiPreserved R = true →
      (X == R) = false := by
    intro X R hX hR
    rcases hXR : (X == R) with _ | _
    · rfl
    · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hR; exact absurd hR (by decide)
  have hframe4 : ∀ R : Register, AbiPreservedNoise R → σ4.regs.get? R = gpre R := by
    intro R hR
    obtain ⟨hab, hpcR, hnpcR, hmiR, hmiiR, hmcR, hmtR, hmipR⟩ := hR
    have h12R : (Register.x12 == R) = false := abi_ne' (by decide) hab
    have h13R : (Register.x13 == R) = false := abi_ne' (by decide) hab
    have h10R : (Register.x10 == R) = false := abi_ne' (by decide) hab
    have h11R : (Register.x11 == R) = false := abi_ne' (by decide) hab
    have f1 : σ1.regs.get? R = c.σ.regs.get? R :=
      (hobs1.1 R hmcR hmtR hmipR).trans
        (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR h12R hnpcR hmiiR)
    have f2 : σ2.regs.get? R = σ1.regs.get? R :=
      (hobs2.1 R hmcR hmtR hmipR).trans
        (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR h13R hnpcR hmiiR)
    have f3 : σ3.regs.get? R = σ2.regs.get? R :=
      (hobs3.1 R hmcR hmtR hmipR).trans
        (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR h10R hnpcR hmiiR)
    have f4 : σ4.regs.get? R = σ3.regs.get? R :=
      (hobs4.1 R hmcR hmtR hmipR).trans
        (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR h11R hnpcR hmiiR)
    rw [f4, f3, f2, f1]; exact hgframe R ⟨hab, hpcR, hnpcR, hmiR, hmiiR, hmcR, hmtR, hmipR⟩
  -- ============ land at σ4 (the jal PC 0x8000404c) as `ExecJalPreBundle e` ==========
  have hjspN : ((sp - 176#64) + 1088#64).toNat = (sp.toNat - 176) + 1088 := by
    rw [BitVec.toNat_add]; have hv : (1088#64 : BitVec 64).toNat = 1088 := by decide
    rw [hv, hespN]; omega
  have hjspcancel : ((sp - 176#64) + 1088#64) - 1088#64 = sp - 176#64 := by
    rw [BitVec.add_sub_cancel]
  have hx2jsp : σ4.regs.get? Register.x2 = some (((sp - 176#64) + 1088#64) - 1088#64) := by
    rw [hjspcancel]; exact hsp_4
  refine ⟨4, ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩, by omega,
    StepsN.succ hstep1 (StepsN.succ hstep2 (StepsN.succ hstep3 (StepsN.succ hstep4 (StepsN.zero _)))), ?_⟩
  refine ⟨gpre, N, A, SL, φf, φc, (0x8000404c#64), (0x80004050#64), (0x1ff118#21),
    (sp - 176#64) + 1088#64, r, aInterp, (sp - 176#64) + sign_extend (m := 64) (0x050#12),
    aInterp, aExprChild, v8, v9, v18, out0, ment, ?_, ?_, ?_, ?_,
    hG4, hi4, hpc4, hx10_4, ?_, hx11_val, hx12_4, hx2jsp, ⟨vmi4, hmi4⟩, hout4, ?_,
    hmem4e, ?_, hEvCode, hViInt, hViSlot, ?_, ?_, ?_, hframe4, ⟨hg8, hg18⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- hjaltgt
  · apply BitVec.eq_of_toNat_eq; simp only [evalExprEntry]; decide
  -- hlink
  · apply BitVec.eq_of_toNat_eq; decide
  -- retAl
  · decide
  -- hjalSite
  · intro σ i u vmiσ hGσ hpcσ hmiσ hcodeσ hiσ
    exact site_8000404c_es σ i u (0x8000404c#64) vmiσ hGσ hpcσ hmiσ hcodeσ rfl hiσ
  -- x9 = sret := aInterp
  · exact obs_alu_other' hobs4 Register.x9 (by decide) hs1_3
  -- String.join out0.toList = st.out
  · exact houtStr
  -- Exec_stmtLoaded ment
  · exact hcode
  -- ExprRepr ment aExprChild e
  · exact hExprChild
  -- StoreRepr ment
  · exact hstore
  -- store_survives (wave 47e: WIDENED `[SL.lo, SL.hi)` footprint end-to-end)
  · intro m' hag
    refine hStoreSurvJ m' (fun k hk1 hk2 => ?_)
    exact hag k hk1 hk2
  -- aOperand % 8 = 0
  · exact hopAl
  -- 0x80000000 ≤ aOperand
  · exact hopLo
  -- aOperand + 16 ≤ 0x100000000
  · exact hopHi
  -- tohostAddr + 16 ≤ aOperand
  · exact hopWin
  -- aOperand + 16 ≤ SL.lo ∨ jsp - 1088 ≤ aOperand
  · rcases hopStk with h | h
    · left; exact h
    · right; rw [show ((sp - 176#64) + 1088#64).toNat - 1088 = sp.toNat - 176 by rw [hjspN]; omega]; exact h
  -- subsret % 8 = 0
  · rw [hsub80]; omega
  -- jsp - 1088 ≤ subsret
  · rw [hsub80, show ((sp - 176#64) + 1088#64).toNat - 1088 = sp.toNat - 176 by rw [hjspN]; omega]; omega
  -- subsret + 24 ≤ jsp - 32
  · rw [hsub80, hjspN]; omega
  -- SL.lo + 3264 ≤ jsp
  · rw [hjspN]; omega
  -- jsp ≤ SL.hi
  · rw [hjspN]; exact hjspSLhi
  -- jsp % 16 = 0
  · rw [hjspN]; omega
  -- 0x80000000 ≤ SL.lo
  · exact hSLlo
  -- SL.hi ≤ 0x100000000
  · exact hSLhiRam
  -- tohostAddr + 16 ≤ SL.lo
  · exact hSLwin
  -- jsp ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo
  · rcases hcodeStkJ with h | h
    · left; rw [hjspN]; exact h
    · right; exact h
  -- (0x8000281c ≤ SL.lo ∨ jsp ≤ 0x8000280c)
  · rcases htableStkJ1 with h | h
    · left; exact h
    · right; rw [hjspN]; exact h
  -- (0x80019f58 + 4 ≤ SL.lo ∨ jsp ≤ 0x80019f58)
  · rcases htableStkJ2 with h | h
    · left; exact h
    · right; rw [hjspN]; exact h
  -- (A.hi ≤ SL.lo ∨ jsp ≤ A.lo)
  · rcases harenaStkJ with h | h
    · left; exact h
    · right; rw [hjspN]; exact h
  -- (A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo)
  · exact ⟨harenaCode,
      (by rw [BitVec.add_sub_cancel]; exact hstackBudget),
      hexprBodies, hstoreBodies⟩

#print axioms blockB_stmtWhileCond_stagePre

/-! ## §2. The `stmtWhileCond` field composer -/

/-- **The stmtWhileCond dispatch residual.** -/
def StmtWhileCondArmDispatch
    (cnd : Expr) (b : Stmt) (st : Vsa.While.St) (d : Nat) (env : Addr) (c : Config) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem),
    ExecEntry g N A SL φf φc st d env (.whileStmt cnd b) sp r aInterp aStmt aEnv aRet m0 c →
    Triple (fun c'' => c'' = c)
      (fun c' => ∃ (gpre : (R : Register) → Option (RegisterType R))
        (aExprChild : BitVec 64) (v8 v9 v18 v19 : BitVec 64) (ment : Mem),
        ExecArmEntryK g N A SL φf φc st (0x8000403c#64)
          sp r aInterp aStmt aEnv aRet v8 v9 v18 v19 c'.σ.sailOutput m0 ment c' ∧
        read64 ment (aStmt.toNat + 8) = some aExprChild.toNat ∧
        ExprRepr ment aExprChild.toNat cnd ∧
        aStmt.toNat % 8 = 0 ∧
        0x80000000 ≤ aStmt.toNat ∧ aStmt.toNat + 16 ≤ 0x100000000 ∧
        (aStmt.toNat + 16 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aStmt.toNat) ∧
        Eval_exprLoaded ment ∧ Value_intLoaded ment ∧ IntSlotPinned ment ∧
        (∀ m' : Mem,
          (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) →
            ¬ (aInterp.toNat ≤ k ∧ k < aInterp.toNat + 24) →
            ment[k]? = m'[k]?) →
          StoreRepr m' N A φf φc st.store) ∧
        aExprChild.toNat % 8 = 0 ∧
        0x80000000 ≤ aExprChild.toNat ∧ aExprChild.toNat + 16 ≤ 0x100000000 ∧
        tohostAddr + 16 ≤ aExprChild.toNat ∧
        (aExprChild.toNat + 16 ≤ SL.lo ∨ (sp.toNat - 176) ≤ aExprChild.toNat) ∧
        SL.lo + 3264 ≤ sp.toNat - 176 ∧ sp.toNat % 16 = 0 ∧
        0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000 ∧ tohostAddr + 16 ≤ SL.lo ∧
        ((sp.toNat - 176) + 1088 ≤ SL.hi) ∧
        (((sp.toNat - 176) + 1088) ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo) ∧
        ((0x8000281c : Nat) ≤ SL.lo ∨ ((sp.toNat - 176) + 1088) ≤ 0x8000280c) ∧
        ((0x80019f58 : Nat) + 4 ≤ SL.lo ∨ ((sp.toNat - 176) + 1088) ≤ 0x80019f58) ∧
        (A.hi ≤ SL.lo ∨ (sp.toNat - 176) + 1088 ≤ A.lo) ∧
        (A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo) ∧
        (∀ R : Register, AbiPreservedNoise R → c'.σ.regs.get? R = gpre R) ∧
        (∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w) ∧
        -- ITEM ZERO B1: the child expression's budget at the statement
        -- frame `sp - 176`, `.fn`-bodies bound, store-bodies invariant.
        StackOK SL (sp - 176#64)
          (cnd.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget cnd = true ∧
        Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget)

/-- **The stmtWhileCond RE-ENTRY dispatch residual** (wave 45, the amended
`SEntryC`'s dispatch-head leg): from `SDispatchC (.whileStmt cnd b)` — a tail
re-dispatch landing this arm from `execStmtDispatchHead` — stage the sub-expr
sub-call.  Supplied upstream by a dispatch-head → arm-head span (the jump-table
half of `execBlockA` re-run from `0x80004014`, no prologue). -/
def StmtWhileCondReentryDispatch
    (cnd : Expr) (b : Stmt) (st : Vsa.While.St) (d : Nat) (env : Addr) (c : Config) : Prop :=
  SDispatchC c st d env (.whileStmt cnd b) →
  LandedN 1 c (fun c' => ExecJalPreBundle cnd c' st d env)

/-- **The stmtWhileCond `viaWhileArm` residual** (wave 45): the while-arm-head
leg of the amended `SEntryC` — the loop-back `bne a0,a5,0x80004034` re-entry.
The ONLY genuinely-while leg (every other arm refutes it by shape); supplied
upstream by the while-arm head span `0x80004034 → jal eval_expr`. -/
def StmtWhileCondViaWhileArm
    (cnd : Expr) (b : Stmt) (st : Vsa.While.St) (d : Nat) (env : Addr) (c : Config) : Prop :=
  SWhileArmC c st d env (.whileStmt cnd b) →
  LandedN 1 c (fun c' => ExecJalPreBundle cnd c' st d env)

/-- **The `EvalChildStages.stmtWhileCond` field, machine-composed (exec twin).** -/
theorem stmtWhileCond_field_of_dispatch
    (cnd : Expr) (b : Stmt) (c : Config) (st : Vsa.While.St) (d : Nat) (env : Addr)
    (hDisp : StmtWhileCondArmDispatch cnd b st d env c)
    (hReentry : StmtWhileCondReentryDispatch cnd b st d env c)
    (hViaWhileArm : StmtWhileCondViaWhileArm cnd b st d env c) :
    SEntryC c st d env (.whileStmt cnd b) →
    LandedN 1 c (fun c' => EEntryC c' st d env cnd) := by
  refine stmtWhileCond_split' cnd b c st d env (fun hSE => ?_)
  rcases hSE with hSE | hRe | hWA
  · -- fresh-call leg (the pre-amendment body)
    obtain ⟨g, N, A, SL, φf, φc, sp, r, aInterp, aStmt, aEnv, aRet, m0, hEntry⟩ := hSE
    obtain ⟨c1, hsteps1, hMid⟩ :=
      hDisp g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 hEntry c rfl
    obtain ⟨gpre, aExprChild, v8, v9, v18, v19, ment, hArm, hpay, hExprChild,
      hstmtAl, hstmtLo, hstmtRam, hstmtWin, hEvCode, hViInt, hViSlot, hStoreSurvJ,
      hopAl, hopLo, hopHi, hopWin, hopStk, hsproom, hsp16pre, hSLlo, hSLhiRam, hSLwin,
      hjspSLhi, hcodeStkJ, htableStkJ1, htableStkJ2, harenaStkJ, harenaCode,
      hgframe, hg8, hg18, hstackBudget, hexprBodies, hstoreBodies⟩ := hMid
    have hcut : LandedN 4 c1 (fun c' => ExecJalPreBundle cnd c' st d env) :=
      blockB_stmtWhileCond_stagePre g gpre N A SL φf φc st d env cnd
        sp r aInterp aStmt aEnv aRet aExprChild v8 v9 v18 v19 c1.σ.sailOutput m0 ment c1
        ⟨hArm, hpay, hExprChild, hstmtAl, hstmtLo, hstmtRam, hstmtWin,
         hEvCode, hViInt, hViSlot, hStoreSurvJ,
         hopAl, hopLo, hopHi, hopWin, hopStk, hsproom, hsp16pre, hSLlo, hSLhiRam, hSLwin,
         hjspSLhi, hcodeStkJ, htableStkJ1, htableStkJ2, harenaStkJ, harenaCode,
         hgframe, hg8, hg18, hstackBudget, hexprBodies, hstoreBodies⟩
    obtain ⟨n1, hn1⟩ := hsteps1.toN
    obtain ⟨m2, c2, hm2, hs2, hpb⟩ := hcut
    exact ⟨n1 + m2, c2, by omega, hn1.trans_add hs2, hpb⟩
  · -- dispatch-head re-entry leg (wave-45 named residual)
    exact hReentry hRe
  · -- while-arm loop-back leg (wave-45 `viaWhileArm` named residual)
    exact hViaWhileArm hWA

#print axioms stmtWhileCond_field_of_dispatch

end Vsa.Sim
