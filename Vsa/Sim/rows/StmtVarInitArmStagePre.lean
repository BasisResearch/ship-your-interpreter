import Vsa.Sim.ArmSegSplitExecEval
import Vsa.Sim.EvalChildFieldCombinator
import Vsa.Sim.ExecBrkCont
import Vsa.Sim.Exec_stmtSites3

/-!
# `StmtVarInitArmStagePre` — the exec-`varDecl x (some e)`-arm-head → `ExecJalPreBundle`
cut (Wave 41)

The `stmtVarInit` twin of the wave-40 model `StmtExprArmStagePre`.  The
`.varDecl x (some e)` arm (`0x800040d8`) head is `ld a2,16(s0); beqz a2,…; mv a1,s1;
mv a3,s3; addi a0,sp,104; jal eval_expr@0x80003164` — SIX head instructions (the
`beqz a2` NULL check is NOT taken on the `some e` route: the init operand pointer is a
real expr node, `≥ 0x80000000 > 0`).  Note the `stmt->init` pointer is loaded from
`8(s0)`+8 = OFFSET 16 (`ld a2,16(s0)`), and the sub-sret buffer is `sp+104`.

Frame-shift ghost `JalPreBundle.sp := esp+1088` (`esp := sp-176`), wide-window
`StoreRepr` survival named premise, dead spill facts — all identical to the model.
Reuses the LANDED `_es` site battery `site_800040d8..ec` from `Exec_stmtSites3`.

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
-- `blockB_stmtExpr_stagePre` `hpre`; consumed through `stmtVarInit_field_of_dispatch`.

/-! ## §1. `blockB_stmtVarInit_stagePre` — the exec-`varDecl x (some e)` arm-head cut -/

/-- **The exec-`varDecl x (some e)` arm-head → `ExecJalPreBundle` cut.**  From the
`ExecArmEntryK`-at-`0x800040d8` bundle plus the child-init payload and eval-side code /
wide-window survival, the six head steps
`ld a2,16(s0)`/`beqz a2 (nottaken)`/`mv a1,s1`/`mv a3,s3`/`addi a0,sp,104` reach the
`jal eval_expr` PC `0x800040ec` with the sub-call staged, satisfying
`ExecJalPreBundle e` with the ghost `sp := esp+1088`. -/
theorem blockB_stmtVarInit_stagePre
    (g gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (e : Expr)
    (sp r aInterp aStmt aEnv aRet aExprChild : BitVec 64)
    (v8 v9 v18 v19 : BitVec 64)
    (out0 : Array String) (m0 ment : Mem)
    (c : Config)
    (hpre :
        ExecArmEntryK g N A SL φf φc st (0x800040d8#64)
          sp r aInterp aStmt aEnv aRet v8 v9 v18 v19 out0 m0 ment c ∧
        read64 ment (aStmt.toNat + 16) = some aExprChild.toNat ∧
        ExprRepr ment aExprChild.toNat e ∧
        aStmt.toNat % 8 = 0 ∧
        0x80000000 ≤ aStmt.toNat ∧ aStmt.toNat + 24 ≤ 0x100000000 ∧
        (aStmt.toNat + 24 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aStmt.toNat) ∧
        Eval_exprLoaded ment ∧ Value_intLoaded ment ∧ IntSlotPinned ment ∧ NBSPins ment ∧
        -- WAVE 47i: the eval child's entry-ground bundle (carried like the
        -- eval-side code facts above; NOT derivable from `ExecGround`).
        EvalGround ment SL A (sp - 176#64)
          ((sp - 176#64) + sign_extend (m := 64) (0x068#12)) aExprChild.toNat e ∧
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
        ((0x8000282c : Nat) ≤ SL.lo ∨ ((sp.toNat - 176) + 1088) ≤ 0x800027ec) ∧
        ((0x80019f58 : Nat) + 44 ≤ SL.lo ∨ ((sp.toNat - 176) + 1088) ≤ 0x80019f58) ∧
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
    LandedN 5 c (fun c' => ExecJalPreBundle e c' st d env) := by
  obtain ⟨hArm, hpay, hExprChild, hstmtAl, hstmtLo, hstmtRam, hstmtWin,
    hEvCode, hViInt, hViSlot, hNbsJ, hGroundJ, hStoreSurvJ,
    hopAl, hopLo, hopHi, hopWin, hopStk, hsproom, hsp16pre,
    hSLlo, hSLhiRam, hSLwin,
    hjspSLhi, hcodeStkJ, htableStkJ1, htableStkJ2, harenaStkJ, harenaCode,
    hgframe, hg8, hg18, hstackBudget, hexprBodies, hstoreBodies⟩ := hpre
  obtain ⟨hG, htick, hpc, hs0, hs1, hs3, hs2, hsp, hra, ⟨vmi, hmi⟩,
    hout, houtStr, hmem, hcode, hstore,
    hslotRa, hslotS0, hslotS1, hslotS2, hslotS3,
    hgx8, hgx9, hgx18, hgx19, hgx2, hframeK, hmemframeK,
    hsp176, hsphi, hsplo, hspwin, hsp8, hraAl, hMemExtK⟩ := hArm
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hespN : (sp - 176#64).toNat = sp.toNat - 176 := by
    rw [BitVec.toNat_sub]
    have h176 : (176#64 : BitVec 64).toNat = 176 := by decide
    rw [h176]; have := sp.isLt; omega
  have h16 : (sign_extend (m := 64) (0x010#12) : BitVec 64) = 16#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  have haddr16 : (aStmt + sign_extend (m := 64) (0x010#12)).toNat = aStmt.toNat + 16 := by
    rw [h16, BitVec.toNat_add]; have hv : (16#64 : BitVec 64).toNat = 16 := by decide
    rw [hv]; omega
  obtain ⟨pb0, pb1, pb2, pb3, pb4, pb5, pb6, pb7, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hpsext⟩ :=
    spill_roundtrip_ee ment (aStmt.toNat + 16) aExprChild hpay
  -- sub-sret buffer addr = esp + 104
  have hsub104 : ((sp - 176#64) + sign_extend (m := 64) (0x068#12)).toNat = (sp.toNat - 176) + 104 := by
    have h104 : (sign_extend (m := 64) (0x068#12) : BitVec 64) = 104#64 := by
      apply BitVec.eq_of_toNat_eq; decide
    rw [h104, BitVec.toNat_add]; have hv : (104#64 : BitVec 64).toNat = 104 := by decide
    rw [hv, hespN]; omega
  -- the operand ptr is nonzero, so the beqz is NOT taken
  have hExprNe : (aExprChild == (0#64)) = false := by
    rw [beq_eq_false_iff_ne]
    intro hEq
    rw [hEq] at hopLo
    simp only [BitVec.toNat_ofNat] at hopLo
    omega
  -- ============ 0x800040d8: ld a2,16(s0) → x12 := aExprChild ============
  obtain ⟨σ1, i1, hs1', hi1, hG1, hmem1, hobs1⟩ :=
    site_800040d8_es c.σ c.tick c.steps (0x800040d8#64) vmi aStmt pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7
      hG hpc hmi hs0 (hmem ▸ hcode) rfl
      (by rw [haddr16]; omega) (by rw [haddr16]; omega)
      (by rw [haddr16, htoh]; rcases hstmtWin with h | h
          · left; rw [htoh] at h; omega
          · right; rw [htoh] at h; omega) (by rw [haddr16]; omega)
      (by rw [haddr16, hmem]; exact hp0) (by rw [haddr16, hmem]; exact hp1)
      (by rw [haddr16, hmem]; exact hp2) (by rw [haddr16, hmem]; exact hp3)
      (by rw [haddr16, hmem]; exact hp4) (by rw [haddr16, hmem]; exact hp5)
      (by rw [haddr16, hmem]; exact hp6) (by rw [haddr16, hmem]; exact hp7) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1'
  have hmem1e : σ1.mem = ment := by rw [hmem1]; exact hmem
  have hpc1 : σ1.regs.get? Register.PC = some (0x800040dc#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x800040d8#64) 4 = (0x800040dc#64 : BitVec 64) from by decide] at this
  have hx12_1 : σ1.regs.get? Register.x12 = some aExprChild := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hpsext] at this
  have hs1_1 : σ1.regs.get? Register.x9 = some aInterp := obs_alu_other' hobs1 Register.x9 (by decide) hs1
  have hs3_1 : σ1.regs.get? Register.x19 = some aEnv := obs_alu_other' hobs1 Register.x19 (by decide) hs3
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp - 176#64) := obs_alu_other' hobs1 Register.x2 (by decide) hsp
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hout1 : σ1.sailOutput = out0 := by rw [hobs1.out, sailOutput_sigmaPost_alu]; exact hout
  have hcode1 : Exec_stmtLoaded σ1.mem := by rw [hmem1e]; exact hcode
  -- ============ 0x800040dc: beqz a2 (NOT taken) → PC := 0x800040e0 ============
  obtain ⟨σ2, i2, hs2', hi2, hG2, hmem2, hobs2⟩ :=
    site_800040dc_nottaken_es σ1 i1 (c.steps + 1) (0x800040dc#64) vmi1 aExprChild
      hG1 hpc1 hmi1 hx12_1 hcode1 rfl hExprNe hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2'
  have hmem2e : σ2.mem = ment := by rw [hmem2]; exact hmem1e
  have hpc2 : σ2.regs.get? Register.PC = some (0x800040e0#64) := by
    have := obs_branch_nottaken_pc hobs2
    rwa [show BitVec.addInt (0x800040dc#64) 4 = (0x800040e0#64 : BitVec 64) from by decide] at this
  have hs1_2 : σ2.regs.get? Register.x9 = some aInterp := obs_branch_nottaken_other' hobs2 Register.x9 (by decide) hs1_1
  have hs3_2 : σ2.regs.get? Register.x19 = some aEnv := obs_branch_nottaken_other' hobs2 Register.x19 (by decide) hs3_1
  have hsp_2 : σ2.regs.get? Register.x2 = some (sp - 176#64) := obs_branch_nottaken_other' hobs2 Register.x2 (by decide) hsp_1
  obtain ⟨vmi2, hmi2⟩ := obs_branch_nottaken_minstret hobs2
  have hout2 : σ2.sailOutput = out0 := by rw [hobs2.out, sailOutput_sigmaPost_branch_nottaken]; exact hout1
  have hcode2 : Exec_stmtLoaded σ2.mem := by rw [hmem2e]; exact hcode
  -- ============ 0x800040e0: mv a1,s1 (addi x11,x9,0) → x11 := aInterp ============
  obtain ⟨σ3, i3, hs3', hi3, hG3, hmem3, hobs3⟩ :=
    site_800040e0_es σ2 i2 (c.steps + 1 + 1) (0x800040e0#64) vmi2 aInterp hG2 hpc2 hmi2 hs1_2 hcode2 rfl hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3'
  have hmem3e : σ3.mem = ment := by rw [hmem3]; exact hmem2e
  have hpc3 : σ3.regs.get? Register.PC = some (0x800040e4#64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x800040e0#64) 4 = (0x800040e4#64 : BitVec 64) from by decide] at this
  have hx11_3 : σ3.regs.get? Register.x11 = some (aInterp + sign_extend (m := 64) (0x000#12)) :=
    obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hs3_3 : σ3.regs.get? Register.x19 = some aEnv := obs_alu_other' hobs3 Register.x19 (by decide) hs3_2
  have hsp_3 : σ3.regs.get? Register.x2 = some (sp - 176#64) := obs_alu_other' hobs3 Register.x2 (by decide) hsp_2
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hout3 : σ3.sailOutput = out0 := by rw [hobs3.out, sailOutput_sigmaPost_alu]; exact hout2
  have hcode3 : Exec_stmtLoaded σ3.mem := by rw [hmem3e]; exact hcode
  -- ============ 0x800040e4: mv a3,s3 (addi x13,x19,0) → x13 := aEnv ============
  obtain ⟨σ4, i4, hs4', hi4, hG4, hmem4, hobs4⟩ :=
    site_800040e4_es σ3 i3 (c.steps + 1 + 1 + 1) (0x800040e4#64) vmi3 aEnv hG3 hpc3 hmi3 hs3_3 hcode3 rfl hi3
  have hstep4 : Step ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ := hs4'
  have hmem4e : σ4.mem = ment := by rw [hmem4]; exact hmem3e
  have hpc4 : σ4.regs.get? Register.PC = some (0x800040e8#64) := by
    have := obs_alu_pc hobs4
    rwa [show BitVec.addInt (0x800040e4#64) 4 = (0x800040e8#64 : BitVec 64) from by decide] at this
  have hx13_4 : σ4.regs.get? Register.x13 = some (aEnv + sign_extend (m := 64) (0x000#12)) :=
    obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx11_4 : σ4.regs.get? Register.x11 = some (aInterp + sign_extend (m := 64) (0x000#12)) :=
    obs_alu_other' hobs4 Register.x11 (by decide) hx11_3
  have hsp_4 : σ4.regs.get? Register.x2 = some (sp - 176#64) := obs_alu_other' hobs4 Register.x2 (by decide) hsp_3
  obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
  have hout4 : σ4.sailOutput = out0 := by rw [hobs4.out, sailOutput_sigmaPost_alu]; exact hout3
  have hcode4 : Exec_stmtLoaded σ4.mem := by rw [hmem4e]; exact hcode
  -- ============ 0x800040e8: addi a0,sp,104 → x10 := esp + 104 ============
  obtain ⟨σ5, i5, hs5', hi5, hG5, hmem5, hobs5⟩ :=
    site_800040e8_es σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x800040e8#64) vmi4 (sp - 176#64) hG4 hpc4 hmi4 hsp_4 hcode4 rfl hi4
  have hstep5 : Step ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ := hs5'
  have hmem5e : σ5.mem = ment := by rw [hmem5]; exact hmem4e
  have hpc5 : σ5.regs.get? Register.PC = some (0x800040ec#64) := by
    have := obs_alu_pc hobs5
    rwa [show BitVec.addInt (0x800040e8#64) 4 = (0x800040ec#64 : BitVec 64) from by decide] at this
  have hx10_5 : σ5.regs.get? Register.x10 = some ((sp - 176#64) + sign_extend (m := 64) (0x068#12)) :=
    obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx11_5 : σ5.regs.get? Register.x11 = some (aInterp + sign_extend (m := 64) (0x000#12)) :=
    obs_alu_other' hobs5 Register.x11 (by decide) hx11_4
  have hx13_5 : σ5.regs.get? Register.x13 = some (aEnv + sign_extend (m := 64) (0x000#12)) :=
    obs_alu_other' hobs5 Register.x13 (by decide) hx13_4
  have hx12_5 : σ5.regs.get? Register.x12 = some aExprChild := by
    have h1 : σ2.regs.get? Register.x12 = some aExprChild :=
      obs_branch_nottaken_other' hobs2 Register.x12 (by decide) hx12_1
    have h3 : σ3.regs.get? Register.x12 = some aExprChild := obs_alu_other' hobs3 Register.x12 (by decide) h1
    have h4 : σ4.regs.get? Register.x12 = some aExprChild := obs_alu_other' hobs4 Register.x12 (by decide) h3
    exact obs_alu_other' hobs5 Register.x12 (by decide) h4
  have hsp_5 : σ5.regs.get? Register.x2 = some (sp - 176#64) := obs_alu_other' hobs5 Register.x2 (by decide) hsp_4
  obtain ⟨vmi5, hmi5⟩ := obs_alu_minstret hobs5
  have hout5 : σ5.sailOutput = out0 := by rw [hobs5.out, sailOutput_sigmaPost_alu]; exact hout4
  have hx11_val : σ5.regs.get? Register.x11 = some aInterp := by
    rw [hx11_5, sext_zero, BitVec.add_zero]
  have hx13_val : σ5.regs.get? Register.x13 = some aEnv := by
    rw [hx13_5, sext_zero, BitVec.add_zero]
  have abi_ne' : ∀ {X R : Register}, AbiPreserved X = false → AbiPreserved R = true →
      (X == R) = false := by
    intro X R hX hR
    rcases hXR : (X == R) with _ | _
    · rfl
    · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hR; exact absurd hR (by decide)
  have hframe5 : ∀ R : Register, AbiPreservedNoise R → σ5.regs.get? R = gpre R := by
    intro R hR
    obtain ⟨hab, hpcR, hnpcR, hmiR, hmiiR, hmcR, hmtR, hmipR⟩ := hR
    have h12R : (Register.x12 == R) = false := abi_ne' (by decide) hab
    have h11R : (Register.x11 == R) = false := abi_ne' (by decide) hab
    have h13R : (Register.x13 == R) = false := abi_ne' (by decide) hab
    have h10R : (Register.x10 == R) = false := abi_ne' (by decide) hab
    have f1 : σ1.regs.get? R = c.σ.regs.get? R :=
      (hobs1.1 R hmcR hmtR hmipR).trans
        (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR h12R hnpcR hmiiR)
    have f2 : σ2.regs.get? R = σ1.regs.get? R :=
      (hobs2.1 R hmcR hmtR hmipR).trans
        (get?_sigmaPost_branch_nottaken _ _ _ R hmiR hpcR hnpcR hmiiR)
    have f3 : σ3.regs.get? R = σ2.regs.get? R :=
      (hobs3.1 R hmcR hmtR hmipR).trans
        (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR h11R hnpcR hmiiR)
    have f4 : σ4.regs.get? R = σ3.regs.get? R :=
      (hobs4.1 R hmcR hmtR hmipR).trans
        (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR h13R hnpcR hmiiR)
    have f5 : σ5.regs.get? R = σ4.regs.get? R :=
      (hobs5.1 R hmcR hmtR hmipR).trans
        (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR h10R hnpcR hmiiR)
    rw [f5, f4, f3, f2, f1]; exact hgframe R ⟨hab, hpcR, hnpcR, hmiR, hmiiR, hmcR, hmtR, hmipR⟩
  -- ============ land at σ5 (the jal PC 0x800040ec) as `ExecJalPreBundle e` ==========
  have hjspN : ((sp - 176#64) + 1088#64).toNat = (sp.toNat - 176) + 1088 := by
    rw [BitVec.toNat_add]; have hv : (1088#64 : BitVec 64).toNat = 1088 := by decide
    rw [hv, hespN]; omega
  have hjspcancel : ((sp - 176#64) + 1088#64) - 1088#64 = sp - 176#64 := by
    rw [BitVec.add_sub_cancel]
  have hx2jsp : σ5.regs.get? Register.x2 = some (((sp - 176#64) + 1088#64) - 1088#64) := by
    rw [hjspcancel]; exact hsp_5
  refine ⟨5, ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩, by omega,
    StepsN.succ hstep1 (StepsN.succ hstep2 (StepsN.succ hstep3 (StepsN.succ hstep4
      (StepsN.succ hstep5 (StepsN.zero _))))), ?_⟩
  refine ⟨gpre, N, A, SL, φf, φc, (0x800040ec#64), (0x800040f0#64), (0x1ff078#21),
    (sp - 176#64) + 1088#64, r, aInterp, (sp - 176#64) + sign_extend (m := 64) (0x068#12),
    aInterp, aExprChild, v8, v9, v18, out0, ment, ?_, ?_, ?_, ?_,
    hG5, hi5, hpc5, hx10_5, ?_, hx11_val, ⟨_, hx13_val⟩, hx12_5, hx2jsp, ⟨vmi5, hmi5⟩, hout5, ?_,
    hmem5e, ?_, hEvCode, hViInt, hViSlot, hNbsJ, ?_, ?_, ?_, ?_, hframe5, ⟨hg8, hg18⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- hjaltgt
  · apply BitVec.eq_of_toNat_eq; simp only [evalExprEntry]; decide
  -- hlink
  · apply BitVec.eq_of_toNat_eq; decide
  -- retAl
  · decide
  -- hjalSite
  · intro σ i u vmiσ hGσ hpcσ hmiσ hcodeσ hiσ
    exact site_800040ec_es σ i u (0x800040ec#64) vmiσ hGσ hpcσ hmiσ hcodeσ rfl hiσ
  -- x9 = sret := aInterp
  · have h4 : σ4.regs.get? Register.x9 = some aInterp := by
      have h1 : σ2.regs.get? Register.x9 = some aInterp := hs1_2
      have h3 : σ3.regs.get? Register.x9 = some aInterp := obs_alu_other' hobs3 Register.x9 (by decide) h1
      exact obs_alu_other' hobs4 Register.x9 (by decide) h3
    exact obs_alu_other' hobs5 Register.x9 (by decide) h4
  -- String.join out0.toList = st.out
  · exact houtStr
  -- Exec_stmtLoaded ment
  · exact hcode
  -- ExprRepr ment aExprChild e
  -- WAVE 47i: EvalGround at the jsp ghost (cancel to the carried sp-176 form)
  · rw [hjspcancel]; exact hGroundJ
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
  · rw [hsub104]; omega
  -- jsp - 1088 ≤ subsret
  · rw [hsub104, show ((sp - 176#64) + 1088#64).toNat - 1088 = sp.toNat - 176 by rw [hjspN]; omega]; omega
  -- subsret + 24 ≤ jsp - 32
  · rw [hsub104, hjspN]; omega
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

#print axioms blockB_stmtVarInit_stagePre

/-! ## §2. The `stmtVarInit` field composer -/

/-- **The stmtVarInit dispatch residual** (the `blockB_stmtVarInit_stagePre` entry
bundle a `blockA` would produce). -/
def StmtVarInitArmDispatch
    (x : String) (e : Expr) (st : Vsa.While.St) (d : Nat) (env : Addr) (c : Config) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem),
    ExecEntry g N A SL φf φc st d env (.varDecl x (some e)) sp r aInterp aStmt aEnv aRet m0 c →
    Triple (fun c'' => c'' = c)
      (fun c' => ∃ (gpre : (R : Register) → Option (RegisterType R))
        (aExprChild : BitVec 64) (v8 v9 v18 v19 : BitVec 64) (ment : Mem),
        ExecArmEntryK g N A SL φf φc st (0x800040d8#64)
          sp r aInterp aStmt aEnv aRet v8 v9 v18 v19 c'.σ.sailOutput m0 ment c' ∧
        read64 ment (aStmt.toNat + 16) = some aExprChild.toNat ∧
        ExprRepr ment aExprChild.toNat e ∧
        aStmt.toNat % 8 = 0 ∧
        0x80000000 ≤ aStmt.toNat ∧ aStmt.toNat + 24 ≤ 0x100000000 ∧
        (aStmt.toNat + 24 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aStmt.toNat) ∧
        Eval_exprLoaded ment ∧ Value_intLoaded ment ∧ IntSlotPinned ment ∧ NBSPins ment ∧
        -- WAVE 47i: the eval child's entry-ground bundle (carried like the
        -- eval-side code facts above; NOT derivable from `ExecGround`).
        EvalGround ment SL A (sp - 176#64)
          ((sp - 176#64) + sign_extend (m := 64) (0x068#12)) aExprChild.toNat e ∧
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
        ((0x8000282c : Nat) ≤ SL.lo ∨ ((sp.toNat - 176) + 1088) ≤ 0x800027ec) ∧
        ((0x80019f58 : Nat) + 44 ≤ SL.lo ∨ ((sp.toNat - 176) + 1088) ≤ 0x80019f58) ∧
        (A.hi ≤ SL.lo ∨ (sp.toNat - 176) + 1088 ≤ A.lo) ∧
        (A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo) ∧
        (∀ R : Register, AbiPreservedNoise R → c'.σ.regs.get? R = gpre R) ∧
        (∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w) ∧
        -- ITEM ZERO B1: the child expression's budget at the statement
        -- frame `sp - 176`, `.fn`-bodies bound, store-bodies invariant.
        StackOK SL (sp - 176#64)
          (e.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget e = true ∧
        Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget)

/-- **The stmtVarInit RE-ENTRY dispatch residual** (wave 45, the amended
`SEntryC`'s dispatch-head leg): from `SDispatchC (.varDecl x (some e))` — a tail
re-dispatch landing this arm from `execStmtDispatchHead` — stage the sub-expr
sub-call.  Supplied upstream by a dispatch-head → arm-head span (the jump-table
half of `execBlockA` re-run from `0x80004014`, no prologue). -/
def StmtVarInitReentryDispatch
    (x : String) (e : Expr) (st : Vsa.While.St) (d : Nat) (env : Addr) (c : Config) : Prop :=
  SDispatchC c st d env (.varDecl x (some e)) →
  LandedN 1 c (fun c' => ExecJalPreBundle e c' st d env)

/-- **The `EvalChildStages.stmtVarInit` field, machine-composed (exec twin).** -/
theorem stmtVarInit_field_of_dispatch
    (x : String) (e : Expr) (c : Config) (st : Vsa.While.St) (d : Nat) (env : Addr)
    (hDisp : StmtVarInitArmDispatch x e st d env c)
    (hReentry : StmtVarInitReentryDispatch x e st d env c) :
    SEntryC c st d env (.varDecl x (some e)) →
    LandedN 1 c (fun c' => EEntryC c' st d env e) := by
  refine stmtVarInit_split' x e c st d env (fun hSE => ?_)
  rcases hSE with hSE | hRe | hWA
  · -- fresh-call leg (the pre-amendment body)
    obtain ⟨g, N, A, SL, φf, φc, sp, r, aInterp, aStmt, aEnv, aRet, m0, hEntry⟩ := hSE
    obtain ⟨c1, hsteps1, hMid⟩ :=
      hDisp g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 hEntry c rfl
    obtain ⟨gpre, aExprChild, v8, v9, v18, v19, ment, hArm, hpay, hExprChild,
      hstmtAl, hstmtLo, hstmtRam, hstmtWin, hEvCode, hViInt, hViSlot, hNbsJ, hGroundJ, hStoreSurvJ,
      hopAl, hopLo, hopHi, hopWin, hopStk, hsproom, hsp16pre, hSLlo, hSLhiRam, hSLwin,
      hjspSLhi, hcodeStkJ, htableStkJ1, htableStkJ2, harenaStkJ, harenaCode,
      hgframe, hg8, hg18, hstackBudget, hexprBodies, hstoreBodies⟩ := hMid
    have hcut : LandedN 5 c1 (fun c' => ExecJalPreBundle e c' st d env) :=
      blockB_stmtVarInit_stagePre g gpre N A SL φf φc st d env e
        sp r aInterp aStmt aEnv aRet aExprChild v8 v9 v18 v19 c1.σ.sailOutput m0 ment c1
        ⟨hArm, hpay, hExprChild, hstmtAl, hstmtLo, hstmtRam, hstmtWin,
         hEvCode, hViInt, hViSlot, hNbsJ, hGroundJ, hStoreSurvJ,
         hopAl, hopLo, hopHi, hopWin, hopStk, hsproom, hsp16pre, hSLlo, hSLhiRam, hSLwin,
         hjspSLhi, hcodeStkJ, htableStkJ1, htableStkJ2, harenaStkJ, harenaCode,
         hgframe, hg8, hg18, hstackBudget, hexprBodies, hstoreBodies⟩
    obtain ⟨n1, hn1⟩ := hsteps1.toN
    obtain ⟨m2, c2, hm2, hs2, hpb⟩ := hcut
    exact ⟨n1 + m2, c2, by omega, hn1.trans_add hs2, hpb⟩
  · -- dispatch-head re-entry leg (wave-45 named residual)
    exact hReentry hRe
  · -- while-arm leg: `(.varDecl x (some e))` is not a while statement
    obtain ⟨cnd', b', hEq⟩ := sWhileArmC_shape hWA
    exact nomatch hEq

#print axioms stmtVarInit_field_of_dispatch

end Vsa.Sim
