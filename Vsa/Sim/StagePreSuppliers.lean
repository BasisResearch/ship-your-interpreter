import Vsa.Sim.EvalNegSim
import Vsa.Sim.EvalBinSim
import Vsa.Sim.ArmSegSplitEval
import Vsa.Sim.EntryGroundKit

/-!
# `StagePreSuppliers` — the arm-head→`JalPreBundle` cuts (Task #76, Half B)

`ArmSegSplitEval` closed the eval-child fields of `ApproxArmResidGap` MODULO a
per-class `*StagePre` residual: from the arm entry, the arm-head + dispatch span
reaches (in `≥ 1` steps) a config satisfying `JalPreBundle child` — the state at the
recursive `jal eval_expr` PC with the child's sub-call fully staged.  This file
supplies those staging cuts by RE-CUTTING the existing landed arm chains: each arm's
head span is ALREADY built (it feeds `armTail_rec`/`evalEntry_of_jalPrefix`); we stop
it at the jal pre-bundle instead of consuming the eval IH.

The shared dispatch prefix (`blockA_k`, `EvalIntSim2.lean`) is the case-INDEPENDENT
first factor — prologue spills + kind read + jump-table dispatch to the arm PC,
landing at `ArmEntryK`.  Each arm's head is then the SECOND factor, cut here.

## `blockB_unary_stagePre` — the unary model

`EvalNegSim.blockB_unary` takes its `ArmEntryK`-plus-recursive-extras precondition,
advances TWO machine steps (`ld a2,16(a2)` operand load ≫ `addi a0,sp,144`
sub-buffer), reaching the config `σ2` at `0x800035e8` (the `jal eval_expr` PC) with
the sub-call fully staged, then hands EXACTLY that state to `armTail_rec` (whose
front is `evalEntry_of_jalPrefix`).  `blockB_unary_stagePre` reuses the SAME two
steps but stops at `σ2`, packaging it as `JalPreBundle esub` — the pre-bundle the
verified marshalling bridge finishes.  The lowered-frame geometry (operand
`ExprRepr`, `SL.lo + 3264 ≤ sp` headroom, sub-buffer disjointness) rides through as
the `ArmEntryK`-extras premises, exactly as the audit prescribes: carried, not
derived.

This makes `blockB_unary_stagePre` a drop-in `EvalChildStages.unary` supplier
(modulo the shared `blockA_k` dispatch composition, whose ~40 entry premises are the
`ArmEntryK` widening residual — the standing upstream, not re-opened here).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no `maxHeartbeats`
bump.  Axioms of every theorem ⊆ {propext, Classical.choice, Quot.sound}.
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
    (hpre : ∃ ment,
        ArmEntryK gouter N A SL φf φc st (0x800035e0#64) UnaryArmCallee (.unary op esub)
          sp r sret aExpr aIn v8 v9 v18 out0 m0 ment c ∧
        c.σ.regs.get? Register.x11 = some aIn ∧
        (∃ w, c.σ.regs.get? Register.x13 = some w) ∧          -- a3 defined (wave 48h CURE A)
        (∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = gpre R) ∧
        (∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w) ∧
        read64 ment (aExpr.toNat + 16) = some aOperand.toNat ∧
        ExprRepr ment aOperand.toNat esub ∧
        -- WAVE 47i: the child's entry-ground bundle (kit-derived at the sim).
        EvalGround ment SL A (sp - 1088#64)
          ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)) aOperand.toNat esub ∧
        aExpr.toNat + 24 ≤ 0x100000000 ∧
        aOperand.toNat % 8 = 0 ∧
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
  obtain ⟨ment, hArm, hx11, ⟨wx13, hx13⟩, hgframe, hg8, hg18, hpay, hsubexpr, hground, hexprHi24,
    hopAl, hopLo, hopHi, hopWin, hopStk,
    hsproom, hspSLhi, hsp16, hSLhiRam,
    hcodeStk, hviStk, htableStk, harenaStk, harenaCode,
    hstackBudget, hexprBodies, hstoreBodies⟩ := hpre
  obtain ⟨hG, htick, hpc, ha0, hs1, ha2, hsp, hra, ⟨vmi, hmi⟩, hout, hmem, hcode, hviCode,
    hexpr, houtStr, hexprAl, hexprLo, hexprHi, hexprWin,
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
      (by rw [haddr16, htoh]; right; omega) (by rw [haddr16]; omega)
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
  have hx13_1 : σ1.regs.get? Register.x13 = some wx13 := obs_alu_other' hobs1 Register.x13 (by decide) hx13
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
  have hx13_2 : σ2.regs.get? Register.x13 = some wx13 := obs_alu_other' hobs2 Register.x13 (by decide) hx13_1
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
      v8, v9, v18, out0, ment,
      (by apply BitVec.eq_of_toNat_eq; simp only [evalExprEntry]; decide),
      (by apply BitVec.eq_of_toNat_eq; decide),
      (by decide),
      (fun σ i u vmiσ hGσ hpcσ hmiσ hcodeσ hiσ =>
        site_800035e8_ee σ i u (0x800035e8#64) vmiσ hGσ hpcσ hmiσ hcodeσ rfl
          (by
            rw [show ((0x800035e8#64 : BitVec 64) + sign_extend (m := 64) (0x1ffb7c#21))
              = (0x80003164#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide]
            decide) hiσ),
      hG2, hi2, hpc2, hx10_2, hs1_2, hx11_2, ⟨wx13, hx13_2⟩, hx12_2, hsp_2, ⟨vmi2, hmi2⟩, hout2, houtStr,
      hmem2e, hcode, hviInt, hviSlot, hnbs, hground, hsubexpr, hstore, hstoreSurv, hframeB, ⟨hg8, hg18⟩,
      hslotRa, hslotS0, hslotS1, hslotS2,
      hopAl, hopLo, hopHi, hopWin, hopStk,
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
    (hpre : ∃ ment,
        ArmEntryK gouter N A SL φf φc st (0x800034e8#64) UnaryArmCallee (.binary op el er)
          sp r sret aExpr aEnv v8 v9 v18 out0 m0 ment c ∧
        BinExtras N A SL el er ment sp sret aExpr aLOp aROp ∧
        c.σ.regs.get? Register.x11 = some aEnv ∧
        c.σ.regs.get? Register.x13 = some aEnvReg ∧
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
  obtain ⟨ment, hArm, hBE, hx11, hx13, hx19, hgframe, hg8, hg18, hgx8v, hgx18v, hgx19v,
    hpayL, hexprL, hpayR, hexprR, hMemExtM0, hGmt47,
    hstackBudgetL, hexprBodiesL, hstoreBodiesL⟩ := hpre
  obtain ⟨hG, htick, hpc, ha0, hs1, ha2, hsp, hra, ⟨vmi, hmi⟩, hout, hmem, hcode, hviCode,
    hexpr, houtStr, hexprAl, hexprLo, hexprHi, hexprWin,
    hslotRa, hslotS0, hslotS1, hslotS2, hmemframe_m0,
    hgx8, hgx9, hgx18, hgx2, hstore, hstoreSurv, hframe,
    hsretAl, hsretLo, hsretHi, hsretWin, hsretVi, hsretStk, hsretEvalCode,
    hsp1088, hsphi, hsplo, hspwin, hsp8, hSLlo, hSLwin, hSLloSp, hraAl,
    _hAEx11, _hAEx8, _hAEx18⟩ := hArm
  obtain ⟨hviInt, hviSlot, hnbs⟩ : Value_intLoaded ment ∧ IntSlotPinned ment ∧ NBSPins ment := hviCode
  have hnodehi := hBE.node_hi
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hsp1088' : 1088 ≤ sp.toNat := by omega
  have hspsub : (sp - 1088#64).toNat = sp.toNat - 1088 := by
    rw [BitVec.toNat_sub]
    have h1088 : (1088#64 : BitVec 64).toNat = 1088 := by decide
    rw [h1088]; have := sp.isLt; omega
  have abi_ne' : ∀ {X R : Register}, AbiPreserved X = false → AbiPreserved R = true →
      (X == R) = false := by
    intro X R hX hR
    rcases hXR : (X == R) with _ | _
    · rfl
    · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hR; exact absurd hR (by decide)
  have h16 : (sign_extend (m := 64) (0x010#12) : BitVec 64) = 16#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  have haddr16 : (aExpr + sign_extend (m := 64) (0x010#12)).toNat = aExpr.toNat + 16 := by
    rw [h16, BitVec.toNat_add]
    have hv : (16#64 : BitVec 64).toNat = 16 := by decide
    rw [hv]; omega
  obtain ⟨lp0, lp1, lp2, lp3, lp4, lp5, lp6, lp7, hlp0, hlp1, hlp2, hlp3, hlp4, hlp5, hlp6, hlp7, hlpsext⟩ :=
    spill_roundtrip_ee ment (aExpr.toNat + 16) aLOp hpayL
  -- ============ 0x800034e8: ld a2,16(a2) → x12 := aLOp ============
  obtain ⟨σ1, i1, hs1', hi1, hG1, hmem1, hobs1⟩ :=
    site_800034e8_ee c.σ c.tick c.steps (0x800034e8#64) vmi aExpr lp0 lp1 lp2 lp3 lp4 lp5 lp6 lp7
      hG hpc hmi ha2 (hmem ▸ hcode) rfl
      (by rw [haddr16]; omega) (by rw [haddr16]; omega)
      (by rw [haddr16, htoh]; right; omega) (by rw [haddr16]; omega)
      (by rw [haddr16, hmem]; exact hlp0) (by rw [haddr16, hmem]; exact hlp1)
      (by rw [haddr16, hmem]; exact hlp2) (by rw [haddr16, hmem]; exact hlp3)
      (by rw [haddr16, hmem]; exact hlp4) (by rw [haddr16, hmem]; exact hlp5)
      (by rw [haddr16, hmem]; exact hlp6) (by rw [haddr16, hmem]; exact hlp7) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1'
  have hmem1e : σ1.mem = ment := by rw [hmem1]; exact hmem
  have hpc1 : σ1.regs.get? Register.PC = some (0x800034ec#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x800034e8#64) 4 = (0x800034ec#64 : BitVec 64) from by decide] at this
  have hx12_1 : σ1.regs.get? Register.x12 = some aLOp := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hlpsext] at this
  have ha0_1 : σ1.regs.get? Register.x10 = some sret := obs_alu_other' hobs1 Register.x10 (by decide) ha0
  have hs1_1 : σ1.regs.get? Register.x9 = some sret := obs_alu_other' hobs1 Register.x9 (by decide) hs1
  have hx11_1 : σ1.regs.get? Register.x11 = some aEnv := obs_alu_other' hobs1 Register.x11 (by decide) hx11
  have hx13_1 : σ1.regs.get? Register.x13 = some aEnvReg := obs_alu_other' hobs1 Register.x13 (by decide) hx13
  have hx19_1 : σ1.regs.get? Register.x19 = some v19 := obs_alu_other' hobs1 Register.x19 (by decide) hx19
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other' hobs1 Register.x2 (by decide) hsp
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hout1 : σ1.sailOutput = out0 := by rw [hobs1.out, sailOutput_sigmaPost_alu]; exact hout
  have hcode1 : Eval_exprLoaded σ1.mem := by rw [hmem1e]; exact hcode
  -- ============ 0x800034ec: addi a0,sp,120 → x10 := sp-968 ============
  obtain ⟨σ2, i2, hs2', hi2, hG2, hmem2, hobs2⟩ :=
    site_800034ec_ee σ1 i1 (c.steps + 1) (0x800034ec#64) vmi1 (sp - 1088#64)
      hG1 hpc1 hmi1 hsp_1 hcode1 rfl hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2'
  have hmem2e : σ2.mem = ment := by rw [hmem2]; exact hmem1e
  have hpc2 : σ2.regs.get? Register.PC = some (0x800034f0#64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x800034ec#64) 4 = (0x800034f0#64 : BitVec 64) from by decide] at this
  have hsretL : ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)).toNat = sp.toNat - 968 :=
    spill_addr sp (0x078#12) 968 (by decide) (by omega) hsp1088'
  have ha0_2 : σ2.regs.get? Register.x10 = some ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)) :=
    obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hs1_2 : σ2.regs.get? Register.x9 = some sret := obs_alu_other' hobs2 Register.x9 (by decide) hs1_1
  have hx11_2 : σ2.regs.get? Register.x11 = some aEnv := obs_alu_other' hobs2 Register.x11 (by decide) hx11_1
  have hx12_2 : σ2.regs.get? Register.x12 = some aLOp := obs_alu_other' hobs2 Register.x12 (by decide) hx12_1
  have hx13_2 : σ2.regs.get? Register.x13 = some aEnvReg := obs_alu_other' hobs2 Register.x13 (by decide) hx13_1
  have hx19_2 : σ2.regs.get? Register.x19 = some v19 := obs_alu_other' hobs2 Register.x19 (by decide) hx19_1
  have hsp_2 : σ2.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other' hobs2 Register.x2 (by decide) hsp_1
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hout2 : σ2.sailOutput = out0 := by rw [hobs2.out, sailOutput_sigmaPost_alu]; exact hout1
  have hcode2 : Eval_exprLoaded σ2.mem := by rw [hmem2e]; exact hcode
  have haddr1048 : ((sp - 1088#64) + sign_extend (m := 64) (0x418#12)).toNat = sp.toNat - 40 :=
    spill_addr sp (0x418#12) 40 (by decide) (by omega) hsp1088'
  have haddr0 : ((sp - 1088#64) + sign_extend (m := 64) (0x000#12)).toNat = sp.toNat - 1088 := by
    have : (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 := by apply BitVec.eq_of_toNat_eq; decide
    rw [this, BitVec.add_zero]; exact hspsub
  -- ============ 0x800034f0: sd s3,1048(sp) → ma at sp-40 ============
  let ma : Mem := writeMap8 ment (sp.toNat - 40) (sdData_val v19)
  obtain ⟨σ3, i3, hs3', hi3, hG3, hmem3, hobs3⟩ :=
    site_800034f0_ee σ2 i2 (c.steps + 1 + 1) (0x800034f0#64) vmi2 (sp - 1088#64) v19
      hG2 hpc2 hmi2 hsp_2 hx19_2 hcode2 rfl
      (by rw [haddr1048]; omega) (by rw [haddr1048]; omega)
      (by rw [haddr1048, htoh]; omega) (by rw [haddr1048]; omega) hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3'
  have hmem3e : σ3.mem = ma := by rw [hmem3, mem_afterNextPC, haddr1048, hmem2e]
  have hpc3 : σ3.regs.get? Register.PC = some (0x800034f4#64) := by
    have := obs_store_pc_val hobs3
    rwa [show BitVec.addInt (0x800034f0#64) 4 = (0x800034f4#64 : BitVec 64) from by decide] at this
  have ha0_3 := obs_store_other_val' hobs3 Register.x10 (by decide) ha0_2
  have hs1_3 := obs_store_other_val' hobs3 Register.x9 (by decide) hs1_2
  have hx11_3 := obs_store_other_val' hobs3 Register.x11 (by decide) hx11_2
  have hx12_3 := obs_store_other_val' hobs3 Register.x12 (by decide) hx12_2
  have hx13_3 := obs_store_other_val' hobs3 Register.x13 (by decide) hx13_2
  have hsp_3 := obs_store_other_val' hobs3 Register.x2 (by decide) hsp_2
  obtain ⟨vmi3, hmi3⟩ := obs_store_minstret_val hobs3
  have hout3 : σ3.sailOutput = out0 := by rw [hobs3.out, sailOutput_sigmaPost_store]; exact hout2
  have hcode3 : Eval_exprLoaded σ3.mem := by
    rw [hmem3e]
    exact loaded_eval_expr_agreeP ment ma
      (fun k hk => (getElem_writeMap8_disjoint ment (sp.toNat-40) k (sdData_val v19)
        (by rcases hBE.codeStk with h | h <;> omega)).symm) hcode
  -- ============ 0x800034f4: sd a3,0(sp) → mcall1 at sp-1088 ============
  let mcall1 : Mem := writeMap8 ma (sp.toNat - 1088) (sdData_val aEnvReg)
  obtain ⟨σ4, i4, hs4', hi4, hG4, hmem4, hobs4⟩ :=
    site_800034f4_ee σ3 i3 (c.steps + 1 + 1 + 1) (0x800034f4#64) vmi3 (sp - 1088#64) aEnvReg
      hG3 hpc3 hmi3 hsp_3 hx13_3 hcode3 rfl
      (by rw [haddr0]; omega) (by rw [haddr0]; omega)
      (by rw [haddr0, htoh]; omega) (by rw [haddr0]; omega) hi3
  have hstep4 : Step ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ := hs4'
  have hmem4e : σ4.mem = mcall1 := by rw [hmem4, mem_afterNextPC, haddr0, hmem3e]
  have hpc4 : σ4.regs.get? Register.PC = some (0x800034f8#64) := by
    have := obs_store_pc_val hobs4
    rwa [show BitVec.addInt (0x800034f4#64) 4 = (0x800034f8#64 : BitVec 64) from by decide] at this
  have ha0_4 := obs_store_other_val' hobs4 Register.x10 (by decide) ha0_3
  have hx13_4 := obs_store_other_val' hobs4 Register.x13 (by decide) hx13_3
  have hs1_4 := obs_store_other_val' hobs4 Register.x9 (by decide) hs1_3
  have hx11_4 := obs_store_other_val' hobs4 Register.x11 (by decide) hx11_3
  have hx12_4 := obs_store_other_val' hobs4 Register.x12 (by decide) hx12_3
  have hsp_4 := obs_store_other_val' hobs4 Register.x2 (by decide) hsp_3
  obtain ⟨vmi4, hmi4⟩ := obs_store_minstret_val hobs4
  have hout4 : σ4.sailOutput = out0 := by rw [hobs4.out, sailOutput_sigmaPost_store]; exact hout3
  have hcodema : Eval_exprLoaded ma := by rw [← hmem3e]; exact hcode3
  have hcode4 : Eval_exprLoaded σ4.mem := by
    rw [hmem4e]
    exact loaded_eval_expr_agreeP ma mcall1
      (fun k hk => (getElem_writeMap8_disjoint ma (sp.toNat-1088) k (sdData_val aEnvReg)
        (by rcases hBE.codeStk with h | h <;> omega)).symm) hcodema
  -- agreement ment ↔ mcall1 outside [SL.lo, sp)
  have hAgMcall1 : ∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → ment[k]? = mcall1[k]? := by
    intro k hk
    show ment[k]? = (writeMap8 ma (sp.toNat - 1088) (sdData_val aEnvReg))[k]?
    rw [getElem_writeMap8_disjoint ma (sp.toNat - 1088) k (sdData_val aEnvReg) (by omega)]
    show ment[k]? = (writeMap8 ment (sp.toNat - 40) (sdData_val v19))[k]?
    rw [getElem_writeMap8_disjoint ment (sp.toNat - 40) k (sdData_val v19) (by omega)]
  have hviInt1 : Value_intLoaded mcall1 :=
    loaded_value_int_agreeP ment mcall1
      (fun a ha => hAgMcall1 a (by rcases hBE.viStk with h | h <;> omega)) hviInt
  have hnbs1 : NBSPins mcall1 :=
    hnbs.survive_stack hBE.viStk hBE.tableStk hAgMcall1
  have hviSlot1 : IntSlotPinned mcall1 := by
    apply intSlot_writeMap8 ma (sp.toNat - 1088) (sdData_val aEnvReg)
      (by simp only [jumpTableBase]; rcases hBE.tableStk with h | h
          · right; omega
          · left; omega)
    exact intSlot_writeMap8 ment (sp.toNat - 40) (sdData_val v19)
      (by simp only [jumpTableBase]; rcases hBE.tableStk with h | h
          · right; omega
          · left; omega) hviSlot
  have hstore1 : StoreRepr mcall1 N A φf φc st.store :=
    hstoreSurv mcall1 (fun k hk1 _ => hAgMcall1 k (fun hcon =>
      hk1 ⟨hcon.1, Nat.lt_of_lt_of_le hcon.2 hBE.spSLhi⟩))
  have hstoreSurv1 : ∀ m' : Mem,
      (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) →
        mcall1[k]? = m'[k]?) → StoreRepr m' N A φf φc st.store := by
    intro m' hag
    refine hstoreSurv m' (fun k hk1 hk2 => ?_)
    have hk1' : ¬ (SL.lo ≤ k ∧ k < sp.toNat) := fun hcon =>
      hk1 ⟨hcon.1, Nat.lt_of_lt_of_le hcon.2 hBE.spSLhi⟩
    rw [hAgMcall1 k hk1']; exact hag k hk1 hk2
  have hsproom := hBE.sproom
  have hspSLhi := hBE.spSLhi
  have hexprL1 : ExprRepr mcall1 aLOp.toNat el :=
    hBE.lexpr_surv mcall1 (fun k hk => hAgMcall1 k (fun ⟨ha, hb⟩ => hk ⟨ha, by omega⟩))
  have hslotpeel : ∀ (a : Nat) (v : BitVec 64), sp.toNat - 32 ≤ a → a + 8 ≤ sp.toNat →
      read64 ment a = some v.toNat → read64 mcall1 a = some v.toNat := by
    intro a v ha1 ha2 hr
    show read64 (writeMap8 ma (sp.toNat - 1088) (sdData_val aEnvReg)) a = some v.toNat
    rw [read64_writeMap8_disj ma a (sp.toNat - 1088) (sdData_val aEnvReg) (by omega)]
    show read64 (writeMap8 ment (sp.toNat - 40) (sdData_val v19)) a = some v.toNat
    rw [read64_writeMap8_disj ment a (sp.toNat - 40) (sdData_val v19) (by omega)]
    exact hr
  have hslotRa1 : read64 mcall1 (sp.toNat - 8) = some r.toNat :=
    hslotpeel (sp.toNat - 8) r (by omega) (by omega) hslotRa
  have hslotS01 : read64 mcall1 (sp.toNat - 16) = some v8.toNat :=
    hslotpeel (sp.toNat - 16) v8 (by omega) (by omega) hslotS0
  have hslotS11 : read64 mcall1 (sp.toNat - 24) = some v9.toNat :=
    hslotpeel (sp.toNat - 24) v9 (by omega) (by omega) hslotS1
  have hslotS21 : read64 mcall1 (sp.toNat - 32) = some v18.toNat :=
    hslotpeel (sp.toNat - 32) v18 (by omega) (by omega) hslotS2
  have hframe4 : ∀ R : Register, AbiPreservedNoise R → σ4.regs.get? R = gpre R := by
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
    have f3 : σ3.regs.get? R = σ2.regs.get? R :=
      (hobs3.1 R hmcR hmtR hmipR).trans
        (get?_sigmaPost_store _ _ _ _ R hmiR hpcR hnpcR hmiiR)
    have f4 : σ4.regs.get? R = σ3.regs.get? R :=
      (hobs4.1 R hmcR hmtR hmipR).trans
        (get?_sigmaPost_store _ _ _ _ R hmiR hpcR hnpcR hmiiR)
    rw [f4, f3, f2, f1]; exact hgframe R hR'
  have hcodemcall1 : Eval_exprLoaded mcall1 := by rw [← hmem4e]; exact hcode4
  have hsub968 : ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)).toNat = sp.toNat - 968 := hsretL
  -- WAVE 47i: the LEFT child's entry-ground bundle at `mcall1` (kit moves 1+2+3).
  have hGroundM1 : EvalGround mcall1 SL A sp sret aExpr.toNat (.binary op el er) :=
    hGmt47.transport_offstack hBE.tableStk hBE.spSLhi
      (fun a ha => (hAgMcall1 a ha).symm)
  have hpayL1 : read64 mcall1 (aExpr.toNat + 16) = some aLOp.toNat := by
    rw [evalGround_ast_read64_agree hGmt47 hBE.spSLhi
      (fun a ha => (hAgMcall1 a ha).symm) (off := 16) (by omega)]
    exact hpayL
  have hGroundL : EvalGround mcall1 SL A (sp - 1088#64)
      ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)) aLOp.toNat el :=
    hGroundM1.child_params (fun lo hi hin => exprIn_binary_left hin aLOp.toNat hpayL1)
      hBE.tableStk hBE.spSLhi (by omega)
      (by rw [hsub968]; have := hBE.sproom; have := hSLlo; omega)
      (by rw [hsub968]; have := hBE.sproom; have := hSLlo; omega)
  -- ============ land at σ4 (the LEFT jal PC) as `JalPreBundle el` ============
  refine ⟨4, ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩, Nat.le_refl _,
    StepsN.succ hstep1 (StepsN.succ hstep2 (StepsN.succ hstep3 (StepsN.succ hstep4 (StepsN.zero _)))),
    ?_⟩
  · exact ⟨gpre, N, A, SL, φf, φc, (0x800034f8#64), (0x800034fc#64), (0x1ffc6c#21),
      sp, r, sret, ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)), aEnv, aLOp,
      v8, v9, v18, out0, mcall1,
      (by apply BitVec.eq_of_toNat_eq; simp only [evalExprEntry]; decide),
      (by apply BitVec.eq_of_toNat_eq; decide),
      (by decide),
      (fun σ i u vmiσ hGσ hpcσ hmiσ hcodeσ hiσ =>
        site_800034f8_ee σ i u (0x800034f8#64) vmiσ hGσ hpcσ hmiσ hcodeσ rfl hiσ),
      hG4, hi4, hpc4, ha0_4, hs1_4, hx11_4, ⟨_, hx13_4⟩, hx12_4, hsp_4, ⟨vmi4, hmi4⟩,
      hout4, houtStr, hmem4e, hcodemcall1, hviInt1, hviSlot1, hnbs1, hGroundL, hexprL1, hstore1, hstoreSurv1,
      hframe4, ⟨hg8, hg18⟩,
      hslotRa1, hslotS01, hslotS11, hslotS21,
      hBE.lop_align, hBE.lop_ram.1, hBE.lop_ram.2, hBE.lop_win, hBE.lop_stk,
      (by rw [hsub968]; omega), (by rw [hsub968]; omega), (by rw [hsub968]; omega),
      (by omega), hBE.spSLhi, hBE.sp16, (by omega), hSLlo, hBE.SLhiRam, hSLwin,
      hBE.codeStk, hBE.viStk, hBE.tableStk, hBE.arenaStk, hBE.arenaCode,
      hstackBudgetL, hexprBodiesL, hstoreBodiesL⟩

#print axioms blockB_binary_leftStagePre

end Vsa.Sim
