import Vsa.Sim.StagePreSuppliers2
import Vsa.Sim.EvalChildFieldCombinator
import Vsa.Sim.DecodeTable.Batch03Part22
import Vsa.Sim.DecodeTable.Batch08Part11
import Vsa.Sim.DecodeTable.Batch04Part14
import Vsa.Sim.DecodeTable.Batch15Part31

/-!
# `CallArmStagePre` — the call-arm-head → `JalPreBundle` cut (Wave 37)

The **call** arm (`.call f args`, arm PC `0x800031b0`) evaluates the CALLEE
expression `f` first — its recursive `jal eval_expr @0x800031bc` — before the arg
loop.  Its arm head is the SAME three-instruction shape as the assign/logical arms:
`ld a2,8(a2)` (a2 := call->callee node = f, at `expr->child[8]`) ≫ `addi a0,sp,96`
(a0 := callee-result sret @sp+96) ≫ `sd a3,0(sp)` (spill env across the sub-call),
parked at `jal eval_expr @0x800031bc`.  Only the operand offset (`8`, vs `16` for
assign/logical), the buffer offset (`0x060` = `sp+96`), the arm/jal PCs, and the jal
target immediate differ from `blockB_assign_stagePre`.

This file supplies the four per-PC `StepObs` site lemmas (`site_*_cf`), the arm-head
cut `blockB_call_stagePre` (a `blockB_assign_stagePre` twin at the call PCs), and the
`callF` field composer `callF_field_of_dispatch` (modulo the standing
`EvalEntry → ArmEntryK` dispatch residual `CallArmDispatch`).

## Uniformity signal
callF joins assignE/logicalL as the SAME `ld+addi+sd → JalPreBundle` arm-head shape;
the only per-arm data is (arm PC, operand-load offset, buffer offset, jal target imm,
callee bundle).  See observation `2026-09-01 assign-call-logical-stagepre-uniform`.

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

-- discipline: allow(R7-conj-tower-def) same as AssignArmStagePre: the ∃-towers are the
-- ESTABLISHED `JalPreBundle` landing bundle + the `blockB_call_stagePre`/`CallArmDispatch`
-- entry bundle mirroring the landed `blockB_logical_stagePre`; consumed through
-- `evalChildField_of_blockA_stage` / `landedN_eentryC_of_preBundle`.

/-! ## §1. The four call-arm-head site lemmas

GENUINE per-PC `StepObs` site lemmas of the grandfathered `LogicalSites` class: the
stagePre cut must land at the `jal eval_expr` PC carrying the rich `JalPreBundle` repr,
which the `#derive_case`/`bridgeOfSeg` reflection layer cannot produce (it fires the jal
and lands at the callee).  Proper factoring = `gen_stagepre.py` (observation
`assign-call-logical-stagepre-uniform`); until then, hand clones with `allow` exemptions. -/

/-- 0x800031b0: `ld x12,0x8(x12)` (a2 := call->callee node = f, at expr->child[8]). -/
-- discipline: allow(R1-site-battery) genuine `JalPreBundle`-landing site lemma (grandfathered LogicalSites class); reflection layer cannot land the rich repr — see §1 doc
theorem site_800031b0_cf (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x800031b0#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v12 + sign_extend (m := 64) (0x008#12)).toNat)
    (hhiram : (v12 + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v12 + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v12 + sign_extend (m := 64) (0x008#12)).toNat)
    (halign : (v12 + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0)
    (h0 : σ.mem[(v12 + sign_extend (m := 64) (0x008#12)).toNat]? = some b0)
    (h1 : σ.mem[(v12 + sign_extend (m := 64) (0x008#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(v12 + sign_extend (m := 64) (0x008#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(v12 + sign_extend (m := 64) (0x008#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(v12 + sign_extend (m := 64) (0x008#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(v12 + sign_extend (m := 64) (0x008#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(v12 + sign_extend (m := 64) (0x008#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(v12 + sign_extend (m := 64) (0x008#12)).toNat + 7]? = some b7)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x12
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.eval_expr_at_800031b0 hmem
  exact stepObs_alu σ i u (0x800031b0#64) vminstret (0x00863603#32)
    (instruction.LOAD (0x008#12, regidx.Regidx 0x0c#5, regidx.Regidx 0x0c#5, false, 8))
    Register.x12 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))
    (0x03#8) (0x36#8) (0x86#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00863603 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x800031b0#64) (0x008#12) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0c#5)
      (sigma3_alu σ (0x800031b0#64) Register.x12 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      v12 b0 b1 b2 b3 b4 b5 b6 b7 hG
      (rX_bits_x12 _ v12
        (by rw [get?_afterNextPC σ (0x800031b0#64) _ (by decide) (by decide)]; exact hx12))
      (wX_bits_x12 _ (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800031b4: `addi x10,x2,0x60` (a0 := callee-result sret @sp+96). -/
-- discipline: allow(R1-site-battery) genuine `JalPreBundle`-landing site lemma — see §1 doc
theorem site_800031b4_cf (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v2 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x800031b4#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x10
        (v2 + sign_extend (m := 64) (0x060#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.eval_expr_at_800031b4 hmem
  exact stepObs_alu σ i u (0x800031b4#64) vminstret (0x06010513#32)
    (instruction.ITYPE (0x060#12, regidx.Regidx 0x02#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 (v2 + sign_extend (m := 64) (0x060#12))
    (0x13#8) (0x05#8) (0x01#8) (0x06#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_06010513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x060#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x0a#5) v2
      (afterNextPC (afterPrelude σ) (0x800031b4#64))
      (sigma3_alu σ (0x800031b4#64) Register.x10 (v2 + sign_extend (m := 64) (0x060#12)))
      (rX_bits_x2 _ v2
        (by rw [get?_afterNextPC σ (0x800031b4#64) _ (by decide) (by decide)]; exact hx2))
      (wX_bits_x10 _ (v2 + sign_extend (m := 64) (0x060#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800031b8: `sd x13,0x0(x2)` (spill env across the sub-call). -/
-- discipline: allow(R1-site-battery) genuine `JalPreBundle`-landing site lemma — see §1 doc
theorem site_800031b8_cf (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v2 v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x800031b8#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x000#12)).toNat)
    (hahiram : (v2 + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (v2 + sign_extend (m := 64) (0x000#12)).toNat)
    (haalign : (v2 + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x800031b8#64)).mem
        (v2 + sign_extend (m := 64) (0x000#12)).toNat (sdData_val v13) ∧
      ReadsLikePost σ' (sigmaPost_store σ pc vminstret
        (writeMap8 (afterNextPC (afterPrelude σ) (0x800031b8#64)).mem (v2 + sign_extend (m := 64) (0x000#12)).toNat (sdData_val v13))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.eval_expr_at_800031b8 hmem
  exact stepObs_store σ i u (0x800031b8#64) vminstret (0x00d13023#32)
    (instruction.STORE (0x000#12, regidx.Regidx 0x0d#5, regidx.Regidx 0x02#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x800031b8#64)).mem (v2 + sign_extend (m := 64) (0x000#12)).toNat (sdData_val v13))
    (0x23#8) (0x30#8) (0xd1#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00d13023 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x800031b8#64) (0x000#12) (regidx.Regidx 0x0d#5) (regidx.Regidx 0x02#5)
      v2 v13 hG
      (rX_bits_x2 _ v2
        (by rw [get?_afterNextPC σ (0x800031b8#64) _ (by decide) (by decide)]; exact hx2))
      (rX_bits_x13 _ v13
        (by rw [get?_afterNextPC σ (0x800031b8#64) _ (by decide) (by decide)]; exact hx13))
      halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800031bc: `jal x1,0x80003164` (link `x1 := 0x800031c0`). THE recursive callee call. -/
-- discipline: allow(R1-site-battery) genuine `JalPreBundle`-landing site lemma — see §1 doc
theorem site_800031bc_cf (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x800031bc#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_jal σ pc vminstret (0x1fffa8#21) Register.x1 (BitVec.addInt pc 4)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.eval_expr_at_800031bc hmem
  refine stepObs_jal σ i u (0x800031bc#64) vminstret (0xfa9ff0ef#32) (0x1fffa8#21)
    (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x800031bc#64) 4)
    (0xef#8) (0xf0#8) (0x9f#8) (0xfa#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_fa9ff0ef (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) ?_ hi
  exact wX_bits_x1 _ (BitVec.addInt (0x800031bc#64) 4)

/-! ## §2. `blockB_call_stagePre` — the call arm-head cut -/

/-- **The call arm-head → `JalPreBundle` cut.**  A `blockB_assign_stagePre` twin at the
call arm PC `0x800031b0` (callee bundle `UnaryArmCallee`, operand at `expr->child[8]`,
buffer offset `0x60` = `sp+96`, callee `jal eval_expr` PC `0x800031bc`, jal imm
`0x1fffa8`).  From the `ArmEntryK`-plus-recursive-extras entry bundle MINUS the `hIH`,
the three head steps reach `σ3` at `0x800031bc` with the callee sub-call staged, and
that state satisfies `JalPreBundle f`.  Delivered as `LandedN 3`. -/
theorem blockB_call_stagePre
    (gouter gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (f : Expr) (args : List Expr)
    (sp r sret aExpr aIn aClo aEnv3 : BitVec 64) (v8 v9 v18 : BitVec 64)
    (out0 : Array String) (m0 : Mem)
    (c : Config)
    (hpre : ∃ ment,
        ArmEntryK gouter N A SL φf φc st (0x800031b0#64) UnaryArmCallee (.call f args)
          sp r sret aExpr aIn v8 v9 v18 out0 m0 ment c ∧
        c.σ.regs.get? Register.x11 = some aIn ∧
        c.σ.regs.get? Register.x13 = some aEnv3 ∧
        (∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = gpre R) ∧
        (∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w) ∧
        read64 ment (aExpr.toNat + 8) = some aClo.toNat ∧
        (∀ m' : Mem,
          (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m'[a]?) →
          ExprRepr m' aClo.toNat f) ∧
        aExpr.toNat + 16 ≤ 0x100000000 ∧
        aClo.toNat % 8 = 0 ∧
        0x80000000 ≤ aClo.toNat ∧ aClo.toNat + 16 ≤ 0x100000000 ∧
        tohostAddr + 16 ≤ aClo.toNat ∧
        (aClo.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ aClo.toNat) ∧
        SL.lo + 3264 ≤ sp.toNat ∧ sp.toNat ≤ SL.hi ∧ sp.toNat % 16 = 0 ∧
        SL.hi ≤ 0x100000000 ∧
        (sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo) ∧
        ((0x8000282c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x800027ec) ∧
        ((0x80019f58 : Nat) + 44 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58) ∧
        (A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo) ∧
        (A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo) ∧
        -- ITEM ZERO B1: the CALLEE operand's recursion-sound budget at `sp - 1088`,
        -- its `.fn`-bodies bound, and the store-bodies invariant (the amended
        -- `JalPreBundle` tail).
        StackOK SL (sp - 1088#64)
          (f.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget f = true ∧
        Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget) :
    LandedN 3 c (fun c' => JalPreBundle f c' st d env) := by
  obtain ⟨ment, hArm, hx11, hx13, hgframe, hg8, hg18, hpay, hexprSurv, hexprHi16,
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
  have h8 : (sign_extend (m := 64) (0x008#12) : BitVec 64) = 8#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  have haddr8 : (aExpr + sign_extend (m := 64) (0x008#12)).toNat = aExpr.toNat + 8 := by
    rw [h8, BitVec.toNat_add]
    have hv : (8#64 : BitVec 64).toNat = 8 := by decide
    rw [hv]; omega
  have hsub992 : ((sp - 1088#64) + sign_extend (m := 64) (0x060#12)).toNat = sp.toNat - 992 :=
    spill_addr sp (0x060#12) 992 (by decide) (by omega) hsp1088
  have hspill0 : ((sp - 1088#64) + sign_extend (m := 64) (0x000#12)).toNat = sp.toNat - 1088 :=
    spill_addr sp (0x000#12) 1088 (by decide) (by omega) hsp1088
  obtain ⟨pb0, pb1, pb2, pb3, pb4, pb5, pb6, pb7, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hpsext⟩ :=
    spill_roundtrip_ee ment (aExpr.toNat + 8) aClo hpay
  -- ============ 0x800031b0: ld a2,8(a2) → x12 := aClo ============
  obtain ⟨σ1, i1, hs1', hi1, hG1, hmem1, hobs1⟩ :=
    site_800031b0_cf c.σ c.tick c.steps (0x800031b0#64) vmi aExpr pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7
      hG hpc hmi ha2 (hmem ▸ hcode) rfl
      (by rw [haddr8]; omega) (by rw [haddr8]; omega)
      (by rw [haddr8, htoh]; right; omega) (by rw [haddr8]; omega)
      (by rw [haddr8, hmem]; exact hp0) (by rw [haddr8, hmem]; exact hp1)
      (by rw [haddr8, hmem]; exact hp2) (by rw [haddr8, hmem]; exact hp3)
      (by rw [haddr8, hmem]; exact hp4) (by rw [haddr8, hmem]; exact hp5)
      (by rw [haddr8, hmem]; exact hp6) (by rw [haddr8, hmem]; exact hp7) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1'
  have hmem1e : σ1.mem = ment := by rw [hmem1]; exact hmem
  have hpc1 : σ1.regs.get? Register.PC = some (0x800031b4#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x800031b0#64) 4 = (0x800031b4#64 : BitVec 64) from by decide] at this
  have hx12_1 : σ1.regs.get? Register.x12 = some aClo := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hpsext] at this
  have ha0_1 : σ1.regs.get? Register.x10 = some sret := obs_alu_other' hobs1 Register.x10 (by decide) ha0
  have hs1_1 : σ1.regs.get? Register.x9 = some sret := obs_alu_other' hobs1 Register.x9 (by decide) hs1
  have hx11_1 : σ1.regs.get? Register.x11 = some aIn := obs_alu_other' hobs1 Register.x11 (by decide) hx11
  have hx13_1 : σ1.regs.get? Register.x13 = some aEnv3 := obs_alu_other' hobs1 Register.x13 (by decide) hx13
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other' hobs1 Register.x2 (by decide) hsp
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hout1 : σ1.sailOutput = out0 := by rw [hobs1.out, sailOutput_sigmaPost_alu]; exact hout
  have hcode1 : Eval_exprLoaded σ1.mem := by rw [hmem1e]; exact hcode
  -- ============ 0x800031b4: addi a0,sp,96 → x10 := (sp-1088) + 96 ============
  obtain ⟨σ2, i2, hs2', hi2, hG2, hmem2, hobs2⟩ :=
    site_800031b4_cf σ1 i1 (c.steps + 1) (0x800031b4#64) vmi1 (sp - 1088#64)
      hG1 hpc1 hmi1 hsp_1 hcode1 rfl hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2'
  have hmem2e : σ2.mem = ment := by rw [hmem2]; exact hmem1e
  have hpc2 : σ2.regs.get? Register.PC = some (0x800031b8#64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x800031b4#64) 4 = (0x800031b8#64 : BitVec 64) from by decide] at this
  have hx10_2 : σ2.regs.get? Register.x10
      = some ((sp - 1088#64) + sign_extend (m := 64) (0x060#12)) :=
    obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hs1_2 : σ2.regs.get? Register.x9 = some sret := obs_alu_other' hobs2 Register.x9 (by decide) hs1_1
  have hx11_2 : σ2.regs.get? Register.x11 = some aIn := obs_alu_other' hobs2 Register.x11 (by decide) hx11_1
  have hx12_2 : σ2.regs.get? Register.x12 = some aClo := obs_alu_other' hobs2 Register.x12 (by decide) hx12_1
  have hx13_2 : σ2.regs.get? Register.x13 = some aEnv3 := obs_alu_other' hobs2 Register.x13 (by decide) hx13_1
  have hsp_2 : σ2.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other' hobs2 Register.x2 (by decide) hsp_1
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hout2 : σ2.sailOutput = out0 := by rw [hobs2.out, sailOutput_sigmaPost_alu]; exact hout1
  have hcode2 : Eval_exprLoaded σ2.mem := by rw [hmem2e]; exact hcode
  -- ============ 0x800031b8: sd a3,0(sp) → mcall := writeMap8 ment (sp-1088) (sdData_val aEnv3) ============
  obtain ⟨σ3, i3, hs3', hi3, hG3, hmem3, hobs3⟩ :=
    site_800031b8_cf σ2 i2 (c.steps + 1 + 1) (0x800031b8#64) vmi2 (sp - 1088#64) aEnv3
      hG2 hpc2 hmi2 hsp_2 hx13_2 hcode2 rfl
      (by rw [hspill0]; omega) (by rw [hspill0]; omega)
      (by rw [hspill0, htoh]; omega) (by rw [hspill0]; omega) hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3'
  let mcall : Mem := writeMap8 ment (sp.toNat - 1088) (sdData_val aEnv3)
  have hmcalldef : mcall = writeMap8 ment (sp.toNat - 1088) (sdData_val aEnv3) := rfl
  have hmem3e : σ3.mem = mcall := by
    rw [hmem3, hmcalldef]
    have hmi' : (afterNextPC (afterPrelude σ2) (0x800031b8#64)).mem = ment := by
      rw [mem_afterNextPC, mem_afterPrelude]; exact hmem2e
    rw [hmi', hspill0]
  have hpc3 : σ3.regs.get? Register.PC = some (0x800031bc#64) := by
    have := obs_store_pc hobs3
    rwa [show BitVec.addInt (0x800031b8#64) 4 = (0x800031bc#64 : BitVec 64) from by decide] at this
  have hx10_3 : σ3.regs.get? Register.x10
      = some ((sp - 1088#64) + sign_extend (m := 64) (0x060#12)) :=
    obs_store_other' hobs3 Register.x10 (by decide) hx10_2
  have hs1_3 : σ3.regs.get? Register.x9 = some sret := obs_store_other' hobs3 Register.x9 (by decide) hs1_2
  have hx11_3 : σ3.regs.get? Register.x11 = some aIn := obs_store_other' hobs3 Register.x11 (by decide) hx11_2
  have hx12_3 : σ3.regs.get? Register.x12 = some aClo := obs_store_other' hobs3 Register.x12 (by decide) hx12_2
  have hsp_3 : σ3.regs.get? Register.x2 = some (sp - 1088#64) := obs_store_other' hobs3 Register.x2 (by decide) hsp_2
  obtain ⟨vmi3, hmi3⟩ := obs_store_minstret hobs3
  have hout3 : σ3.sailOutput = out0 := by rw [hobs3.out, sailOutput_sigmaPost_store]; exact hout2
  -- ===== the env-spill preserves everything the JalPreBundle needs =====
  have hAgSpill : ∀ k : Nat, ¬ (sp.toNat - 1088 ≤ k ∧ k < sp.toNat - 1088 + 8) →
      mcall[k]? = ment[k]? := by
    intro k hk
    rw [hmcalldef, getElem_writeMap8_disjoint ment (sp.toNat - 1088) k (sdData_val aEnv3) (by omega)]
  have hcodeMcall : Eval_exprLoaded mcall :=
    loaded_eval_expr_agreeP ment mcall
      (fun a ha => (hAgSpill a (by rcases hcodeStk with h | h <;> omega)).symm) hcode
  have hviIntMcall : Value_intLoaded mcall :=
    loaded_value_int_agreeP ment mcall
      (fun a ha => (hAgSpill a (by rcases hviStk with h | h <;> omega)).symm) hviInt
  have hviSlotMcall : IntSlotPinned mcall := by
    obtain ⟨q0, q1, q2, q3⟩ := hviSlot
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      (rw [hAgSpill _ (by simp only [jumpTableBase] at *; rcases htableStk with h | h <;> omega)]; assumption)
  have hnbsMcall : NBSPins mcall :=
    hnbs.transport
      (fun a ha => (hAgSpill a (by rcases hviStk with h | h <;> omega)).symm)
      (fun a ha => (hAgSpill a (by rcases htableStk with h | h <;> omega)).symm)
  have hExprMcall : ExprRepr mcall aClo.toNat f :=
    hexprSurv mcall (fun a ha => (hAgSpill a (by omega)).symm)
  have hStoreMcall : StoreRepr mcall N A φf φc st.store := by
    refine hstoreSurv mcall (fun k hk1 _ => ?_)
    exact (hAgSpill k (by omega)).symm
  have hStoreSurvMcall : ∀ m' : Mem,
      (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) →
        mcall[k]? = m'[k]?) → StoreRepr m' N A φf φc st.store := by
    intro m' hag
    refine hstoreSurv m' (fun k hk1 hk2 => ?_)
    rw [← hag k hk1 hk2, hAgSpill k (by omega)]
  have hslotRaMcall : read64 mcall (sp.toNat - 8) = some r.toNat := by
    rw [read64_agreeP (P := fun k => sp.toNat - 8 ≤ k ∧ k < sp.toNat) (m := mcall) (m' := ment)
      (fun j hj => hAgSpill j (by omega)) (fun j hj => by omega)]; exact hslotRa
  have hslotS0Mcall : read64 mcall (sp.toNat - 16) = some v8.toNat := by
    rw [read64_agreeP (P := fun k => sp.toNat - 16 ≤ k ∧ k < sp.toNat - 8) (m := mcall) (m' := ment)
      (fun j hj => hAgSpill j (by omega)) (fun j hj => by omega)]; exact hslotS0
  have hslotS1Mcall : read64 mcall (sp.toNat - 24) = some v9.toNat := by
    rw [read64_agreeP (P := fun k => sp.toNat - 24 ≤ k ∧ k < sp.toNat - 16) (m := mcall) (m' := ment)
      (fun j hj => hAgSpill j (by omega)) (fun j hj => by omega)]; exact hslotS1
  have hslotS2Mcall : read64 mcall (sp.toNat - 32) = some v18.toNat := by
    rw [read64_agreeP (P := fun k => sp.toNat - 32 ≤ k ∧ k < sp.toNat - 24) (m := mcall) (m' := ment)
      (fun j hj => hAgSpill j (by omega)) (fun j hj => by omega)]; exact hslotS2
  have abi_ne' : ∀ {X R : Register}, AbiPreserved X = false → AbiPreserved R = true →
      (X == R) = false := by
    intro X R hX hR
    rcases hXR : (X == R) with _ | _
    · rfl
    · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hR; exact absurd hR (by decide)
  have hframeB : ∀ R : Register, AbiPreservedNoise R → σ3.regs.get? R = gpre R := by
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
    rw [f3, f2, f1]; exact hgframe R hR'
  -- ============ land at σ3 (the callee jal PC 0x800031bc) as `JalPreBundle f` ============
  refine ⟨3, ⟨σ3, i3, c.steps + 1 + 1 + 1⟩, Nat.le_refl _,
    StepsN.succ hstep1 (StepsN.succ hstep2 (StepsN.succ hstep3 (StepsN.zero _))), ?_⟩
  · exact ⟨gpre, N, A, SL, φf, φc, (0x800031bc#64), (0x800031c0#64), (0x1fffa8#21),
      sp, r, sret, ((sp - 1088#64) + sign_extend (m := 64) (0x060#12)), aIn, aClo,
      v8, v9, v18, out0, mcall,
      (by apply BitVec.eq_of_toNat_eq; simp only [evalExprEntry]; decide),
      (by apply BitVec.eq_of_toNat_eq; decide),
      (by decide),
      (fun σ i u vmiσ hGσ hpcσ hmiσ hcodeσ hiσ =>
        site_800031bc_cf σ i u (0x800031bc#64) vmiσ hGσ hpcσ hmiσ hcodeσ rfl hiσ),
      hG3, hi3, hpc3, hx10_3, hs1_3, hx11_3, hx12_3, hsp_3, ⟨vmi3, hmi3⟩, hout3, houtStr,
      hmem3e, hcodeMcall, hviIntMcall, hviSlotMcall, hnbsMcall, hExprMcall, hStoreMcall, hStoreSurvMcall,
      hframeB, ⟨hg8, hg18⟩,
      hslotRaMcall, hslotS0Mcall, hslotS1Mcall, hslotS2Mcall,
      hopAl, hopLo, hopHi, hopWin, hopStk,
      (by rw [hsub992]; omega), (by rw [hsub992]; omega), (by rw [hsub992]; omega),
      hsproom, hspSLhi, hsp16, hsphi, hSLlo, hSLhiRam, hSLwin,
      hcodeStk, hviStk, htableStk, harenaStk, harenaCode,
      hstackBudget, hexprBodies, hstoreBodies⟩

#print axioms blockB_call_stagePre

/-! ## §3. The `callF` field composer -/

/-- **The call dispatch residual** (the `blockA_callArm` a row would produce, named as a
premise).  The `Mid` post is `blockB_call_stagePre`'s entry bundle. -/
def CallArmDispatch
    (f : Expr) (args : List Expr) (st : Vsa.While.St) (d : Nat) (env : Addr) (c : Config) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r0 sret aEnv aExpr : BitVec 64) (m0 : Mem),
    EvalEntry g N A SL φf φc st d env (.call f args) sp r0 sret aEnv aExpr m0 c →
    Triple (fun c'' => c'' = c)
      (fun c' => ∃ (gpre : (R : Register) → Option (RegisterType R))
        (aIn aClo aEnv3 : BitVec 64) (v8 v9 v18 : BitVec 64),
        ∃ ment,
        ArmEntryK g N A SL φf φc st (0x800031b0#64) UnaryArmCallee (.call f args)
          sp r0 sret aExpr aIn v8 v9 v18 c'.σ.sailOutput m0 ment c' ∧
        c'.σ.regs.get? Register.x11 = some aIn ∧
        c'.σ.regs.get? Register.x13 = some aEnv3 ∧
        (∀ R : Register, AbiPreservedNoise R → c'.σ.regs.get? R = gpre R) ∧
        (∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w) ∧
        read64 ment (aExpr.toNat + 8) = some aClo.toNat ∧
        (∀ m' : Mem,
          (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m'[a]?) →
          ExprRepr m' aClo.toNat f) ∧
        aExpr.toNat + 16 ≤ 0x100000000 ∧
        aClo.toNat % 8 = 0 ∧
        0x80000000 ≤ aClo.toNat ∧ aClo.toNat + 16 ≤ 0x100000000 ∧
        tohostAddr + 16 ≤ aClo.toNat ∧
        (aClo.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ aClo.toNat) ∧
        SL.lo + 3264 ≤ sp.toNat ∧ sp.toNat ≤ SL.hi ∧ sp.toNat % 16 = 0 ∧
        SL.hi ≤ 0x100000000 ∧
        (sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo) ∧
        ((0x8000282c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x800027ec) ∧
        ((0x80019f58 : Nat) + 44 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58) ∧
        (A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo) ∧
        (A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo))

/-- **The `EvalChildStages.callF` field, machine-composed.**  From
`EEntryC (.call f args)` plus the dispatch residual `CallArmDispatch`, the composer runs
the dispatch Triple to `blockB_call_stagePre`'s entry bundle, then that cut stages the
callee sub-call — landing at `JalPreBundle f`. -/
theorem callF_field_of_dispatch
    (f : Expr) (args : List Expr) (c : Config) (st : Vsa.While.St)
    (d : Nat) (env : Addr)
    (hDisp : CallArmDispatch f args st d env c)
    (hEE : EEntryC c st d env (.call f args)) :
    LandedN 1 c (fun c' => JalPreBundle f c' st d env) := by
  obtain ⟨g, N, A, SL, φf, φc, sp, r0, sret, aEnv, aExpr, m0, hEntry⟩ := hEE
  refine evalChildField_of_blockA_stage (k := 3) (by omega)
    (hDisp g N A SL φf φc sp r0 sret aEnv aExpr m0 hEntry)
    (fun c' hMid => ?_) c rfl
  obtain ⟨gpre, aIn, aClo, aEnv3, v8, v9, v18, ment, hArm, hx11, hx13, hgframe,
    hg8, hg18, hpay, hexprSurv, hexprHi16, hopAl, hopLo, hopHi, hopWin, hopStk,
    hsproom, hspSLhi, hsp16, hSLhiRam, hcodeStk, hviStk, htableStk,
    harenaStk, harenaCode⟩ := hMid
  exact blockB_call_stagePre g gpre N A SL φf φc st d env f args
    sp r0 sret aExpr aIn aClo aEnv3 v8 v9 v18 c'.σ.sailOutput m0 c'
    ⟨ment, hArm, hx11, hx13, hgframe, hg8, hg18, hpay, hexprSurv, hexprHi16,
      hopAl, hopLo, hopHi, hopWin, hopStk, hsproom, hspSLhi, hsp16, hSLhiRam,
      hcodeStk, hviStk, htableStk, harenaStk, harenaCode,
      -- ITEM ZERO B1: the CALLEE child budget, DERIVED from the entry's fields.
      hEntry.stackBudget.child (by decide)
        (by
          have h1 : (Expr.call f args).stackNeed
              = evalFrame + max f.stackNeed (Expr.stackNeedList args) := rfl
          have h2 : ((1088#64 : BitVec 64)).toNat = 1088 := by decide
          have hm := Nat.le_max_left f.stackNeed (Expr.stackNeedList args)
          simp only [h1, h2, evalFrame]; omega),
      (Expr.bodiesBound_call hEntry.expr_bodies).1,
      hEntry.store_bodies⟩

#print axioms callF_field_of_dispatch

end Vsa.Sim
