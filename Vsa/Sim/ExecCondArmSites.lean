import Vsa.Sim.Exec_stmtSites2
import Vsa.Sim.DecodeTable.Batch03Part19
import Vsa.Sim.DecodeTable.Batch05Part14
import Vsa.Sim.DecodeTable.Batch02Part04
import Vsa.Sim.DecodeTable.Batch01Part14
import Vsa.Sim.DecodeTable.Batch07Part17
import Vsa.Sim.DecodeTable.Batch08Part03
import Vsa.Sim.DecodeTable.Batch08Part16
import Vsa.Sim.DecodeTable.Batch06Part22
import Vsa.Sim.DecodeTable.Batch15Part24
import Vsa.Sim.DecodeTable.Batch13Part18
import Vsa.Sim.DecodeTable.Batch15Part15

/-!
# `ExecCondArmSites` — per-PC `_es` site batteries for the exec if/while/for cond arms

The `stmtIfCond` (`0x800041e8`), `stmtWhileCond` (`0x8000403c`) and `flCond`
(`0x8000426c`) arm heads reach `jal eval_expr` but their sites were not landed
before wave 41.  Each is a `ld/mv/addi/jal` (+ optional `beqz`) site — identical
class to the landed `Exec_stmtSites*` `_es` batteries, just at new PCs.  The byte
lemmas `exec_stmt_at_*` and the `decode_*` lemmas already exist.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
Axioms of every theorem ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps StepsN)

namespace Vsa.Sim

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

-- discipline: allow(R5-stepobs-volume) this file is a per-PC `_es` StepObs site
-- battery — the SAME class as the grandfathered `ExecIfSites`/`ExecWhileSites`/
-- `Exec_stmtSites*` (all in scripts/discipline_grandfather.txt).  The block-
-- reflection layer (block_facts/#derive_case) cannot land these rich
-- `sigmaPost_alu`/`sigmaPost_jal`/`sigmaPost_branch_nottaken` ReadsLikePost site
-- lemmas for the deeply-typed exec-arm loads; they are the leaf primitives the seg
-- layer itself is built from.  Each site carries its own R1-site-battery allow.
-- discipline: allow(R7-conj-tower-def) the ∃'s here are the per-site `∃ σ' i', Step …`
-- existential POSTS of the StepObs primitives (not anonymous entry/exit towers); every
-- one is the fixed `stepObs_*` output shape, consumed positionally by the seg layer.

/-! ## stmtIfCond arm (0x800041e8): `ld a2,8(s0); mv a3,s3; mv a1,s1; addi a0,sp,56; jal` -/

/-- 0x800041e8: `ld x12,0x8(x8)` (a2 := stmt->cond). -/
-- discipline: allow(R1-site-battery) `ExecJalPreBundle`-landing site (LogicalSites class); reflection cannot land the rich repr
theorem site_800041e8_es (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v8 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx8 : σ.regs.get? Register.x8 = some v8)
    (hmem : Vsa.Sim.Code.Exec_stmtLoaded σ.mem)
    (hpcv : pc = (0x800041e8#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v8 + sign_extend (m := 64) (0x008#12)).toNat)
    (hhiram : (v8 + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v8 + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v8 + sign_extend (m := 64) (0x008#12)).toNat)
    (halign : (v8 + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0)
    (h0 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat]? = some b0)
    (h1 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat + 7]? = some b7)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x12
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.exec_stmt_at_800041e8 hmem
  exact stepObs_alu σ i u (0x800041e8#64) vminstret (0x00843603#32)
    (instruction.LOAD (0x008#12, regidx.Regidx 0x08#5, regidx.Regidx 0x0c#5, false, 8))
    Register.x12 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))
    (0x03#8) (0x36#8) (0x84#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00843603 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x800041e8#64) (0x008#12) (regidx.Regidx 0x08#5) (regidx.Regidx 0x0c#5)
      (sigma3_alu σ (0x800041e8#64) Register.x12 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      v8 b0 b1 b2 b3 b4 b5 b6 b7 hG
      (rX_bits_x8 _ v8
        (by rw [get?_afterNextPC σ (0x800041e8#64) _ (by decide) (by decide)]; exact hx8))
      (wX_bits_x12 _ (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800041ec: `addi x13,x19,0x0` (mv a3,s3). -/
-- discipline: allow(R1-site-battery) `ExecJalPreBundle`-landing site
theorem site_800041ec_es (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v19 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx19 : σ.regs.get? Register.x19 = some v19)
    (hmem : Vsa.Sim.Code.Exec_stmtLoaded σ.mem)
    (hpcv : pc = (0x800041ec#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x13
        (v19 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.exec_stmt_at_800041ec hmem
  exact stepObs_alu σ i u (0x800041ec#64) vminstret (0x00098693#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x13#5, regidx.Regidx 0x0d#5, iop.ADDI))
    Register.x13 (v19 + sign_extend (m := 64) (0x000#12))
    (0x93#8) (0x86#8) (0x09#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00098693 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x13#5) (regidx.Regidx 0x0d#5) v19
      (afterNextPC (afterPrelude σ) (0x800041ec#64))
      (sigma3_alu σ (0x800041ec#64) Register.x13 (v19 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x19 _ v19
        (by rw [get?_afterNextPC σ (0x800041ec#64) _ (by decide) (by decide)]; exact hx19))
      (wX_bits_x13 _ (v19 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800041f0: `addi x11,x9,0x0` (mv a1,s1). -/
-- discipline: allow(R1-site-battery) `ExecJalPreBundle`-landing site
theorem site_800041f0_es (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v9 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx9 : σ.regs.get? Register.x9 = some v9)
    (hmem : Vsa.Sim.Code.Exec_stmtLoaded σ.mem)
    (hpcv : pc = (0x800041f0#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x11
        (v9 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.exec_stmt_at_800041f0 hmem
  exact stepObs_alu σ i u (0x800041f0#64) vminstret (0x00048593#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x09#5, regidx.Regidx 0x0b#5, iop.ADDI))
    Register.x11 (v9 + sign_extend (m := 64) (0x000#12))
    (0x93#8) (0x85#8) (0x04#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00048593 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x09#5) (regidx.Regidx 0x0b#5) v9
      (afterNextPC (afterPrelude σ) (0x800041f0#64))
      (sigma3_alu σ (0x800041f0#64) Register.x11 (v9 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x9 _ v9
        (by rw [get?_afterNextPC σ (0x800041f0#64) _ (by decide) (by decide)]; exact hx9))
      (wX_bits_x11 _ (v9 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800041f4: `addi x10,x2,0x38` (addi a0,sp,56). -/
-- discipline: allow(R1-site-battery) `ExecJalPreBundle`-landing site
theorem site_800041f4_es (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v2 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hmem : Vsa.Sim.Code.Exec_stmtLoaded σ.mem)
    (hpcv : pc = (0x800041f4#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x10
        (v2 + sign_extend (m := 64) (0x038#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.exec_stmt_at_800041f4 hmem
  exact stepObs_alu σ i u (0x800041f4#64) vminstret (0x03810513#32)
    (instruction.ITYPE (0x038#12, regidx.Regidx 0x02#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 (v2 + sign_extend (m := 64) (0x038#12))
    (0x13#8) (0x05#8) (0x81#8) (0x03#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_03810513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x038#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x0a#5) v2
      (afterNextPC (afterPrelude σ) (0x800041f4#64))
      (sigma3_alu σ (0x800041f4#64) Register.x10 (v2 + sign_extend (m := 64) (0x038#12)))
      (rX_bits_x2 _ v2
        (by rw [get?_afterNextPC σ (0x800041f4#64) _ (by decide) (by decide)]; exact hx2))
      (wX_bits_x10 _ (v2 + sign_extend (m := 64) (0x038#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800041f8: `jal x1,0x80003164` (link `x1 := 0x800041fc`). -/
-- discipline: allow(R1-site-battery) `ExecJalPreBundle`-landing site
theorem site_800041f8_es (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Vsa.Sim.Code.Exec_stmtLoaded σ.mem)
    (hpcv : pc = (0x800041f8#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_jal σ pc vminstret (0x1fef6c#21) Register.x1 (BitVec.addInt pc 4)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.exec_stmt_at_800041f8 hmem
  refine stepObs_jal σ i u (0x800041f8#64) vminstret (0xf6dfe0ef#32) (0x1fef6c#21)
    (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x800041f8#64) 4)
    (0xef#8) (0xe0#8) (0xdf#8) (0xf6#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_f6dfe0ef (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) ?_ hi
  exact wX_bits_x1 _ (BitVec.addInt (0x800041f8#64) 4)

/-! ## stmtWhileCond arm (0x8000403c): `ld a2,8(s0); mv a3,s3; addi a0,sp,80; mv a1,s1; jal` -/

/-- 0x8000403c: `ld x12,0x8(x8)` (a2 := while cond). -/
-- discipline: allow(R1-site-battery) `ExecJalPreBundle`-landing site
theorem site_8000403c_es (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v8 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx8 : σ.regs.get? Register.x8 = some v8)
    (hmem : Vsa.Sim.Code.Exec_stmtLoaded σ.mem)
    (hpcv : pc = (0x8000403c#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v8 + sign_extend (m := 64) (0x008#12)).toNat)
    (hhiram : (v8 + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v8 + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v8 + sign_extend (m := 64) (0x008#12)).toNat)
    (halign : (v8 + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0)
    (h0 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat]? = some b0)
    (h1 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(v8 + sign_extend (m := 64) (0x008#12)).toNat + 7]? = some b7)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x12
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.exec_stmt_at_8000403c hmem
  exact stepObs_alu σ i u (0x8000403c#64) vminstret (0x00843603#32)
    (instruction.LOAD (0x008#12, regidx.Regidx 0x08#5, regidx.Regidx 0x0c#5, false, 8))
    Register.x12 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))
    (0x03#8) (0x36#8) (0x84#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00843603 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x8000403c#64) (0x008#12) (regidx.Regidx 0x08#5) (regidx.Regidx 0x0c#5)
      (sigma3_alu σ (0x8000403c#64) Register.x12 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      v8 b0 b1 b2 b3 b4 b5 b6 b7 hG
      (rX_bits_x8 _ v8
        (by rw [get?_afterNextPC σ (0x8000403c#64) _ (by decide) (by decide)]; exact hx8))
      (wX_bits_x12 _ (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80004040: `addi x13,x19,0x0` (mv a3,s3). -/
-- discipline: allow(R1-site-battery) `ExecJalPreBundle`-landing site
theorem site_80004040_es (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v19 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx19 : σ.regs.get? Register.x19 = some v19)
    (hmem : Vsa.Sim.Code.Exec_stmtLoaded σ.mem)
    (hpcv : pc = (0x80004040#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x13
        (v19 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.exec_stmt_at_80004040 hmem
  exact stepObs_alu σ i u (0x80004040#64) vminstret (0x00098693#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x13#5, regidx.Regidx 0x0d#5, iop.ADDI))
    Register.x13 (v19 + sign_extend (m := 64) (0x000#12))
    (0x93#8) (0x86#8) (0x09#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00098693 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x13#5) (regidx.Regidx 0x0d#5) v19
      (afterNextPC (afterPrelude σ) (0x80004040#64))
      (sigma3_alu σ (0x80004040#64) Register.x13 (v19 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x19 _ v19
        (by rw [get?_afterNextPC σ (0x80004040#64) _ (by decide) (by decide)]; exact hx19))
      (wX_bits_x13 _ (v19 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80004044: `addi x10,x2,0x50` (addi a0,sp,80). -/
-- discipline: allow(R1-site-battery) `ExecJalPreBundle`-landing site
theorem site_80004044_es (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v2 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hmem : Vsa.Sim.Code.Exec_stmtLoaded σ.mem)
    (hpcv : pc = (0x80004044#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x10
        (v2 + sign_extend (m := 64) (0x050#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.exec_stmt_at_80004044 hmem
  exact stepObs_alu σ i u (0x80004044#64) vminstret (0x05010513#32)
    (instruction.ITYPE (0x050#12, regidx.Regidx 0x02#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 (v2 + sign_extend (m := 64) (0x050#12))
    (0x13#8) (0x05#8) (0x01#8) (0x05#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_05010513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x050#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x0a#5) v2
      (afterNextPC (afterPrelude σ) (0x80004044#64))
      (sigma3_alu σ (0x80004044#64) Register.x10 (v2 + sign_extend (m := 64) (0x050#12)))
      (rX_bits_x2 _ v2
        (by rw [get?_afterNextPC σ (0x80004044#64) _ (by decide) (by decide)]; exact hx2))
      (wX_bits_x10 _ (v2 + sign_extend (m := 64) (0x050#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80004048: `addi x11,x9,0x0` (mv a1,s1). -/
-- discipline: allow(R1-site-battery) `ExecJalPreBundle`-landing site
theorem site_80004048_es (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v9 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx9 : σ.regs.get? Register.x9 = some v9)
    (hmem : Vsa.Sim.Code.Exec_stmtLoaded σ.mem)
    (hpcv : pc = (0x80004048#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x11
        (v9 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.exec_stmt_at_80004048 hmem
  exact stepObs_alu σ i u (0x80004048#64) vminstret (0x00048593#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x09#5, regidx.Regidx 0x0b#5, iop.ADDI))
    Register.x11 (v9 + sign_extend (m := 64) (0x000#12))
    (0x93#8) (0x85#8) (0x04#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00048593 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x09#5) (regidx.Regidx 0x0b#5) v9
      (afterNextPC (afterPrelude σ) (0x80004048#64))
      (sigma3_alu σ (0x80004048#64) Register.x11 (v9 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x9 _ v9
        (by rw [get?_afterNextPC σ (0x80004048#64) _ (by decide) (by decide)]; exact hx9))
      (wX_bits_x11 _ (v9 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x8000404c: `jal x1,0x80003164` (link `x1 := 0x80004050`). -/
-- discipline: allow(R1-site-battery) `ExecJalPreBundle`-landing site
theorem site_8000404c_es (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Vsa.Sim.Code.Exec_stmtLoaded σ.mem)
    (hpcv : pc = (0x8000404c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_jal σ pc vminstret (0x1ff118#21) Register.x1 (BitVec.addInt pc 4)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.exec_stmt_at_8000404c hmem
  refine stepObs_jal σ i u (0x8000404c#64) vminstret (0x918ff0ef#32) (0x1ff118#21)
    (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x8000404c#64) 4)
    (0xef#8) (0xf0#8) (0x8f#8) (0x91#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_918ff0ef (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) ?_ hi
  exact wX_bits_x1 _ (BitVec.addInt (0x8000404c#64) 4)

/-! ## flCond arm (0x8000426c): `ld a2,16(s0); beqz a2; mv a3,s3; addi a0,sp,104; mv a1,s1; jal` -/

/-- 0x8000426c: `ld x12,0x10(x8)` (a2 := for-cond). -/
-- discipline: allow(R1-site-battery) `ExecJalPreBundle`-landing site
theorem site_8000426c_es (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v8 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx8 : σ.regs.get? Register.x8 = some v8)
    (hmem : Vsa.Sim.Code.Exec_stmtLoaded σ.mem)
    (hpcv : pc = (0x8000426c#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v8 + sign_extend (m := 64) (0x010#12)).toNat)
    (hhiram : (v8 + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v8 + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v8 + sign_extend (m := 64) (0x010#12)).toNat)
    (halign : (v8 + sign_extend (m := 64) (0x010#12)).toNat % 8 = 0)
    (h0 : σ.mem[(v8 + sign_extend (m := 64) (0x010#12)).toNat]? = some b0)
    (h1 : σ.mem[(v8 + sign_extend (m := 64) (0x010#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(v8 + sign_extend (m := 64) (0x010#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(v8 + sign_extend (m := 64) (0x010#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(v8 + sign_extend (m := 64) (0x010#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(v8 + sign_extend (m := 64) (0x010#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(v8 + sign_extend (m := 64) (0x010#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(v8 + sign_extend (m := 64) (0x010#12)).toNat + 7]? = some b7)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x12
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.exec_stmt_at_8000426c hmem
  exact stepObs_alu σ i u (0x8000426c#64) vminstret (0x01043603#32)
    (instruction.LOAD (0x010#12, regidx.Regidx 0x08#5, regidx.Regidx 0x0c#5, false, 8))
    Register.x12 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))
    (0x03#8) (0x36#8) (0x04#8) (0x01#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_01043603 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x8000426c#64) (0x010#12) (regidx.Regidx 0x08#5) (regidx.Regidx 0x0c#5)
      (sigma3_alu σ (0x8000426c#64) Register.x12 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      v8 b0 b1 b2 b3 b4 b5 b6 b7 hG
      (rX_bits_x8 _ v8
        (by rw [get?_afterNextPC σ (0x8000426c#64) _ (by decide) (by decide)]; exact hx8))
      (wX_bits_x12 _ (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80004270: `beq x12,x0` (NOT taken). -/
-- discipline: allow(R1-site-battery) `ExecJalPreBundle`-landing site
theorem site_80004270_nottaken_es (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : Vsa.Sim.Code.Exec_stmtLoaded σ.mem)
    (hpcv : pc = (0x80004270#64 : BitVec 64))
    (hv : (v12 == (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.exec_stmt_at_80004270 hmem
  exact stepObs_branch_nottaken σ i u (0x80004270#64) vminstret (0x0038#13)
    (regidx.Regidx 0x0c#5) (regidx.Regidx 0x00#5) bop.BEQ (0x02060c63#32)
    (0x63#8) (0x0c#8) (0x06#8) (0x02#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_02060c63 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_btype_beq_nottaken (0x0038#13) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x00#5)
      v12 (0#64) (afterNextPC (afterPrelude σ) (0x80004270#64))
      (rX_bits_x12 _ v12
        (by rw [get?_afterNextPC σ (0x80004270#64) _ (by decide) (by decide)]; exact hx12))
      (rX_bits_zero _)
      hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80004274: `addi x13,x19,0x0` (mv a3,s3). -/
-- discipline: allow(R1-site-battery) `ExecJalPreBundle`-landing site
theorem site_80004274_es (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v19 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx19 : σ.regs.get? Register.x19 = some v19)
    (hmem : Vsa.Sim.Code.Exec_stmtLoaded σ.mem)
    (hpcv : pc = (0x80004274#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x13
        (v19 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.exec_stmt_at_80004274 hmem
  exact stepObs_alu σ i u (0x80004274#64) vminstret (0x00098693#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x13#5, regidx.Regidx 0x0d#5, iop.ADDI))
    Register.x13 (v19 + sign_extend (m := 64) (0x000#12))
    (0x93#8) (0x86#8) (0x09#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00098693 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x13#5) (regidx.Regidx 0x0d#5) v19
      (afterNextPC (afterPrelude σ) (0x80004274#64))
      (sigma3_alu σ (0x80004274#64) Register.x13 (v19 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x19 _ v19
        (by rw [get?_afterNextPC σ (0x80004274#64) _ (by decide) (by decide)]; exact hx19))
      (wX_bits_x13 _ (v19 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80004278: `addi x10,x2,0x68` (addi a0,sp,104). -/
-- discipline: allow(R1-site-battery) `ExecJalPreBundle`-landing site
theorem site_80004278_es (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v2 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hmem : Vsa.Sim.Code.Exec_stmtLoaded σ.mem)
    (hpcv : pc = (0x80004278#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x10
        (v2 + sign_extend (m := 64) (0x068#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.exec_stmt_at_80004278 hmem
  exact stepObs_alu σ i u (0x80004278#64) vminstret (0x06810513#32)
    (instruction.ITYPE (0x068#12, regidx.Regidx 0x02#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 (v2 + sign_extend (m := 64) (0x068#12))
    (0x13#8) (0x05#8) (0x81#8) (0x06#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_06810513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x068#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x0a#5) v2
      (afterNextPC (afterPrelude σ) (0x80004278#64))
      (sigma3_alu σ (0x80004278#64) Register.x10 (v2 + sign_extend (m := 64) (0x068#12)))
      (rX_bits_x2 _ v2
        (by rw [get?_afterNextPC σ (0x80004278#64) _ (by decide) (by decide)]; exact hx2))
      (wX_bits_x10 _ (v2 + sign_extend (m := 64) (0x068#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x8000427c: `addi x11,x9,0x0` (mv a1,s1). -/
-- discipline: allow(R1-site-battery) `ExecJalPreBundle`-landing site
theorem site_8000427c_es (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v9 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx9 : σ.regs.get? Register.x9 = some v9)
    (hmem : Vsa.Sim.Code.Exec_stmtLoaded σ.mem)
    (hpcv : pc = (0x8000427c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x11
        (v9 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.exec_stmt_at_8000427c hmem
  exact stepObs_alu σ i u (0x8000427c#64) vminstret (0x00048593#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x09#5, regidx.Regidx 0x0b#5, iop.ADDI))
    Register.x11 (v9 + sign_extend (m := 64) (0x000#12))
    (0x93#8) (0x85#8) (0x04#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00048593 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x09#5) (regidx.Regidx 0x0b#5) v9
      (afterNextPC (afterPrelude σ) (0x8000427c#64))
      (sigma3_alu σ (0x8000427c#64) Register.x11 (v9 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x9 _ v9
        (by rw [get?_afterNextPC σ (0x8000427c#64) _ (by decide) (by decide)]; exact hx9))
      (wX_bits_x11 _ (v9 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80004280: `jal x1,0x80003164` (link `x1 := 0x80004284`). -/
-- discipline: allow(R1-site-battery) `ExecJalPreBundle`-landing site
theorem site_80004280_es (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Vsa.Sim.Code.Exec_stmtLoaded σ.mem)
    (hpcv : pc = (0x80004280#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_jal σ pc vminstret (0x1feee4#21) Register.x1 (BitVec.addInt pc 4)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.exec_stmt_at_80004280 hmem
  refine stepObs_jal σ i u (0x80004280#64) vminstret (0xee5fe0ef#32) (0x1feee4#21)
    (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x80004280#64) 4)
    (0xef#8) (0xe0#8) (0x5f#8) (0xee#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_ee5fe0ef (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) ?_ hi
  exact wX_bits_x1 _ (BitVec.addInt (0x80004280#64) 4)

end Vsa.Sim
