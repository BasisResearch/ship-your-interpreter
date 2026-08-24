import Vsa.Sim.StepObs
import Vsa.Sim.ExecuteAlu
import Vsa.Sim.ExecuteBranch
import Vsa.Sim.ExecuteLoad
import Vsa.Sim.MemLoadTotal
import Vsa.Sim.RegAccess
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part16
import Vsa.Sim.DecodeTable.Batch01Part28
import Vsa.Sim.DecodeTable.Batch02Part26
import Vsa.Sim.DecodeTable.Batch03Part15
import Vsa.Sim.DecodeTable.Batch03Part16
import Vsa.Sim.DecodeTable.Batch03Part23
import Vsa.Sim.DecodeTable.Batch04Part13
import Vsa.Sim.DecodeTable.Batch04Part14
import Vsa.Sim.DecodeTable.Batch04Part16
import Vsa.Sim.DecodeTable.Batch04Part18
import Vsa.Sim.DecodeTable.Batch04Part19
import Vsa.Sim.DecodeTable.Batch04Part29
import Vsa.Sim.DecodeTable.Batch05Part01
import Vsa.Sim.DecodeTable.Batch06Part25
import Vsa.Sim.DecodeTable.Batch07Part28
import Vsa.Sim.DecodeTable.Batch08Part14
import Vsa.Sim.DecodeTable.Batch08Part30
import Vsa.Sim.DecodeTable.Batch11Part20
import Vsa.Sim.DecodeTable.Batch13Part06
import Vsa.Sim.DecodeTable.Batch15Part25
import Vsa.Sim.DecodeTable.Batch15Part26
import Vsa.Sim.DecodeTable.Batch16Part11
import Vsa.Sim.DecodeTable.Batch16Part13
import Vsa.Sim.DecodeTable.Batch16Part21
import Vsa.Sim.DecodeTable.Batch16Part22
import Vsa.Sim.DecodeTable.Batch16Part23
import Vsa.Sim.DecodeTable.Batch16Part24
import Vsa.Sim.DecodeTable.Batch16Part25
import Vsa.Sim.DecodeTable.Batch16Part26
import Vsa.Sim.DecodeTable.Batch16Part28
import Vsa.Sim.Code.Strlen

/-!
# Layer 3 — per-site observational step lemmas for `strlen`

One observational-step (`StepObs`) lemma per instruction of `strlen`
(53 instructions at `[0x80006cf0, 0x80006dc4)`), following `Muldi3Sites.lean`
verbatim: each site = the fully-qualified `DecodeTable` decode lemma + the
`rX`/`wX` read-backs + the matching `ExecuteAlu`/`ExecuteBranch`/`ExecuteLoad`
character, assembled into the abstract `hexec` the generic `stepObs_*` wrapper
wants, and closed by one `stepObs_*` application.

Every lemma is **parity-agnostic** (`i < 2 ↦ ∃ σ' i', … ∧ i' < 2 ∧ … ∧
ReadsLikePost σ' (sigmaPost_…)`), folding the tick/notick split into the
`ReadsLikePost` observation.

Load handling follows `DemoLoad.lean`: an executed LOAD's post-state is a single
`rd` insert (`sigma3_alu`), so loads plug into `stepObs_alu`.
* The word-wise `ld a2,0(a4)` (`0x80006d10`) uses the **TOTAL** load chain
  (`vmem_read_data_eight_total`), so no per-byte `some`-hypotheses are needed —
  the trailing bytes of the NUL-containing word may be unmapped.
* The `lbu` sites read mapped string bytes, so the width-1 `some`-hyp chain
  (`vmem_read_data_one`) is used.

Segments (control flow):
* entry / alignment test (`0xcf0…cfc`)
* magic-constant setup (`0xd00…d0c`)
* word-scan loop (`0xd10…d28`)
* byte tail (`0xd2c…d70`)
* byte-at-a-time alignment head (`0xd74…d90`)
* exit blocks (`0xd94…dc0`)
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code (StrlenLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Entry / alignment test (`0x80006cf0 … 0x80006cfc`) -/

/-! ### Site 0x80006cf0 — `andi a5,a0,7` = `andi x15,x10,7` -/

theorem exec_andi_a5_a0_7 (σ : MState) (pc : BitVec 64) (v10 : BitVec 64)
    (hx10 : σ.regs.get? Register.x10 = some v10) :
    (execute (instruction.ITYPE (0x007#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0f#5, iop.ANDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x15 (v10 &&& sign_extend (m := 64) (0x007#12))) := by
  have hx10₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx10
  exact execute_itype_andi_char (0x007#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0f#5) v10
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x15 (v10 &&& sign_extend (m := 64) (0x007#12)))
    (rX_bits_x10 _ v10 hx10₂)
    (wX_bits_x15 _ (v10 &&& sign_extend (m := 64) (0x007#12)))

theorem andi_a5_a0_7_word :
    (((0x00#8).append (0x75#8)).append (0x77#8)).append (0x93#8) = (0x00757793#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem andi_a5_a0_7_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x75#8)).append (0x77#8)).append (0x93#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006cf0** (`andi a5,a0,7`). Writes `x15 := a0 & 7`. -/
theorem site_80006cf0
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006cf0#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x15 (v10 &&& sign_extend (m := 64) (0x007#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006cf0 hmem
  exact stepObs_alu σ i u (0x80006cf0#64) vminstret (0x00757793#32)
    (instruction.ITYPE (0x007#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0f#5, iop.ANDI))
    Register.x15 (v10 &&& sign_extend (m := 64) (0x007#12)) (0x93#8) (0x77#8) (0x75#8) (0x00#8)
    hG hpc hminstret andi_a5_a0_7_word andi_a5_a0_7_notrvc
    (Vsa.Sim.DecodeTable.decode_00757793 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_andi_a5_a0_7 σ (0x80006cf0#64) v10 hx10)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006cf4 — `mv a4,a0` = `addi x14,x10,0` -/

theorem exec_mv_a4_a0 (σ : MState) (pc : BitVec 64) (v10 : BitVec 64)
    (hx10 : σ.regs.get? Register.x10 = some v10) :
    (execute (instruction.ITYPE (0x000#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0e#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x14 (v10 + sign_extend (m := 64) (0x000#12))) := by
  have hx10₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx10
  exact execute_itype_addi_char (0x000#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0e#5) v10
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x14 (v10 + sign_extend (m := 64) (0x000#12)))
    (rX_bits_x10 _ v10 hx10₂)
    (wX_bits_x14 _ (v10 + sign_extend (m := 64) (0x000#12)))

theorem mv_a4_a0_word :
    (((0x00#8).append (0x05#8)).append (0x07#8)).append (0x13#8) = (0x00050713#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem mv_a4_a0_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x05#8)).append (0x07#8)).append (0x13#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006cf4** (`mv a4,a0`). Writes `x14 := a0`. -/
theorem site_80006cf4
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006cf4#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x14 (v10 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006cf4 hmem
  exact stepObs_alu σ i u (0x80006cf4#64) vminstret (0x00050713#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0e#5, iop.ADDI))
    Register.x14 (v10 + sign_extend (m := 64) (0x000#12)) (0x13#8) (0x07#8) (0x05#8) (0x00#8)
    hG hpc hminstret mv_a4_a0_word mv_a4_a0_notrvc
    (Vsa.Sim.DecodeTable.decode_00050713 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_mv_a4_a0 σ (0x80006cf4#64) v10 hx10)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006cf8 — `bnez a5,+0x80` = `bne x15,x0` (to 0x80006d78)

Decode: `BTYPE (0x0080#13, x0, x15, BNE)`. Taken (a5 ≠ 0): PC → pc + sext 0x0080.
Not-taken (a5 = 0): fall through to pc+4. -/

theorem bnez_a5_entry_word :
    (((0x08#8).append (0x07#8)).append (0x90#8)).append (0x63#8) = (0x08079063#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem bnez_a5_entry_notrvc :
    Sail.BitVec.extractLsb ((((0x08#8).append (0x07#8)).append (0x90#8)).append (0x63#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem exec_bnez_a5_entry_taken (σ : MState) (pc : BitVec 64) (v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (htgt : (pc + sign_extend (m := 64) (0x0080#13)).toNat % 4 = 0)
    (hv : (v15 != (0#64)) = true) :
    (execute (instruction.BTYPE (0x0080#13, regidx.Regidx 0x00#5, regidx.Regidx 0x0f#5, bop.BNE))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc (0x0080#13)) := by
  have hx15₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  have hpc₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.PC = some pc := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc
  have hmisa₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.misa = some initMisa := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.misa
  exact execute_btype_bne_taken (0x0080#13) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5)
    v15 (0#64) pc initMisa (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x15 _ v15 hx15₂) (rX_bits_zero _) hpc₂ hmisa₂ htgt hv

theorem exec_bnez_a5_entry_nottaken (σ : MState) (pc : BitVec 64) (v15 : BitVec 64)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hv : (v15 != (0#64)) = false) :
    (execute (instruction.BTYPE (0x0080#13, regidx.Regidx 0x00#5, regidx.Regidx 0x0f#5, bop.BNE))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) := by
  have hx15₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  exact execute_btype_bne_nottaken (0x0080#13) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5)
    v15 (0#64) (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x15 _ v15 hx15₂) (rX_bits_zero _) hv

/-- **Observational step at 0x80006cf8, taken** (`bnez a5`, a5 ≠ 0): PC → 0x80006d78. -/
theorem site_80006cf8_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006cf8#64 : BitVec 64)) (hv : (v15 != (0#64)) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x0080#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006cf8 hmem
  exact stepObs_branch_taken σ i u (0x80006cf8#64) vminstret (0x0080#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) bop.BNE (0x08079063#32)
    (0x63#8) (0x90#8) (0x07#8) (0x08#8)
    hG hpc hminstret bnez_a5_entry_word bnez_a5_entry_notrvc
    (Vsa.Sim.DecodeTable.decode_08079063 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bnez_a5_entry_taken σ (0x80006cf8#64) v15 hG hpc hx15 (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Observational step at 0x80006cf8, not taken** (`bnez a5`, a5 = 0): PC → pc+4. -/
theorem site_80006cf8_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006cf8#64 : BitVec 64)) (hv : (v15 != (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006cf8 hmem
  exact stepObs_branch_nottaken σ i u (0x80006cf8#64) vminstret (0x0080#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) bop.BNE (0x08079063#32)
    (0x63#8) (0x90#8) (0x07#8) (0x08#8)
    hG hpc hminstret bnez_a5_entry_word bnez_a5_entry_notrvc
    (Vsa.Sim.DecodeTable.decode_08079063 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bnez_a5_entry_nottaken σ (0x80006cf8#64) v15 hx15 hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006cfc — `lui a5,0x7f7f8` = `lui x15,0x7f7f8` -/

theorem exec_lui_a5 (σ : MState) (pc : BitVec 64) :
    (execute (instruction.UTYPE (0x7f7f8#20, regidx.Regidx 0x0f#5, uop.LUI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x15 (sign_extend (m := 64) ((0x7f7f8#20) +++ 0x000#12))) :=
  execute_utype_lui_char (0x7f7f8#20) (regidx.Regidx 0x0f#5)
    (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x15 (sign_extend (m := 64) ((0x7f7f8#20) +++ 0x000#12)))
    (wX_bits_x15 _ (sign_extend (m := 64) ((0x7f7f8#20) +++ 0x000#12)))

theorem lui_a5_word :
    (((0x7f#8).append (0x7f#8)).append (0x87#8)).append (0xb7#8) = (0x7f7f87b7#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem lui_a5_notrvc :
    Sail.BitVec.extractLsb ((((0x7f#8).append (0x7f#8)).append (0x87#8)).append (0xb7#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006cfc** (`lui a5,0x7f7f8`). Writes `x15 := sext(0x7f7f8000)`. -/
theorem site_80006cfc
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006cfc#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x15
          (sign_extend (m := 64) ((0x7f7f8#20) +++ 0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006cfc hmem
  exact stepObs_alu σ i u (0x80006cfc#64) vminstret (0x7f7f87b7#32)
    (instruction.UTYPE (0x7f7f8#20, regidx.Regidx 0x0f#5, uop.LUI))
    Register.x15 (sign_extend (m := 64) ((0x7f7f8#20) +++ 0x000#12)) (0xb7#8) (0x87#8) (0x7f#8) (0x7f#8)
    hG hpc hminstret lui_a5_word lui_a5_notrvc
    (Vsa.Sim.DecodeTable.decode_7f7f87b7 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lui_a5 σ (0x80006cfc#64))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Magic-constant setup (`0x80006d00 … 0x80006d0c`) -/

/-! ### Site 0x80006d00 — `addi a5,a5,-129` = `addi x15,x15,0xf7f` -/

theorem exec_addi_a5_m129 (σ : MState) (pc : BitVec 64) (v15 : BitVec 64)
    (hx15 : σ.regs.get? Register.x15 = some v15) :
    (execute (instruction.ITYPE (0xf7f#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x15 (v15 + sign_extend (m := 64) (0xf7f#12))) := by
  have hx15₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  exact execute_itype_addi_char (0xf7f#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5) v15
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x15 (v15 + sign_extend (m := 64) (0xf7f#12)))
    (rX_bits_x15 _ v15 hx15₂)
    (wX_bits_x15 _ (v15 + sign_extend (m := 64) (0xf7f#12)))

theorem addi_a5_m129_word :
    (((0xf7#8).append (0xf7#8)).append (0x87#8)).append (0x93#8) = (0xf7f78793#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem addi_a5_m129_notrvc :
    Sail.BitVec.extractLsb ((((0xf7#8).append (0xf7#8)).append (0x87#8)).append (0x93#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006d00** (`addi a5,a5,-129`). Writes `x15 := a5 + sext 0xf7f`. -/
theorem site_80006d00
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d00#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x15 (v15 + sign_extend (m := 64) (0xf7f#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d00 hmem
  exact stepObs_alu σ i u (0x80006d00#64) vminstret (0xf7f78793#32)
    (instruction.ITYPE (0xf7f#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, iop.ADDI))
    Register.x15 (v15 + sign_extend (m := 64) (0xf7f#12)) (0x93#8) (0x87#8) (0xf7#8) (0xf7#8)
    hG hpc hminstret addi_a5_m129_word addi_a5_m129_notrvc
    (Vsa.Sim.DecodeTable.decode_f7f78793 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_addi_a5_m129 σ (0x80006d00#64) v15 hx15)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006d04 — `slli a3,a5,0x20` = `slli x13,x15,0x20` -/

theorem exec_slli_a3_a5 (σ : MState) (pc : BitVec 64) (v15 : BitVec 64)
    (hx15 : σ.regs.get? Register.x15 = some v15) :
    (execute (instruction.SHIFTIOP (0x20#6, regidx.Regidx 0x0f#5, regidx.Regidx 0x0d#5, sop.SLLI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x13 (shift_bits_left v15 (Sail.BitVec.extractLsb (0x20#6) 5 0))) := by
  have hx15₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  exact execute_shiftiop_slli_char (0x20#6) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0d#5) v15
    (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x13 (shift_bits_left v15 (Sail.BitVec.extractLsb (0x20#6) 5 0)))
    (rX_bits_x15 _ v15 hx15₂)
    (wX_bits_x13 _ (shift_bits_left v15 (Sail.BitVec.extractLsb (0x20#6) 5 0)))

theorem slli_a3_a5_word :
    (((0x02#8).append (0x07#8)).append (0x96#8)).append (0x93#8) = (0x02079693#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem slli_a3_a5_notrvc :
    Sail.BitVec.extractLsb ((((0x02#8).append (0x07#8)).append (0x96#8)).append (0x93#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006d04** (`slli a3,a5,0x20`). Writes `x13 := a5 << 32`. -/
theorem site_80006d04
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d04#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x13
          (shift_bits_left v15 (Sail.BitVec.extractLsb (0x20#6) 5 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d04 hmem
  exact stepObs_alu σ i u (0x80006d04#64) vminstret (0x02079693#32)
    (instruction.SHIFTIOP (0x20#6, regidx.Regidx 0x0f#5, regidx.Regidx 0x0d#5, sop.SLLI))
    Register.x13 (shift_bits_left v15 (Sail.BitVec.extractLsb (0x20#6) 5 0))
    (0x93#8) (0x96#8) (0x07#8) (0x02#8)
    hG hpc hminstret slli_a3_a5_word slli_a3_a5_notrvc
    (Vsa.Sim.DecodeTable.decode_02079693 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_slli_a3_a5 σ (0x80006d04#64) v15 hx15)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006d08 — `add a3,a3,a5` = `add x13,x13,x15` -/

theorem exec_add_a3_a3_a5 (σ : MState) (pc : BitVec 64) (v13 v15 : BitVec 64)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hx15 : σ.regs.get? Register.x15 = some v15) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0f#5, regidx.Regidx 0x0d#5, regidx.Regidx 0x0d#5, rop.ADD))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x13 (v13 + v15)) := by
  have hx13₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x13 = some v13 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx13
  have hx15₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  exact execute_rtype_add_char (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0d#5) (regidx.Regidx 0x0d#5)
    v13 v15 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x13 (v13 + v15))
    (rX_bits_x13 _ v13 hx13₂) (rX_bits_x15 _ v15 hx15₂)
    (wX_bits_x13 _ (v13 + v15))

theorem add_a3_a3_a5_word :
    (((0x00#8).append (0xf6#8)).append (0x86#8)).append (0xb3#8) = (0x00f686b3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem add_a3_a3_a5_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xf6#8)).append (0x86#8)).append (0xb3#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006d08** (`add a3,a3,a5`). Writes `x13 := a3 + a5`. -/
theorem site_80006d08
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v13 v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d08#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x13 (v13 + v15)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d08 hmem
  exact stepObs_alu σ i u (0x80006d08#64) vminstret (0x00f686b3#32)
    (instruction.RTYPE (regidx.Regidx 0x0f#5, regidx.Regidx 0x0d#5, regidx.Regidx 0x0d#5, rop.ADD))
    Register.x13 (v13 + v15) (0xb3#8) (0x86#8) (0xf6#8) (0x00#8)
    hG hpc hminstret add_a3_a3_a5_word add_a3_a3_a5_notrvc
    (Vsa.Sim.DecodeTable.decode_00f686b3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_add_a3_a3_a5 σ (0x80006d08#64) v13 v15 hx13 hx15)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006d0c — `li a1,-1` = `addi x11,x0,0xfff` -/

theorem exec_li_a1_m1 (σ : MState) (pc : BitVec 64) :
    (execute (instruction.ITYPE (0xfff#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0b#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x11 ((0#64) + sign_extend (m := 64) (0xfff#12))) :=
  execute_itype_addi_char (0xfff#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0b#5) (0#64)
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x11 ((0#64) + sign_extend (m := 64) (0xfff#12)))
    (rX_bits_zero _)
    (wX_bits_x11 _ ((0#64) + sign_extend (m := 64) (0xfff#12)))

theorem li_a1_m1_word :
    (((0xff#8).append (0xf0#8)).append (0x05#8)).append (0x93#8) = (0xfff00593#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem li_a1_m1_notrvc :
    Sail.BitVec.extractLsb ((((0xff#8).append (0xf0#8)).append (0x05#8)).append (0x93#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006d0c** (`li a1,-1`). Writes `x11 := -1`. -/
theorem site_80006d0c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d0c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x11 ((0#64) + sign_extend (m := 64) (0xfff#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d0c hmem
  exact stepObs_alu σ i u (0x80006d0c#64) vminstret (0xfff00593#32)
    (instruction.ITYPE (0xfff#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0b#5, iop.ADDI))
    Register.x11 ((0#64) + sign_extend (m := 64) (0xfff#12)) (0x93#8) (0x05#8) (0xf0#8) (0xff#8)
    hG hpc hminstret li_a1_m1_word li_a1_m1_notrvc
    (Vsa.Sim.DecodeTable.decode_fff00593 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_li_a1_m1 σ (0x80006d0c#64))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Word-scan loop (`0x80006d10 … 0x80006d28`)

The word-loop scans 8 aligned bytes at a time: `ld a2,0(a4)` then the magic
`a5 = ((a2 & a3) + a3) | a2 | a3`, and `beq a5,a1` (loop while `a5 = all-ones`,
i.e. no zero byte — see `StrlenMagic.detect_all_ones`). The `ld` uses the TOTAL
chain (`vmem_read_data_eight_total`), since the NUL-containing word's trailing
bytes may be unmapped. -/

/-! ### Site 0x80006d10 — `ld a2,0(a4)` = `ld x12, 0(x14)` (TOTAL 8-byte load)

Effective address `a := v14 + sext 0`; loads the eight little-endian bytes
`getD 0`. Value written to `x12` is `sign_extend (ldBytesT σ₂ a)`. -/

/-- `execute (LOAD ld a2,0(a4))` via the TOTAL 8-byte chain. -/
theorem exec_ld_a2_a4 (σ : MState) (pc : BitVec 64) (v14 : BitVec 64)
    (hG : GoodState σ)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hlo : 0x80000000 ≤ (v14 + sign_extend (m := 64) (0x000#12)).toNat)
    (hhiram : (v14 + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v14 + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ tohostAddr
        ∨ tohostAddr + 8 ≤ (v14 + sign_extend (m := 64) (0x000#12)).toNat)
    (halign : (v14 + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0) :
    (execute (instruction.LOAD (0x000#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x0c#5, false, 8))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x12
            (sign_extend (m := 64)
              (ldBytesT (afterNextPC (afterPrelude σ) pc) (v14 + sign_extend (m := 64) (0x000#12))))) := by
  have hpriv : (afterNextPC (afterPrelude σ) pc).regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.cur_privilege
  have hmstatus : (afterNextPC (afterPrelude σ) pc).regs.get? Register.mstatus = some initMstatus := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.mstatus
  have hseccfg : (afterNextPC (afterPrelude σ) pc).regs.get? Register.mseccfg = some (0#64) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.mseccfg
  have hpma : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pma_regions
  have hcfg : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pmpcfg_n
  have haddr : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pmpaddr_n = some initPmpaddr := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pmpaddr_n
  have hbase' : (afterNextPC (afterPrelude σ) pc).regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.htif_tohost_base
  have hx14₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx14
  have hmprv : _get_Mstatus_MPRV initMstatus = 0#1 := by decide
  have hread := vmem_read_data_eight_total (afterNextPC (afterPrelude σ) pc)
    (regidx.Regidx 0x0e#5) (sign_extend (m := 64) (0x000#12)) v14
    initMstatus initPmpaddr
    hpriv hmstatus hmprv hseccfg hpma hcfg haddr hbase'
    (rX_bits_x14 _ v14 hx14₂)
    hlo hhiram hhtif halign
  exact execute_load_signed_char (0x000#12) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0c#5)
    8 (ldBytesT (afterNextPC (afterPrelude σ) pc) (v14 + sign_extend (m := 64) (0x000#12)))
    (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x12
      (sign_extend (m := 64) (ldBytesT (afterNextPC (afterPrelude σ) pc) (v14 + sign_extend (m := 64) (0x000#12)))))
    (by decide) hread
    (wX_bits_x12 _ (sign_extend (m := 64)
      (ldBytesT (afterNextPC (afterPrelude σ) pc) (v14 + sign_extend (m := 64) (0x000#12)))))

theorem ld_a2_a4_word :
    (((0x00#8).append (0x07#8)).append (0x36#8)).append (0x03#8) = (0x00073603#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem ld_a2_a4_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x07#8)).append (0x36#8)).append (0x03#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006d10** (`ld a2,0(a4)`, TOTAL). Writes
`x12 := sign_extend (ldBytesT σ₂ (a4+0))`; the eight bytes are read `getD 0`. -/
theorem site_80006d10
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d10#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v14 + sign_extend (m := 64) (0x000#12)).toNat)
    (hhiram : (v14 + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v14 + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ tohostAddr
        ∨ tohostAddr + 8 ≤ (v14 + sign_extend (m := 64) (0x000#12)).toNat)
    (halign : (v14 + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x12
          (sign_extend (m := 64)
            (ldBytesT (afterNextPC (afterPrelude σ) pc) (v14 + sign_extend (m := 64) (0x000#12))))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d10 hmem
  exact stepObs_alu σ i u (0x80006d10#64) vminstret (0x00073603#32)
    (instruction.LOAD (0x000#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x0c#5, false, 8))
    Register.x12
    (sign_extend (m := 64)
      (ldBytesT (afterNextPC (afterPrelude σ) (0x80006d10#64)) (v14 + sign_extend (m := 64) (0x000#12))))
    (0x03#8) (0x36#8) (0x07#8) (0x00#8)
    hG hpc hminstret ld_a2_a4_word ld_a2_a4_notrvc
    (Vsa.Sim.DecodeTable.decode_00073603 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld_a2_a4 σ (0x80006d10#64) v14 hG hx14 hlo hhiram hhtif halign)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006d14 — `addi a4,a4,8` = `addi x14,x14,8` -/

theorem exec_addi_a4_8 (σ : MState) (pc : BitVec 64) (v14 : BitVec 64)
    (hx14 : σ.regs.get? Register.x14 = some v14) :
    (execute (instruction.ITYPE (0x008#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x0e#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x14 (v14 + sign_extend (m := 64) (0x008#12))) := by
  have hx14₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx14
  exact execute_itype_addi_char (0x008#12) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0e#5) v14
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x14 (v14 + sign_extend (m := 64) (0x008#12)))
    (rX_bits_x14 _ v14 hx14₂)
    (wX_bits_x14 _ (v14 + sign_extend (m := 64) (0x008#12)))

theorem addi_a4_8_word :
    (((0x00#8).append (0x87#8)).append (0x07#8)).append (0x13#8) = (0x00870713#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem addi_a4_8_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x87#8)).append (0x07#8)).append (0x13#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006d14** (`addi a4,a4,8`). Writes `x14 := a4 + 8`. -/
theorem site_80006d14
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d14#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x14 (v14 + sign_extend (m := 64) (0x008#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d14 hmem
  exact stepObs_alu σ i u (0x80006d14#64) vminstret (0x00870713#32)
    (instruction.ITYPE (0x008#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x0e#5, iop.ADDI))
    Register.x14 (v14 + sign_extend (m := 64) (0x008#12)) (0x13#8) (0x07#8) (0x87#8) (0x00#8)
    hG hpc hminstret addi_a4_8_word addi_a4_8_notrvc
    (Vsa.Sim.DecodeTable.decode_00870713 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_addi_a4_8 σ (0x80006d14#64) v14 hx14)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006d18 — `and a5,a2,a3` = `and x15,x12,x13` -/

theorem exec_and_a5_a2_a3 (σ : MState) (pc : BitVec 64) (v12 v13 : BitVec 64)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hx13 : σ.regs.get? Register.x13 = some v13) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0d#5, regidx.Regidx 0x0c#5, regidx.Regidx 0x0f#5, rop.AND))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x15 (v12 &&& v13)) := by
  have hx12₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x12 = some v12 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx12
  have hx13₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x13 = some v13 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx13
  exact execute_rtype_and_char (regidx.Regidx 0x0d#5) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0f#5)
    v12 v13 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x15 (v12 &&& v13))
    (rX_bits_x12 _ v12 hx12₂) (rX_bits_x13 _ v13 hx13₂)
    (wX_bits_x15 _ (v12 &&& v13))

theorem and_a5_a2_a3_word :
    (((0x00#8).append (0xd6#8)).append (0x77#8)).append (0xb3#8) = (0x00d677b3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem and_a5_a2_a3_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xd6#8)).append (0x77#8)).append (0xb3#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006d18** (`and a5,a2,a3`). Writes `x15 := a2 & a3`. -/
theorem site_80006d18
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d18#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (v12 &&& v13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d18 hmem
  exact stepObs_alu σ i u (0x80006d18#64) vminstret (0x00d677b3#32)
    (instruction.RTYPE (regidx.Regidx 0x0d#5, regidx.Regidx 0x0c#5, regidx.Regidx 0x0f#5, rop.AND))
    Register.x15 (v12 &&& v13) (0xb3#8) (0x77#8) (0xd6#8) (0x00#8)
    hG hpc hminstret and_a5_a2_a3_word and_a5_a2_a3_notrvc
    (Vsa.Sim.DecodeTable.decode_00d677b3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_and_a5_a2_a3 σ (0x80006d18#64) v12 v13 hx12 hx13)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006d1c — `add a5,a5,a3` = `add x15,x15,x13` -/

theorem exec_add_a5_a5_a3 (σ : MState) (pc : BitVec 64) (v15 v13 : BitVec 64)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hx13 : σ.regs.get? Register.x13 = some v13) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0d#5, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, rop.ADD))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x15 (v15 + v13)) := by
  have hx15₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  have hx13₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x13 = some v13 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx13
  exact execute_rtype_add_char (regidx.Regidx 0x0d#5) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5)
    v15 v13 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x15 (v15 + v13))
    (rX_bits_x15 _ v15 hx15₂) (rX_bits_x13 _ v13 hx13₂)
    (wX_bits_x15 _ (v15 + v13))

theorem add_a5_a5_a3_word :
    (((0x00#8).append (0xd7#8)).append (0x87#8)).append (0xb3#8) = (0x00d787b3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem add_a5_a5_a3_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xd7#8)).append (0x87#8)).append (0xb3#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006d1c** (`add a5,a5,a3`). Writes `x15 := a5 + a3`. -/
theorem site_80006d1c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d1c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (v15 + v13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d1c hmem
  exact stepObs_alu σ i u (0x80006d1c#64) vminstret (0x00d787b3#32)
    (instruction.RTYPE (regidx.Regidx 0x0d#5, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, rop.ADD))
    Register.x15 (v15 + v13) (0xb3#8) (0x87#8) (0xd7#8) (0x00#8)
    hG hpc hminstret add_a5_a5_a3_word add_a5_a5_a3_notrvc
    (Vsa.Sim.DecodeTable.decode_00d787b3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_add_a5_a5_a3 σ (0x80006d1c#64) v15 v13 hx15 hx13)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006d20 — `or a5,a5,a2` = `or x15,x15,x12` -/

theorem exec_or_a5_a5_a2 (σ : MState) (pc : BitVec 64) (v15 v12 : BitVec 64)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hx12 : σ.regs.get? Register.x12 = some v12) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0c#5, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, rop.OR))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x15 (v15 ||| v12)) := by
  have hx15₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  have hx12₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x12 = some v12 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx12
  exact execute_rtype_or_char (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5)
    v15 v12 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x15 (v15 ||| v12))
    (rX_bits_x15 _ v15 hx15₂) (rX_bits_x12 _ v12 hx12₂)
    (wX_bits_x15 _ (v15 ||| v12))

theorem or_a5_a5_a2_word :
    (((0x00#8).append (0xc7#8)).append (0xe7#8)).append (0xb3#8) = (0x00c7e7b3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem or_a5_a5_a2_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xc7#8)).append (0xe7#8)).append (0xb3#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006d20** (`or a5,a5,a2`). Writes `x15 := a5 | a2`. -/
theorem site_80006d20
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d20#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (v15 ||| v12)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d20 hmem
  exact stepObs_alu σ i u (0x80006d20#64) vminstret (0x00c7e7b3#32)
    (instruction.RTYPE (regidx.Regidx 0x0c#5, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, rop.OR))
    Register.x15 (v15 ||| v12) (0xb3#8) (0xe7#8) (0xc7#8) (0x00#8)
    hG hpc hminstret or_a5_a5_a2_word or_a5_a5_a2_notrvc
    (Vsa.Sim.DecodeTable.decode_00c7e7b3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_or_a5_a5_a2 σ (0x80006d20#64) v15 v12 hx15 hx12)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006d24 — `or a5,a5,a3` = `or x15,x15,x13` -/

theorem exec_or_a5_a5_a3 (σ : MState) (pc : BitVec 64) (v15 v13 : BitVec 64)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hx13 : σ.regs.get? Register.x13 = some v13) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0d#5, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, rop.OR))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x15 (v15 ||| v13)) := by
  have hx15₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  have hx13₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x13 = some v13 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx13
  exact execute_rtype_or_char (regidx.Regidx 0x0d#5) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5)
    v15 v13 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x15 (v15 ||| v13))
    (rX_bits_x15 _ v15 hx15₂) (rX_bits_x13 _ v13 hx13₂)
    (wX_bits_x15 _ (v15 ||| v13))

theorem or_a5_a5_a3_word :
    (((0x00#8).append (0xd7#8)).append (0xe7#8)).append (0xb3#8) = (0x00d7e7b3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem or_a5_a5_a3_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xd7#8)).append (0xe7#8)).append (0xb3#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006d24** (`or a5,a5,a3`). Writes `x15 := a5 | a3`. -/
theorem site_80006d24
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d24#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (v15 ||| v13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d24 hmem
  exact stepObs_alu σ i u (0x80006d24#64) vminstret (0x00d7e7b3#32)
    (instruction.RTYPE (regidx.Regidx 0x0d#5, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, rop.OR))
    Register.x15 (v15 ||| v13) (0xb3#8) (0xe7#8) (0xd7#8) (0x00#8)
    hG hpc hminstret or_a5_a5_a3_word or_a5_a5_a3_notrvc
    (Vsa.Sim.DecodeTable.decode_00d7e7b3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_or_a5_a5_a3 σ (0x80006d24#64) v15 v13 hx15 hx13)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006d28 — `beq a5,a1,0x80006d10` = `beq x15,x11` (loop back-edge)

Decode: `BTYPE (0x1fe8#13, x11, x15, BEQ)`. Taken (a5 = a1 = all-ones ⟺ no zero
byte in the word): PC → pc + sext 0x1fe8 = pc - 24 = 0x80006d10 (loop back).
Not-taken (a5 ≠ a1 ⟺ zero byte found): fall through to pc+4 (byte tail). -/

theorem beq_a5_a1_word :
    (((0xfe#8).append (0xb7#8)).append (0x84#8)).append (0xe3#8) = (0xfeb784e3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem beq_a5_a1_notrvc :
    Sail.BitVec.extractLsb ((((0xfe#8).append (0xb7#8)).append (0x84#8)).append (0xe3#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem exec_beq_a5_a1_taken (σ : MState) (pc : BitVec 64) (v15 v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (htgt : (pc + sign_extend (m := 64) (0x1fe8#13)).toNat % 4 = 0)
    (hv : (v15 == v11) = true) :
    (execute (instruction.BTYPE (0x1fe8#13, regidx.Regidx 0x0b#5, regidx.Regidx 0x0f#5, bop.BEQ))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc (0x1fe8#13)) := by
  have hx15₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  have hx11₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx11
  have hpc₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.PC = some pc := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc
  have hmisa₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.misa = some initMisa := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.misa
  exact execute_btype_beq_taken (0x1fe8#13) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0b#5)
    v15 v11 pc initMisa (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x15 _ v15 hx15₂) (rX_bits_x11 _ v11 hx11₂) hpc₂ hmisa₂ htgt hv

theorem exec_beq_a5_a1_nottaken (σ : MState) (pc : BitVec 64) (v15 v11 : BitVec 64)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hv : (v15 == v11) = false) :
    (execute (instruction.BTYPE (0x1fe8#13, regidx.Regidx 0x0b#5, regidx.Regidx 0x0f#5, bop.BEQ))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) := by
  have hx15₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  have hx11₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx11
  exact execute_btype_beq_nottaken (0x1fe8#13) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0b#5)
    v15 v11 (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x15 _ v15 hx15₂) (rX_bits_x11 _ v11 hx11₂) hv

/-- **Observational step at 0x80006d28, taken** (`beq a5,a1`, a5 = a1): back to 0x80006d10. -/
theorem site_80006d28_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d28#64 : BitVec 64)) (hv : (v15 == v11) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x1fe8#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d28 hmem
  exact stepObs_branch_taken σ i u (0x80006d28#64) vminstret (0x1fe8#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0b#5) bop.BEQ (0xfeb784e3#32)
    (0xe3#8) (0x84#8) (0xb7#8) (0xfe#8)
    hG hpc hminstret beq_a5_a1_word beq_a5_a1_notrvc
    (Vsa.Sim.DecodeTable.decode_feb784e3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_beq_a5_a1_taken σ (0x80006d28#64) v15 v11 hG hpc hx15 hx11 (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Observational step at 0x80006d28, not taken** (`beq a5,a1`, a5 ≠ a1): fall to tail. -/
theorem site_80006d28_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d28#64 : BitVec 64)) (hv : (v15 == v11) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d28 hmem
  exact stepObs_branch_nottaken σ i u (0x80006d28#64) vminstret (0x1fe8#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0b#5) bop.BEQ (0xfeb784e3#32)
    (0xe3#8) (0x84#8) (0xb7#8) (0xfe#8)
    hG hpc hminstret beq_a5_a1_word beq_a5_a1_notrvc
    (Vsa.Sim.DecodeTable.decode_feb784e3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_beq_a5_a1_nottaken σ (0x80006d28#64) v15 v11 hx15 hx11 hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Byte tail (`0x80006d2c … 0x80006d70`)

Once the word-loop finds a word with a zero byte, the tail probes the eight
bytes `a4-8 … a4-1` with `lbu`+`beqz` to locate the exact NUL. These bytes are
all mapped (they lie within the just-loaded word), so the `lbu` sites use the
width-1 `some`-hypothesis chain (`vmem_read_data_one`).

Two shared parameterized executes serve the whole tail (and the alignment head):
`exec_lbu_a5_a4` (`lbu x15, imm(x14)`, over the byte offset `imm`) and
`exec_beqz_a5` (`beq x15,x0`, over the branch immediate). -/

/-- Shared `execute (LOAD lbu x15, imm(x14))` via the width-1 `some`-hyp chain.
Writes `x15 := zero_extend b0v`, the mapped byte at `v14 + sext imm`. Serves all
`lbu a5,off(a4)` sites (tail + alignment head) by choice of `imm`. -/
theorem exec_lbu_a5_a4 (σ : MState) (pc : BitVec 64) (imm : BitVec 12) (v14 : BitVec 64)
    (b0v : BitVec 8)
    (hG : GoodState σ)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hlo : 0x80000000 ≤ (v14 + sign_extend (m := 64) imm).toNat)
    (hhiram : (v14 + sign_extend (m := 64) imm).toNat + 1 ≤ 0x100000000)
    (hhtif : (v14 + sign_extend (m := 64) imm).toNat + 1 ≤ tohostAddr
        ∨ tohostAddr + 8 ≤ (v14 + sign_extend (m := 64) imm).toNat)
    (hb0 : σ.mem[(v14 + sign_extend (m := 64) imm).toNat]? = some b0v) :
    (execute (instruction.LOAD (imm, regidx.Regidx 0x0e#5, regidx.Regidx 0x0f#5, true, 1))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x15 (zero_extend (m := 64) b0v)) := by
  have hpriv : (afterNextPC (afterPrelude σ) pc).regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.cur_privilege
  have hmstatus : (afterNextPC (afterPrelude σ) pc).regs.get? Register.mstatus = some initMstatus := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.mstatus
  have hseccfg : (afterNextPC (afterPrelude σ) pc).regs.get? Register.mseccfg = some (0#64) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.mseccfg
  have hpma : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pma_regions
  have hcfg : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pmpcfg_n
  have haddr : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pmpaddr_n = some initPmpaddr := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pmpaddr_n
  have hbase' : (afterNextPC (afterPrelude σ) pc).regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.htif_tohost_base
  have hx14₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx14
  have hmprv : _get_Mstatus_MPRV initMstatus = 0#1 := by decide
  have hread := vmem_read_data_one (afterNextPC (afterPrelude σ) pc)
    (regidx.Regidx 0x0e#5) (sign_extend (m := 64) imm) v14 b0v
    initMstatus initPmpaddr
    hpriv hmstatus hmprv hseccfg hpma hcfg haddr hbase'
    (rX_bits_x14 _ v14 hx14₂)
    hlo hhiram hhtif
    (by rw [mem_afterNextPC]; exact hb0)
  exact execute_load_unsigned_char imm (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0f#5)
    1 b0v (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x15 (zero_extend (m := 64) b0v))
    (by decide) hread
    (wX_bits_x15 _ (zero_extend (m := 64) b0v))

/-- Shared taken `beqz a5` (`beq x15,x0`) execute char (a5 = 0). Serves all tail
`beqz a5,off` sites by choice of the branch immediate `imm`. -/
theorem exec_beqz_a5_taken (σ : MState) (pc : BitVec 64) (imm : BitVec 13) (v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (htgt : (pc + sign_extend (m := 64) imm).toNat % 4 = 0)
    (hv : (v15 == (0#64)) = true) :
    (execute (instruction.BTYPE (imm, regidx.Regidx 0x00#5, regidx.Regidx 0x0f#5, bop.BEQ))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc imm) := by
  have hx15₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  have hpc₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.PC = some pc := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc
  have hmisa₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.misa = some initMisa := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.misa
  exact execute_btype_beq_taken imm (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5)
    v15 (0#64) pc initMisa (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x15 _ v15 hx15₂) (rX_bits_zero _) hpc₂ hmisa₂ htgt hv

/-- Shared not-taken `beqz a5` (`beq x15,x0`) execute char (a5 ≠ 0). -/
theorem exec_beqz_a5_nottaken (σ : MState) (pc : BitVec 64) (imm : BitVec 13) (v15 : BitVec 64)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hv : (v15 == (0#64)) = false) :
    (execute (instruction.BTYPE (imm, regidx.Regidx 0x00#5, regidx.Regidx 0x0f#5, bop.BEQ))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) := by
  have hx15₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  exact execute_btype_beq_nottaken imm (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5)
    v15 (0#64) (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x15 _ v15 hx15₂) (rX_bits_zero _) hv

/-! ### Site 0x80006d2c — `lbu a5,-8(a4)` = `lbu x15, 0xff8(x14)` -/

theorem lbu_m8_word :
    (((0xff#8).append (0x87#8)).append (0x47#8)).append (0x83#8) = (0xff874783#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem lbu_m8_notrvc :
    Sail.BitVec.extractLsb ((((0xff#8).append (0x87#8)).append (0x47#8)).append (0x83#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006d2c** (`lbu a5,-8(a4)`). Writes `x15 := zext byte@(a4-8)`. -/
theorem site_80006d2c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 : BitVec 64) (b0v : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d2c#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v14 + sign_extend (m := 64) (0xff8#12)).toNat)
    (hhiram : (v14 + sign_extend (m := 64) (0xff8#12)).toNat + 1 ≤ 0x100000000)
    (hhtif : (v14 + sign_extend (m := 64) (0xff8#12)).toNat + 1 ≤ tohostAddr
        ∨ tohostAddr + 8 ≤ (v14 + sign_extend (m := 64) (0xff8#12)).toNat)
    (hb0 : σ.mem[(v14 + sign_extend (m := 64) (0xff8#12)).toNat]? = some b0v)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (zero_extend (m := 64) b0v)) := by
  subst hpcv
  obtain ⟨hb0', hb1', hb2', hb3'⟩ := Vsa.Sim.Code.strlen_at_80006d2c hmem
  exact stepObs_alu σ i u (0x80006d2c#64) vminstret (0xff874783#32)
    (instruction.LOAD (0xff8#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x0f#5, true, 1))
    Register.x15 (zero_extend (m := 64) b0v) (0x83#8) (0x47#8) (0x87#8) (0xff#8)
    hG hpc hminstret lbu_m8_word lbu_m8_notrvc
    (Vsa.Sim.DecodeTable.decode_ff874783 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lbu_a5_a4 σ (0x80006d2c#64) (0xff8#12) v14 b0v hG hx14 hlo hhiram hhtif hb0)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0' hb1' hb2' hb3' (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006d30 — `sub a3,a4,a0` = `sub x13,x14,x10` -/

theorem exec_sub_a3_a4_a0 (σ : MState) (pc : BitVec 64) (v14 v10 : BitVec 64)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hx10 : σ.regs.get? Register.x10 = some v10) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0a#5, regidx.Regidx 0x0e#5, regidx.Regidx 0x0d#5, rop.SUB))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x13 (v14 - v10)) := by
  have hx14₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx14
  have hx10₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx10
  exact execute_rtype_sub_char (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0d#5)
    v14 v10 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x13 (v14 - v10))
    (rX_bits_x14 _ v14 hx14₂) (rX_bits_x10 _ v10 hx10₂)
    (wX_bits_x13 _ (v14 - v10))

theorem sub_a3_a4_a0_word :
    (((0x40#8).append (0xa7#8)).append (0x06#8)).append (0xb3#8) = (0x40a706b3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem sub_a3_a4_a0_notrvc :
    Sail.BitVec.extractLsb ((((0x40#8).append (0xa7#8)).append (0x06#8)).append (0xb3#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006d30** (`sub a3,a4,a0`). Writes `x13 := a4 - a0`. -/
theorem site_80006d30
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d30#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x13 (v14 - v10)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d30 hmem
  exact stepObs_alu σ i u (0x80006d30#64) vminstret (0x40a706b3#32)
    (instruction.RTYPE (regidx.Regidx 0x0a#5, regidx.Regidx 0x0e#5, regidx.Regidx 0x0d#5, rop.SUB))
    Register.x13 (v14 - v10) (0xb3#8) (0x06#8) (0xa7#8) (0x40#8)
    hG hpc hminstret sub_a3_a4_a0_word sub_a3_a4_a0_notrvc
    (Vsa.Sim.DecodeTable.decode_40a706b3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sub_a3_a4_a0 σ (0x80006d30#64) v14 v10 hx14 hx10)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006d34 — `beqz a5,0x80006d9c` = `beq x15,x0` (imm 0x0068) -/

theorem beqz_d34_word :
    (((0x06#8).append (0x07#8)).append (0x84#8)).append (0x63#8) = (0x06078463#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem beqz_d34_notrvc :
    Sail.BitVec.extractLsb ((((0x06#8).append (0x07#8)).append (0x84#8)).append (0x63#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006d34, taken** (`beqz a5`, a5 = 0): PC → 0x80006d9c. -/
theorem site_80006d34_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d34#64 : BitVec 64)) (hv : (v15 == (0#64)) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x0068#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d34 hmem
  exact stepObs_branch_taken σ i u (0x80006d34#64) vminstret (0x0068#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) bop.BEQ (0x06078463#32)
    (0x63#8) (0x84#8) (0x07#8) (0x06#8)
    hG hpc hminstret beqz_d34_word beqz_d34_notrvc
    (Vsa.Sim.DecodeTable.decode_06078463 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_beqz_a5_taken σ (0x80006d34#64) (0x0068#13) v15 hG hpc hx15 (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Observational step at 0x80006d34, not taken** (`beqz a5`, a5 ≠ 0): PC → pc+4. -/
theorem site_80006d34_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d34#64 : BitVec 64)) (hv : (v15 == (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d34 hmem
  exact stepObs_branch_nottaken σ i u (0x80006d34#64) vminstret (0x0068#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) bop.BEQ (0x06078463#32)
    (0x63#8) (0x84#8) (0x07#8) (0x06#8)
    hG hpc hminstret beqz_d34_word beqz_d34_notrvc
    (Vsa.Sim.DecodeTable.decode_06078463 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_beqz_a5_nottaken σ (0x80006d34#64) (0x0068#13) v15 hx15 hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006d38 — `lbu a5,-7(a4)` = `lbu x15, 0xff9(x14)` -/

theorem lbu_m7_word :
    (((0xff#8).append (0x97#8)).append (0x47#8)).append (0x83#8) = (0xff974783#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem lbu_m7_notrvc :
    Sail.BitVec.extractLsb ((((0xff#8).append (0x97#8)).append (0x47#8)).append (0x83#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006d38** (`lbu a5,-7(a4)`). Writes `x15 := zext byte@(a4-7)`. -/
theorem site_80006d38
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 : BitVec 64) (b0v : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d38#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v14 + sign_extend (m := 64) (0xff9#12)).toNat)
    (hhiram : (v14 + sign_extend (m := 64) (0xff9#12)).toNat + 1 ≤ 0x100000000)
    (hhtif : (v14 + sign_extend (m := 64) (0xff9#12)).toNat + 1 ≤ tohostAddr
        ∨ tohostAddr + 8 ≤ (v14 + sign_extend (m := 64) (0xff9#12)).toNat)
    (hb0 : σ.mem[(v14 + sign_extend (m := 64) (0xff9#12)).toNat]? = some b0v)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (zero_extend (m := 64) b0v)) := by
  subst hpcv
  obtain ⟨hb0', hb1', hb2', hb3'⟩ := Vsa.Sim.Code.strlen_at_80006d38 hmem
  exact stepObs_alu σ i u (0x80006d38#64) vminstret (0xff974783#32)
    (instruction.LOAD (0xff9#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x0f#5, true, 1))
    Register.x15 (zero_extend (m := 64) b0v) (0x83#8) (0x47#8) (0x97#8) (0xff#8)
    hG hpc hminstret lbu_m7_word lbu_m7_notrvc
    (Vsa.Sim.DecodeTable.decode_ff974783 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lbu_a5_a4 σ (0x80006d38#64) (0xff9#12) v14 b0v hG hx14 hlo hhiram hhtif hb0)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0' hb1' hb2' hb3' (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006d3c — `beqz a5,0x80006d94` = `beq x15,x0` (imm 0x0058) -/

theorem beqz_d3c_word :
    (((0x04#8).append (0x07#8)).append (0x8c#8)).append (0x63#8) = (0x04078c63#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem beqz_d3c_notrvc :
    Sail.BitVec.extractLsb ((((0x04#8).append (0x07#8)).append (0x8c#8)).append (0x63#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006d3c, taken** (`beqz a5`, a5 = 0): PC → 0x80006d94. -/
theorem site_80006d3c_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d3c#64 : BitVec 64)) (hv : (v15 == (0#64)) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x0058#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d3c hmem
  exact stepObs_branch_taken σ i u (0x80006d3c#64) vminstret (0x0058#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) bop.BEQ (0x04078c63#32)
    (0x63#8) (0x8c#8) (0x07#8) (0x04#8)
    hG hpc hminstret beqz_d3c_word beqz_d3c_notrvc
    (Vsa.Sim.DecodeTable.decode_04078c63 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_beqz_a5_taken σ (0x80006d3c#64) (0x0058#13) v15 hG hpc hx15 (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Observational step at 0x80006d3c, not taken** (`beqz a5`, a5 ≠ 0): PC → pc+4. -/
theorem site_80006d3c_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d3c#64 : BitVec 64)) (hv : (v15 == (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d3c hmem
  exact stepObs_branch_nottaken σ i u (0x80006d3c#64) vminstret (0x0058#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) bop.BEQ (0x04078c63#32)
    (0x63#8) (0x8c#8) (0x07#8) (0x04#8)
    hG hpc hminstret beqz_d3c_word beqz_d3c_notrvc
    (Vsa.Sim.DecodeTable.decode_04078c63 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_beqz_a5_nottaken σ (0x80006d3c#64) (0x0058#13) v15 hx15 hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006d40 — `lbu a5,-6(a4)` = `lbu x15, 0xffa(x14)` -/

theorem lbu_m6_word :
    (((0xff#8).append (0xa7#8)).append (0x47#8)).append (0x83#8) = (0xffa74783#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem lbu_m6_notrvc :
    Sail.BitVec.extractLsb ((((0xff#8).append (0xa7#8)).append (0x47#8)).append (0x83#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006d40** (`lbu a5,-6(a4)`). Writes `x15 := zext byte@(a4-6)`. -/
theorem site_80006d40
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 : BitVec 64) (b0v : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d40#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v14 + sign_extend (m := 64) (0xffa#12)).toNat)
    (hhiram : (v14 + sign_extend (m := 64) (0xffa#12)).toNat + 1 ≤ 0x100000000)
    (hhtif : (v14 + sign_extend (m := 64) (0xffa#12)).toNat + 1 ≤ tohostAddr
        ∨ tohostAddr + 8 ≤ (v14 + sign_extend (m := 64) (0xffa#12)).toNat)
    (hb0 : σ.mem[(v14 + sign_extend (m := 64) (0xffa#12)).toNat]? = some b0v)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (zero_extend (m := 64) b0v)) := by
  subst hpcv
  obtain ⟨hb0', hb1', hb2', hb3'⟩ := Vsa.Sim.Code.strlen_at_80006d40 hmem
  exact stepObs_alu σ i u (0x80006d40#64) vminstret (0xffa74783#32)
    (instruction.LOAD (0xffa#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x0f#5, true, 1))
    Register.x15 (zero_extend (m := 64) b0v) (0x83#8) (0x47#8) (0xa7#8) (0xff#8)
    hG hpc hminstret lbu_m6_word lbu_m6_notrvc
    (Vsa.Sim.DecodeTable.decode_ffa74783 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lbu_a5_a4 σ (0x80006d40#64) (0xffa#12) v14 b0v hG hx14 hlo hhiram hhtif hb0)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0' hb1' hb2' hb3' (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006d44 — `beqz a5,0x80006dac` = `beq x15,x0` (imm 0x0068) -/

theorem beqz_d44_word :
    (((0x06#8).append (0x07#8)).append (0x84#8)).append (0x63#8) = (0x06078463#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006d44, taken** (`beqz a5`, a5 = 0): PC → 0x80006dac. -/
theorem site_80006d44_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d44#64 : BitVec 64)) (hv : (v15 == (0#64)) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x0068#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d44 hmem
  exact stepObs_branch_taken σ i u (0x80006d44#64) vminstret (0x0068#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) bop.BEQ (0x06078463#32)
    (0x63#8) (0x84#8) (0x07#8) (0x06#8)
    hG hpc hminstret beqz_d44_word beqz_d34_notrvc
    (Vsa.Sim.DecodeTable.decode_06078463 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_beqz_a5_taken σ (0x80006d44#64) (0x0068#13) v15 hG hpc hx15 (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Observational step at 0x80006d44, not taken** (`beqz a5`, a5 ≠ 0): PC → pc+4. -/
theorem site_80006d44_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d44#64 : BitVec 64)) (hv : (v15 == (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d44 hmem
  exact stepObs_branch_nottaken σ i u (0x80006d44#64) vminstret (0x0068#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) bop.BEQ (0x06078463#32)
    (0x63#8) (0x84#8) (0x07#8) (0x06#8)
    hG hpc hminstret beqz_d44_word beqz_d34_notrvc
    (Vsa.Sim.DecodeTable.decode_06078463 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_beqz_a5_nottaken σ (0x80006d44#64) (0x0068#13) v15 hx15 hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006d48 — `lbu a5,-5(a4)` = `lbu x15, 0xffb(x14)` -/

theorem lbu_m5_word :
    (((0xff#8).append (0xb7#8)).append (0x47#8)).append (0x83#8) = (0xffb74783#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem lbu_m5_notrvc :
    Sail.BitVec.extractLsb ((((0xff#8).append (0xb7#8)).append (0x47#8)).append (0x83#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006d48** (`lbu a5,-5(a4)`). Writes `x15 := zext byte@(a4-5)`. -/
theorem site_80006d48
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 : BitVec 64) (b0v : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d48#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v14 + sign_extend (m := 64) (0xffb#12)).toNat)
    (hhiram : (v14 + sign_extend (m := 64) (0xffb#12)).toNat + 1 ≤ 0x100000000)
    (hhtif : (v14 + sign_extend (m := 64) (0xffb#12)).toNat + 1 ≤ tohostAddr
        ∨ tohostAddr + 8 ≤ (v14 + sign_extend (m := 64) (0xffb#12)).toNat)
    (hb0 : σ.mem[(v14 + sign_extend (m := 64) (0xffb#12)).toNat]? = some b0v)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (zero_extend (m := 64) b0v)) := by
  subst hpcv
  obtain ⟨hb0', hb1', hb2', hb3'⟩ := Vsa.Sim.Code.strlen_at_80006d48 hmem
  exact stepObs_alu σ i u (0x80006d48#64) vminstret (0xffb74783#32)
    (instruction.LOAD (0xffb#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x0f#5, true, 1))
    Register.x15 (zero_extend (m := 64) b0v) (0x83#8) (0x47#8) (0xb7#8) (0xff#8)
    hG hpc hminstret lbu_m5_word lbu_m5_notrvc
    (Vsa.Sim.DecodeTable.decode_ffb74783 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lbu_a5_a4 σ (0x80006d48#64) (0xffb#12) v14 b0v hG hx14 hlo hhiram hhtif hb0)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0' hb1' hb2' hb3' (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006d4c — `beqz a5,0x80006da4` = `beq x15,x0` (imm 0x0058) -/

/-- **Observational step at 0x80006d4c, taken** (`beqz a5`, a5 = 0): PC → 0x80006da4. -/
theorem site_80006d4c_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d4c#64 : BitVec 64)) (hv : (v15 == (0#64)) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x0058#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d4c hmem
  exact stepObs_branch_taken σ i u (0x80006d4c#64) vminstret (0x0058#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) bop.BEQ (0x04078c63#32)
    (0x63#8) (0x8c#8) (0x07#8) (0x04#8)
    hG hpc hminstret beqz_d3c_word beqz_d3c_notrvc
    (Vsa.Sim.DecodeTable.decode_04078c63 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_beqz_a5_taken σ (0x80006d4c#64) (0x0058#13) v15 hG hpc hx15 (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Observational step at 0x80006d4c, not taken** (`beqz a5`, a5 ≠ 0): PC → pc+4. -/
theorem site_80006d4c_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d4c#64 : BitVec 64)) (hv : (v15 == (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d4c hmem
  exact stepObs_branch_nottaken σ i u (0x80006d4c#64) vminstret (0x0058#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) bop.BEQ (0x04078c63#32)
    (0x63#8) (0x8c#8) (0x07#8) (0x04#8)
    hG hpc hminstret beqz_d3c_word beqz_d3c_notrvc
    (Vsa.Sim.DecodeTable.decode_04078c63 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_beqz_a5_nottaken σ (0x80006d4c#64) (0x0058#13) v15 hx15 hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006d50 — `lbu a5,-4(a4)` = `lbu x15, 0xffc(x14)` -/

theorem lbu_m4_word :
    (((0xff#8).append (0xc7#8)).append (0x47#8)).append (0x83#8) = (0xffc74783#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem lbu_m4_notrvc :
    Sail.BitVec.extractLsb ((((0xff#8).append (0xc7#8)).append (0x47#8)).append (0x83#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006d50** (`lbu a5,-4(a4)`). Writes `x15 := zext byte@(a4-4)`. -/
theorem site_80006d50
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 : BitVec 64) (b0v : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d50#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v14 + sign_extend (m := 64) (0xffc#12)).toNat)
    (hhiram : (v14 + sign_extend (m := 64) (0xffc#12)).toNat + 1 ≤ 0x100000000)
    (hhtif : (v14 + sign_extend (m := 64) (0xffc#12)).toNat + 1 ≤ tohostAddr
        ∨ tohostAddr + 8 ≤ (v14 + sign_extend (m := 64) (0xffc#12)).toNat)
    (hb0 : σ.mem[(v14 + sign_extend (m := 64) (0xffc#12)).toNat]? = some b0v)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (zero_extend (m := 64) b0v)) := by
  subst hpcv
  obtain ⟨hb0', hb1', hb2', hb3'⟩ := Vsa.Sim.Code.strlen_at_80006d50 hmem
  exact stepObs_alu σ i u (0x80006d50#64) vminstret (0xffc74783#32)
    (instruction.LOAD (0xffc#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x0f#5, true, 1))
    Register.x15 (zero_extend (m := 64) b0v) (0x83#8) (0x47#8) (0xc7#8) (0xff#8)
    hG hpc hminstret lbu_m4_word lbu_m4_notrvc
    (Vsa.Sim.DecodeTable.decode_ffc74783 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lbu_a5_a4 σ (0x80006d50#64) (0xffc#12) v14 b0v hG hx14 hlo hhiram hhtif hb0)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0' hb1' hb2' hb3' (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006d54 — `beqz a5,0x80006db4` = `beq x15,x0` (imm 0x0060) -/

theorem beqz_d54_word :
    (((0x06#8).append (0x07#8)).append (0x80#8)).append (0x63#8) = (0x06078063#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem beqz_d54_notrvc :
    Sail.BitVec.extractLsb ((((0x06#8).append (0x07#8)).append (0x80#8)).append (0x63#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006d54, taken** (`beqz a5`, a5 = 0): PC → 0x80006db4. -/
theorem site_80006d54_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d54#64 : BitVec 64)) (hv : (v15 == (0#64)) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x0060#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d54 hmem
  exact stepObs_branch_taken σ i u (0x80006d54#64) vminstret (0x0060#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) bop.BEQ (0x06078063#32)
    (0x63#8) (0x80#8) (0x07#8) (0x06#8)
    hG hpc hminstret beqz_d54_word beqz_d54_notrvc
    (Vsa.Sim.DecodeTable.decode_06078063 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_beqz_a5_taken σ (0x80006d54#64) (0x0060#13) v15 hG hpc hx15 (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Observational step at 0x80006d54, not taken** (`beqz a5`, a5 ≠ 0): PC → pc+4. -/
theorem site_80006d54_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d54#64 : BitVec 64)) (hv : (v15 == (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d54 hmem
  exact stepObs_branch_nottaken σ i u (0x80006d54#64) vminstret (0x0060#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) bop.BEQ (0x06078063#32)
    (0x63#8) (0x80#8) (0x07#8) (0x06#8)
    hG hpc hminstret beqz_d54_word beqz_d54_notrvc
    (Vsa.Sim.DecodeTable.decode_06078063 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_beqz_a5_nottaken σ (0x80006d54#64) (0x0060#13) v15 hx15 hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006d58 — `lbu a5,-3(a4)` = `lbu x15, 0xffd(x14)` -/

theorem lbu_m3_word :
    (((0xff#8).append (0xd7#8)).append (0x47#8)).append (0x83#8) = (0xffd74783#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem lbu_m3_notrvc :
    Sail.BitVec.extractLsb ((((0xff#8).append (0xd7#8)).append (0x47#8)).append (0x83#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006d58** (`lbu a5,-3(a4)`). Writes `x15 := zext byte@(a4-3)`. -/
theorem site_80006d58
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 : BitVec 64) (b0v : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d58#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v14 + sign_extend (m := 64) (0xffd#12)).toNat)
    (hhiram : (v14 + sign_extend (m := 64) (0xffd#12)).toNat + 1 ≤ 0x100000000)
    (hhtif : (v14 + sign_extend (m := 64) (0xffd#12)).toNat + 1 ≤ tohostAddr
        ∨ tohostAddr + 8 ≤ (v14 + sign_extend (m := 64) (0xffd#12)).toNat)
    (hb0 : σ.mem[(v14 + sign_extend (m := 64) (0xffd#12)).toNat]? = some b0v)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (zero_extend (m := 64) b0v)) := by
  subst hpcv
  obtain ⟨hb0', hb1', hb2', hb3'⟩ := Vsa.Sim.Code.strlen_at_80006d58 hmem
  exact stepObs_alu σ i u (0x80006d58#64) vminstret (0xffd74783#32)
    (instruction.LOAD (0xffd#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x0f#5, true, 1))
    Register.x15 (zero_extend (m := 64) b0v) (0x83#8) (0x47#8) (0xd7#8) (0xff#8)
    hG hpc hminstret lbu_m3_word lbu_m3_notrvc
    (Vsa.Sim.DecodeTable.decode_ffd74783 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lbu_a5_a4 σ (0x80006d58#64) (0xffd#12) v14 b0v hG hx14 hlo hhiram hhtif hb0)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0' hb1' hb2' hb3' (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006d5c — `beqz a5,0x80006dbc` = `beq x15,x0` (imm 0x0060) -/

/-- **Observational step at 0x80006d5c, taken** (`beqz a5`, a5 = 0): PC → 0x80006dbc. -/
theorem site_80006d5c_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d5c#64 : BitVec 64)) (hv : (v15 == (0#64)) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x0060#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d5c hmem
  exact stepObs_branch_taken σ i u (0x80006d5c#64) vminstret (0x0060#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) bop.BEQ (0x06078063#32)
    (0x63#8) (0x80#8) (0x07#8) (0x06#8)
    hG hpc hminstret beqz_d54_word beqz_d54_notrvc
    (Vsa.Sim.DecodeTable.decode_06078063 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_beqz_a5_taken σ (0x80006d5c#64) (0x0060#13) v15 hG hpc hx15 (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Observational step at 0x80006d5c, not taken** (`beqz a5`, a5 ≠ 0): PC → pc+4. -/
theorem site_80006d5c_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d5c#64 : BitVec 64)) (hv : (v15 == (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d5c hmem
  exact stepObs_branch_nottaken σ i u (0x80006d5c#64) vminstret (0x0060#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) bop.BEQ (0x06078063#32)
    (0x63#8) (0x80#8) (0x07#8) (0x06#8)
    hG hpc hminstret beqz_d54_word beqz_d54_notrvc
    (Vsa.Sim.DecodeTable.decode_06078063 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_beqz_a5_nottaken σ (0x80006d5c#64) (0x0060#13) v15 hx15 hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006d60 — `lbu a5,-2(a4)` = `lbu x15, 0xffe(x14)` -/

theorem lbu_m2_word :
    (((0xff#8).append (0xe7#8)).append (0x47#8)).append (0x83#8) = (0xffe74783#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem lbu_m2_notrvc :
    Sail.BitVec.extractLsb ((((0xff#8).append (0xe7#8)).append (0x47#8)).append (0x83#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006d60** (`lbu a5,-2(a4)`). Writes `x15 := zext byte@(a4-2)`. -/
theorem site_80006d60
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 : BitVec 64) (b0v : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d60#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v14 + sign_extend (m := 64) (0xffe#12)).toNat)
    (hhiram : (v14 + sign_extend (m := 64) (0xffe#12)).toNat + 1 ≤ 0x100000000)
    (hhtif : (v14 + sign_extend (m := 64) (0xffe#12)).toNat + 1 ≤ tohostAddr
        ∨ tohostAddr + 8 ≤ (v14 + sign_extend (m := 64) (0xffe#12)).toNat)
    (hb0 : σ.mem[(v14 + sign_extend (m := 64) (0xffe#12)).toNat]? = some b0v)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (zero_extend (m := 64) b0v)) := by
  subst hpcv
  obtain ⟨hb0', hb1', hb2', hb3'⟩ := Vsa.Sim.Code.strlen_at_80006d60 hmem
  exact stepObs_alu σ i u (0x80006d60#64) vminstret (0xffe74783#32)
    (instruction.LOAD (0xffe#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x0f#5, true, 1))
    Register.x15 (zero_extend (m := 64) b0v) (0x83#8) (0x47#8) (0xe7#8) (0xff#8)
    hG hpc hminstret lbu_m2_word lbu_m2_notrvc
    (Vsa.Sim.DecodeTable.decode_ffe74783 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lbu_a5_a4 σ (0x80006d60#64) (0xffe#12) v14 b0v hG hx14 hlo hhiram hhtif hb0)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0' hb1' hb2' hb3' (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006d64 — `snez a0,a5` = `sltu x10,x0,x15` -/

theorem exec_snez_a0_a5 (σ : MState) (pc : BitVec 64) (v15 : BitVec 64)
    (hx15 : σ.regs.get? Register.x15 = some v15) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0f#5, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, rop.SLTU))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x10 (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) v15)))) := by
  have hx15₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  exact execute_rtype_sltu_char (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0a#5)
    (0#64) v15 (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x10 (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) v15))))
    (rX_bits_zero _) (rX_bits_x15 _ v15 hx15₂)
    (wX_bits_x10 _ (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) v15))))

theorem snez_a0_a5_word :
    (((0x00#8).append (0xf0#8)).append (0x35#8)).append (0x33#8) = (0x00f03533#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem snez_a0_a5_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xf0#8)).append (0x35#8)).append (0x33#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006d64** (`snez a0,a5`). Writes `x10 := (a5 ≠ 0 ? 1 : 0)`. -/
theorem site_80006d64
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d64#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10
          (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) v15)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d64 hmem
  exact stepObs_alu σ i u (0x80006d64#64) vminstret (0x00f03533#32)
    (instruction.RTYPE (regidx.Regidx 0x0f#5, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, rop.SLTU))
    Register.x10 (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) v15)))
    (0x33#8) (0x35#8) (0xf0#8) (0x00#8)
    hG hpc hminstret snez_a0_a5_word snez_a0_a5_notrvc
    (Vsa.Sim.DecodeTable.decode_00f03533 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_snez_a0_a5 σ (0x80006d64#64) v15 hx15)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006d68 — `add a0,a0,a3` = `add x10,x10,x13` -/

theorem exec_add_a0_a0_a3 (σ : MState) (pc : BitVec 64) (v10 v13 : BitVec 64)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hx13 : σ.regs.get? Register.x13 = some v13) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0d#5, regidx.Regidx 0x0a#5, regidx.Regidx 0x0a#5, rop.ADD))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x10 (v10 + v13)) := by
  have hx10₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx10
  have hx13₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x13 = some v13 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx13
  exact execute_rtype_add_char (regidx.Regidx 0x0d#5) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0a#5)
    v10 v13 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x10 (v10 + v13))
    (rX_bits_x10 _ v10 hx10₂) (rX_bits_x13 _ v13 hx13₂)
    (wX_bits_x10 _ (v10 + v13))

theorem add_a0_a0_a3_word :
    (((0x00#8).append (0xd5#8)).append (0x05#8)).append (0x33#8) = (0x00d50533#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem add_a0_a0_a3_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xd5#8)).append (0x05#8)).append (0x33#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006d68** (`add a0,a0,a3`). Writes `x10 := a0 + a3`. -/
theorem site_80006d68
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d68#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x10 (v10 + v13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d68 hmem
  exact stepObs_alu σ i u (0x80006d68#64) vminstret (0x00d50533#32)
    (instruction.RTYPE (regidx.Regidx 0x0d#5, regidx.Regidx 0x0a#5, regidx.Regidx 0x0a#5, rop.ADD))
    Register.x10 (v10 + v13) (0x33#8) (0x05#8) (0xd5#8) (0x00#8)
    hG hpc hminstret add_a0_a0_a3_word add_a0_a0_a3_notrvc
    (Vsa.Sim.DecodeTable.decode_00d50533 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_add_a0_a0_a3 σ (0x80006d68#64) v10 v13 hx10 hx13)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006d6c — `addi a0,a0,-2` = `addi x10,x10,0xffe` -/

theorem exec_addi_a0_m2 (σ : MState) (pc : BitVec 64) (v10 : BitVec 64)
    (hx10 : σ.regs.get? Register.x10 = some v10) :
    (execute (instruction.ITYPE (0xffe#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0a#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x10 (v10 + sign_extend (m := 64) (0xffe#12))) := by
  have hx10₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx10
  exact execute_itype_addi_char (0xffe#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0a#5) v10
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x10 (v10 + sign_extend (m := 64) (0xffe#12)))
    (rX_bits_x10 _ v10 hx10₂)
    (wX_bits_x10 _ (v10 + sign_extend (m := 64) (0xffe#12)))

theorem addi_a0_m2_word :
    (((0xff#8).append (0xe5#8)).append (0x05#8)).append (0x13#8) = (0xffe50513#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem addi_a0_m2_notrvc :
    Sail.BitVec.extractLsb ((((0xff#8).append (0xe5#8)).append (0x05#8)).append (0x13#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006d6c** (`addi a0,a0,-2`). Writes `x10 := a0 - 2`. -/
theorem site_80006d6c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d6c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10 (v10 + sign_extend (m := 64) (0xffe#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d6c hmem
  exact stepObs_alu σ i u (0x80006d6c#64) vminstret (0xffe50513#32)
    (instruction.ITYPE (0xffe#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 (v10 + sign_extend (m := 64) (0xffe#12)) (0x13#8) (0x05#8) (0xe5#8) (0xff#8)
    hG hpc hminstret addi_a0_m2_word addi_a0_m2_notrvc
    (Vsa.Sim.DecodeTable.decode_ffe50513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_addi_a0_m2 σ (0x80006d6c#64) v10 hx10)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006d70 — `ret` = `jalr x0,ra,0` (rs1 = x1 = ra) -/

theorem ret_d70_word :
    (((0x00#8).append (0x00#8)).append (0x80#8)).append (0x67#8) = (0x00008067#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem ret_d70_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x00#8)).append (0x80#8)).append (0x67#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006d70** (`ret`): PC → bit-0-cleared `ra`. -/
theorem site_80006d70
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vra : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some vra)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d70#64 : BitVec 64))
    (htgt : (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d70 hmem
  have hx1₂ : (rX_bits (regidx.Regidx 0x01#5)).run (afterNextPC (afterPrelude σ) (0x80006d70#64))
      = .ok vra (afterNextPC (afterPrelude σ) (0x80006d70#64)) := by
    apply rX_bits_x1
    rw [get?_afterNextPC σ (0x80006d70#64) _ (by decide) (by decide)]; exact hx1
  exact stepObs_jr σ i u (0x80006d70#64) vminstret vra (0x00008067#32) (0x000#12)
    (regidx.Regidx 0x01#5) (0x67#8) (0x80#8) (0x00#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    ret_d70_notrvc ret_d70_word
    (Vsa.Sim.DecodeTable.decode_00008067 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    hx1₂ htgt hi

/-! ## Byte-at-a-time alignment head (`0x80006d74 … 0x80006d90`)

Reached from the entry `bnez a5` when `a0` is not 8-aligned: advance a byte at a
time until aligned, checking for NUL. `beqz a3` tests the alignment counter
`a3 = a4 & 7`; `bnez a5` tests the loaded byte. -/

/-! ### Site 0x80006d74 — `beqz a3,0x80006cfc` = `beq x13,x0` (imm 0x1f88) -/

theorem beqz_a3_d74_word :
    (((0xf8#8).append (0x06#8)).append (0x84#8)).append (0xe3#8) = (0xf80684e3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem beqz_a3_d74_notrvc :
    Sail.BitVec.extractLsb ((((0xf8#8).append (0x06#8)).append (0x84#8)).append (0xe3#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem exec_beqz_a3_d74_taken (σ : MState) (pc : BitVec 64) (v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (htgt : (pc + sign_extend (m := 64) (0x1f88#13)).toNat % 4 = 0)
    (hv : (v13 == (0#64)) = true) :
    (execute (instruction.BTYPE (0x1f88#13, regidx.Regidx 0x00#5, regidx.Regidx 0x0d#5, bop.BEQ))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc (0x1f88#13)) := by
  have hx13₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x13 = some v13 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx13
  have hpc₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.PC = some pc := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc
  have hmisa₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.misa = some initMisa := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.misa
  exact execute_btype_beq_taken (0x1f88#13) (regidx.Regidx 0x0d#5) (regidx.Regidx 0x00#5)
    v13 (0#64) pc initMisa (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x13 _ v13 hx13₂) (rX_bits_zero _) hpc₂ hmisa₂ htgt hv

theorem exec_beqz_a3_d74_nottaken (σ : MState) (pc : BitVec 64) (v13 : BitVec 64)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hv : (v13 == (0#64)) = false) :
    (execute (instruction.BTYPE (0x1f88#13, regidx.Regidx 0x00#5, regidx.Regidx 0x0d#5, bop.BEQ))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) := by
  have hx13₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x13 = some v13 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx13
  exact execute_btype_beq_nottaken (0x1f88#13) (regidx.Regidx 0x0d#5) (regidx.Regidx 0x00#5)
    v13 (0#64) (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x13 _ v13 hx13₂) (rX_bits_zero _) hv

/-- **Observational step at 0x80006d74, taken** (`beqz a3`, a3 = 0): PC → 0x80006cfc. -/
theorem site_80006d74_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d74#64 : BitVec 64)) (hv : (v13 == (0#64)) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x1f88#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d74 hmem
  exact stepObs_branch_taken σ i u (0x80006d74#64) vminstret (0x1f88#13)
    (regidx.Regidx 0x0d#5) (regidx.Regidx 0x00#5) bop.BEQ (0xf80684e3#32)
    (0xe3#8) (0x84#8) (0x06#8) (0xf8#8)
    hG hpc hminstret beqz_a3_d74_word beqz_a3_d74_notrvc
    (Vsa.Sim.DecodeTable.decode_f80684e3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_beqz_a3_d74_taken σ (0x80006d74#64) v13 hG hpc hx13 (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Observational step at 0x80006d74, not taken** (`beqz a3`, a3 ≠ 0): PC → pc+4. -/
theorem site_80006d74_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d74#64 : BitVec 64)) (hv : (v13 == (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d74 hmem
  exact stepObs_branch_nottaken σ i u (0x80006d74#64) vminstret (0x1f88#13)
    (regidx.Regidx 0x0d#5) (regidx.Regidx 0x00#5) bop.BEQ (0xf80684e3#32)
    (0xe3#8) (0x84#8) (0x06#8) (0xf8#8)
    hG hpc hminstret beqz_a3_d74_word beqz_a3_d74_notrvc
    (Vsa.Sim.DecodeTable.decode_f80684e3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_beqz_a3_d74_nottaken σ (0x80006d74#64) v13 hx13 hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006d78 — `lbu a5,0(a4)` = `lbu x15, 0x000(x14)` -/

theorem lbu_0_word :
    (((0x00#8).append (0x07#8)).append (0x47#8)).append (0x83#8) = (0x00074783#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem lbu_0_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x07#8)).append (0x47#8)).append (0x83#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006d78** (`lbu a5,0(a4)`). Writes `x15 := zext byte@(a4)`. -/
theorem site_80006d78
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 : BitVec 64) (b0v : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d78#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v14 + sign_extend (m := 64) (0x000#12)).toNat)
    (hhiram : (v14 + sign_extend (m := 64) (0x000#12)).toNat + 1 ≤ 0x100000000)
    (hhtif : (v14 + sign_extend (m := 64) (0x000#12)).toNat + 1 ≤ tohostAddr
        ∨ tohostAddr + 8 ≤ (v14 + sign_extend (m := 64) (0x000#12)).toNat)
    (hb0 : σ.mem[(v14 + sign_extend (m := 64) (0x000#12)).toNat]? = some b0v)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (zero_extend (m := 64) b0v)) := by
  subst hpcv
  obtain ⟨hb0', hb1', hb2', hb3'⟩ := Vsa.Sim.Code.strlen_at_80006d78 hmem
  exact stepObs_alu σ i u (0x80006d78#64) vminstret (0x00074783#32)
    (instruction.LOAD (0x000#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x0f#5, true, 1))
    Register.x15 (zero_extend (m := 64) b0v) (0x83#8) (0x47#8) (0x07#8) (0x00#8)
    hG hpc hminstret lbu_0_word lbu_0_notrvc
    (Vsa.Sim.DecodeTable.decode_00074783 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lbu_a5_a4 σ (0x80006d78#64) (0x000#12) v14 b0v hG hx14 hlo hhiram hhtif hb0)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0' hb1' hb2' hb3' (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006d7c — `addi a4,a4,1` = `addi x14,x14,1` -/

theorem exec_addi_a4_1 (σ : MState) (pc : BitVec 64) (v14 : BitVec 64)
    (hx14 : σ.regs.get? Register.x14 = some v14) :
    (execute (instruction.ITYPE (0x001#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x0e#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x14 (v14 + sign_extend (m := 64) (0x001#12))) := by
  have hx14₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx14
  exact execute_itype_addi_char (0x001#12) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0e#5) v14
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x14 (v14 + sign_extend (m := 64) (0x001#12)))
    (rX_bits_x14 _ v14 hx14₂)
    (wX_bits_x14 _ (v14 + sign_extend (m := 64) (0x001#12)))

theorem addi_a4_1_word :
    (((0x00#8).append (0x17#8)).append (0x07#8)).append (0x13#8) = (0x00170713#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem addi_a4_1_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x17#8)).append (0x07#8)).append (0x13#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006d7c** (`addi a4,a4,1`). Writes `x14 := a4 + 1`. -/
theorem site_80006d7c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d7c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x14 (v14 + sign_extend (m := 64) (0x001#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d7c hmem
  exact stepObs_alu σ i u (0x80006d7c#64) vminstret (0x00170713#32)
    (instruction.ITYPE (0x001#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x0e#5, iop.ADDI))
    Register.x14 (v14 + sign_extend (m := 64) (0x001#12)) (0x13#8) (0x07#8) (0x17#8) (0x00#8)
    hG hpc hminstret addi_a4_1_word addi_a4_1_notrvc
    (Vsa.Sim.DecodeTable.decode_00170713 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_addi_a4_1 σ (0x80006d7c#64) v14 hx14)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006d80 — `andi a3,a4,7` = `andi x13,x14,7` -/

theorem exec_andi_a3_a4_7 (σ : MState) (pc : BitVec 64) (v14 : BitVec 64)
    (hx14 : σ.regs.get? Register.x14 = some v14) :
    (execute (instruction.ITYPE (0x007#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x0d#5, iop.ANDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x13 (v14 &&& sign_extend (m := 64) (0x007#12))) := by
  have hx14₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx14
  exact execute_itype_andi_char (0x007#12) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0d#5) v14
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x13 (v14 &&& sign_extend (m := 64) (0x007#12)))
    (rX_bits_x14 _ v14 hx14₂)
    (wX_bits_x13 _ (v14 &&& sign_extend (m := 64) (0x007#12)))

theorem andi_a3_a4_7_word :
    (((0x00#8).append (0x77#8)).append (0x76#8)).append (0x93#8) = (0x00777693#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem andi_a3_a4_7_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x77#8)).append (0x76#8)).append (0x93#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006d80** (`andi a3,a4,7`). Writes `x13 := a4 & 7`. -/
theorem site_80006d80
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d80#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x13 (v14 &&& sign_extend (m := 64) (0x007#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d80 hmem
  exact stepObs_alu σ i u (0x80006d80#64) vminstret (0x00777693#32)
    (instruction.ITYPE (0x007#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x0d#5, iop.ANDI))
    Register.x13 (v14 &&& sign_extend (m := 64) (0x007#12)) (0x93#8) (0x76#8) (0x77#8) (0x00#8)
    hG hpc hminstret andi_a3_a4_7_word andi_a3_a4_7_notrvc
    (Vsa.Sim.DecodeTable.decode_00777693 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_andi_a3_a4_7 σ (0x80006d80#64) v14 hx14)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006d84 — `bnez a5,0x80006d74` = `bne x15,x0` (imm 0x1ff0, loop back-edge) -/

theorem bnez_a5_d84_word :
    (((0xfe#8).append (0x07#8)).append (0x98#8)).append (0xe3#8) = (0xfe0798e3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem bnez_a5_d84_notrvc :
    Sail.BitVec.extractLsb ((((0xfe#8).append (0x07#8)).append (0x98#8)).append (0xe3#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem exec_bnez_a5_d84_taken (σ : MState) (pc : BitVec 64) (v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (htgt : (pc + sign_extend (m := 64) (0x1ff0#13)).toNat % 4 = 0)
    (hv : (v15 != (0#64)) = true) :
    (execute (instruction.BTYPE (0x1ff0#13, regidx.Regidx 0x00#5, regidx.Regidx 0x0f#5, bop.BNE))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc (0x1ff0#13)) := by
  have hx15₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  have hpc₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.PC = some pc := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc
  have hmisa₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.misa = some initMisa := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.misa
  exact execute_btype_bne_taken (0x1ff0#13) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5)
    v15 (0#64) pc initMisa (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x15 _ v15 hx15₂) (rX_bits_zero _) hpc₂ hmisa₂ htgt hv

theorem exec_bnez_a5_d84_nottaken (σ : MState) (pc : BitVec 64) (v15 : BitVec 64)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hv : (v15 != (0#64)) = false) :
    (execute (instruction.BTYPE (0x1ff0#13, regidx.Regidx 0x00#5, regidx.Regidx 0x0f#5, bop.BNE))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) := by
  have hx15₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  exact execute_btype_bne_nottaken (0x1ff0#13) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5)
    v15 (0#64) (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x15 _ v15 hx15₂) (rX_bits_zero _) hv

/-- **Observational step at 0x80006d84, taken** (`bnez a5`, a5 ≠ 0): back to 0x80006d74. -/
theorem site_80006d84_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d84#64 : BitVec 64)) (hv : (v15 != (0#64)) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x1ff0#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d84 hmem
  exact stepObs_branch_taken σ i u (0x80006d84#64) vminstret (0x1ff0#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) bop.BNE (0xfe0798e3#32)
    (0xe3#8) (0x98#8) (0x07#8) (0xfe#8)
    hG hpc hminstret bnez_a5_d84_word bnez_a5_d84_notrvc
    (Vsa.Sim.DecodeTable.decode_fe0798e3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bnez_a5_d84_taken σ (0x80006d84#64) v15 hG hpc hx15 (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Observational step at 0x80006d84, not taken** (`bnez a5`, a5 = 0): fall to 0x80006d88. -/
theorem site_80006d84_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d84#64 : BitVec 64)) (hv : (v15 != (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d84 hmem
  exact stepObs_branch_nottaken σ i u (0x80006d84#64) vminstret (0x1ff0#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) bop.BNE (0xfe0798e3#32)
    (0xe3#8) (0x98#8) (0x07#8) (0xfe#8)
    hG hpc hminstret bnez_a5_d84_word bnez_a5_d84_notrvc
    (Vsa.Sim.DecodeTable.decode_fe0798e3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bnez_a5_d84_nottaken σ (0x80006d84#64) v15 hx15 hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006d88 — `sub a4,a4,a0` = `sub x14,x14,x10` -/

theorem exec_sub_a4_a4_a0 (σ : MState) (pc : BitVec 64) (v14 v10 : BitVec 64)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hx10 : σ.regs.get? Register.x10 = some v10) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0a#5, regidx.Regidx 0x0e#5, regidx.Regidx 0x0e#5, rop.SUB))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x14 (v14 - v10)) := by
  have hx14₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx14
  have hx10₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx10
  exact execute_rtype_sub_char (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0e#5)
    v14 v10 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x14 (v14 - v10))
    (rX_bits_x14 _ v14 hx14₂) (rX_bits_x10 _ v10 hx10₂)
    (wX_bits_x14 _ (v14 - v10))

theorem sub_a4_a4_a0_word :
    (((0x40#8).append (0xa7#8)).append (0x07#8)).append (0x33#8) = (0x40a70733#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem sub_a4_a4_a0_notrvc :
    Sail.BitVec.extractLsb ((((0x40#8).append (0xa7#8)).append (0x07#8)).append (0x33#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006d88** (`sub a4,a4,a0`). Writes `x14 := a4 - a0`. -/
theorem site_80006d88
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d88#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x14 (v14 - v10)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d88 hmem
  exact stepObs_alu σ i u (0x80006d88#64) vminstret (0x40a70733#32)
    (instruction.RTYPE (regidx.Regidx 0x0a#5, regidx.Regidx 0x0e#5, regidx.Regidx 0x0e#5, rop.SUB))
    Register.x14 (v14 - v10) (0x33#8) (0x07#8) (0xa7#8) (0x40#8)
    hG hpc hminstret sub_a4_a4_a0_word sub_a4_a4_a0_notrvc
    (Vsa.Sim.DecodeTable.decode_40a70733 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sub_a4_a4_a0 σ (0x80006d88#64) v14 v10 hx14 hx10)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006d8c — `addi a0,a4,-1` = `addi x10,x14,0xfff` -/

theorem exec_addi_a0_a4_m1 (σ : MState) (pc : BitVec 64) (v14 : BitVec 64)
    (hx14 : σ.regs.get? Register.x14 = some v14) :
    (execute (instruction.ITYPE (0xfff#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x0a#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x10 (v14 + sign_extend (m := 64) (0xfff#12))) := by
  have hx14₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx14
  exact execute_itype_addi_char (0xfff#12) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0a#5) v14
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x10 (v14 + sign_extend (m := 64) (0xfff#12)))
    (rX_bits_x14 _ v14 hx14₂)
    (wX_bits_x10 _ (v14 + sign_extend (m := 64) (0xfff#12)))

theorem addi_a0_a4_m1_word :
    (((0xff#8).append (0xf7#8)).append (0x05#8)).append (0x13#8) = (0xfff70513#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem addi_a0_a4_m1_notrvc :
    Sail.BitVec.extractLsb ((((0xff#8).append (0xf7#8)).append (0x05#8)).append (0x13#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006d8c** (`addi a0,a4,-1`). Writes `x10 := a4 - 1`. -/
theorem site_80006d8c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d8c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10 (v14 + sign_extend (m := 64) (0xfff#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d8c hmem
  exact stepObs_alu σ i u (0x80006d8c#64) vminstret (0xfff70513#32)
    (instruction.ITYPE (0xfff#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 (v14 + sign_extend (m := 64) (0xfff#12)) (0x13#8) (0x05#8) (0xf7#8) (0xff#8)
    hG hpc hminstret addi_a0_a4_m1_word addi_a0_a4_m1_notrvc
    (Vsa.Sim.DecodeTable.decode_fff70513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_addi_a0_a4_m1 σ (0x80006d8c#64) v14 hx14)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006d90 — `ret` = `jalr x0,ra,0` -/

/-- **Observational step at 0x80006d90** (`ret`): PC → bit-0-cleared `ra`. -/
theorem site_80006d90
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vra : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some vra)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d90#64 : BitVec 64))
    (htgt : (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d90 hmem
  have hx1₂ : (rX_bits (regidx.Regidx 0x01#5)).run (afterNextPC (afterPrelude σ) (0x80006d90#64))
      = .ok vra (afterNextPC (afterPrelude σ) (0x80006d90#64)) := by
    apply rX_bits_x1
    rw [get?_afterNextPC σ (0x80006d90#64) _ (by decide) (by decide)]; exact hx1
  exact stepObs_jr σ i u (0x80006d90#64) vminstret vra (0x00008067#32) (0x000#12)
    (regidx.Regidx 0x01#5) (0x67#8) (0x80#8) (0x00#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    ret_d70_notrvc ret_d70_word
    (Vsa.Sim.DecodeTable.decode_00008067 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    hx1₂ htgt hi

/-! ## Exit blocks (`0x80006d94 … 0x80006dc0`)

Six `addi a0,a3,imm; ret` pairs — the word-loop tail jumps to the block matching
which byte held the NUL, computing `strlen = (a4 - a0) - k`. The `addi` sites all
share one execute (`exec_addi_a0_a3`, `addi x10,x13,imm`); the `ret` sites are the
`stepObs_jr` instantiation (identical to `site_80006d70`/`d90` at a different pc). -/

/-- Shared `execute (addi x10,x13,imm)` for the exit-block `addi a0,a3,imm` sites. -/
theorem exec_addi_a0_a3 (σ : MState) (pc : BitVec 64) (imm : BitVec 12) (v13 : BitVec 64)
    (hx13 : σ.regs.get? Register.x13 = some v13) :
    (execute (instruction.ITYPE (imm, regidx.Regidx 0x0d#5, regidx.Regidx 0x0a#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x10 (v13 + sign_extend (m := 64) imm)) := by
  have hx13₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x13 = some v13 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx13
  exact execute_itype_addi_char imm (regidx.Regidx 0x0d#5) (regidx.Regidx 0x0a#5) v13
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x10 (v13 + sign_extend (m := 64) imm))
    (rX_bits_x13 _ v13 hx13₂)
    (wX_bits_x10 _ (v13 + sign_extend (m := 64) imm))

/-- Shared `ret` observational step for the exit-block `ret` sites (over the pc and
its four fetch bytes, identical to `site_80006d70`). -/
theorem site_exit_ret
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vra : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some vra)
    (hb0 : σ.mem[pc.toNat]? = some (0x67#8)) (hb1 : σ.mem[pc.toNat + 1]? = some (0x80#8))
    (hb2 : σ.mem[pc.toNat + 2]? = some (0x00#8)) (hb3 : σ.mem[pc.toNat + 3]? = some (0x00#8))
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (htgt : (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  have hx1₂ : (rX_bits (regidx.Regidx 0x01#5)).run (afterNextPC (afterPrelude σ) pc)
      = .ok vra (afterNextPC (afterPrelude σ) pc) := by
    apply rX_bits_x1
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx1
  exact stepObs_jr σ i u pc vminstret vra (0x00008067#32) (0x000#12)
    (regidx.Regidx 0x01#5) (0x67#8) (0x80#8) (0x00#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 hlo hhi halign
    ret_d70_notrvc ret_d70_word
    (Vsa.Sim.DecodeTable.decode_00008067 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    hx1₂ htgt hi

/-! ### Site 0x80006d94 — `addi a0,a3,-7` = `addi x10,x13,0xff9` -/

theorem addi_a0_a3_m7_word :
    (((0xff#8).append (0x96#8)).append (0x85#8)).append (0x13#8) = (0xff968513#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem addi_a0_a3_m7_notrvc :
    Sail.BitVec.extractLsb ((((0xff#8).append (0x96#8)).append (0x85#8)).append (0x13#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006d94** (`addi a0,a3,-7`). Writes `x10 := a3 - 7`. -/
theorem site_80006d94
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d94#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10 (v13 + sign_extend (m := 64) (0xff9#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d94 hmem
  exact stepObs_alu σ i u (0x80006d94#64) vminstret (0xff968513#32)
    (instruction.ITYPE (0xff9#12, regidx.Regidx 0x0d#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 (v13 + sign_extend (m := 64) (0xff9#12)) (0x13#8) (0x85#8) (0x96#8) (0xff#8)
    hG hpc hminstret addi_a0_a3_m7_word addi_a0_a3_m7_notrvc
    (Vsa.Sim.DecodeTable.decode_ff968513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_addi_a0_a3 σ (0x80006d94#64) (0xff9#12) v13 hx13)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006d98 — `ret` -/

/-- **Observational step at 0x80006d98** (`ret`). -/
theorem site_80006d98
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vra : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some vra)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d98#64 : BitVec 64))
    (htgt : (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d98 hmem
  exact site_exit_ret σ i u (0x80006d98#64) vminstret vra hG hpc hminstret hx1
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) htgt hi

/-! ### Site 0x80006d9c — `addi a0,a3,-8` = `addi x10,x13,0xff8` -/

theorem addi_a0_a3_m8_word :
    (((0xff#8).append (0x86#8)).append (0x85#8)).append (0x13#8) = (0xff868513#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem addi_a0_a3_m8_notrvc :
    Sail.BitVec.extractLsb ((((0xff#8).append (0x86#8)).append (0x85#8)).append (0x13#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006d9c** (`addi a0,a3,-8`). Writes `x10 := a3 - 8`. -/
theorem site_80006d9c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d9c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10 (v13 + sign_extend (m := 64) (0xff8#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d9c hmem
  exact stepObs_alu σ i u (0x80006d9c#64) vminstret (0xff868513#32)
    (instruction.ITYPE (0xff8#12, regidx.Regidx 0x0d#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 (v13 + sign_extend (m := 64) (0xff8#12)) (0x13#8) (0x85#8) (0x86#8) (0xff#8)
    hG hpc hminstret addi_a0_a3_m8_word addi_a0_a3_m8_notrvc
    (Vsa.Sim.DecodeTable.decode_ff868513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_addi_a0_a3 σ (0x80006d9c#64) (0xff8#12) v13 hx13)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006da0 — `ret` -/

/-- **Observational step at 0x80006da0** (`ret`). -/
theorem site_80006da0
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vra : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some vra)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006da0#64 : BitVec 64))
    (htgt : (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006da0 hmem
  exact site_exit_ret σ i u (0x80006da0#64) vminstret vra hG hpc hminstret hx1
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) htgt hi

/-! ### Site 0x80006da4 — `addi a0,a3,-5` = `addi x10,x13,0xffb` -/

theorem addi_a0_a3_m5_word :
    (((0xff#8).append (0xb6#8)).append (0x85#8)).append (0x13#8) = (0xffb68513#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem addi_a0_a3_m5_notrvc :
    Sail.BitVec.extractLsb ((((0xff#8).append (0xb6#8)).append (0x85#8)).append (0x13#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006da4** (`addi a0,a3,-5`). Writes `x10 := a3 - 5`. -/
theorem site_80006da4
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006da4#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10 (v13 + sign_extend (m := 64) (0xffb#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006da4 hmem
  exact stepObs_alu σ i u (0x80006da4#64) vminstret (0xffb68513#32)
    (instruction.ITYPE (0xffb#12, regidx.Regidx 0x0d#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 (v13 + sign_extend (m := 64) (0xffb#12)) (0x13#8) (0x85#8) (0xb6#8) (0xff#8)
    hG hpc hminstret addi_a0_a3_m5_word addi_a0_a3_m5_notrvc
    (Vsa.Sim.DecodeTable.decode_ffb68513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_addi_a0_a3 σ (0x80006da4#64) (0xffb#12) v13 hx13)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006da8 — `ret` -/

/-- **Observational step at 0x80006da8** (`ret`). -/
theorem site_80006da8
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vra : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some vra)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006da8#64 : BitVec 64))
    (htgt : (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006da8 hmem
  exact site_exit_ret σ i u (0x80006da8#64) vminstret vra hG hpc hminstret hx1
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) htgt hi

/-! ### Site 0x80006dac — `addi a0,a3,-6` = `addi x10,x13,0xffa` -/

theorem addi_a0_a3_m6_word :
    (((0xff#8).append (0xa6#8)).append (0x85#8)).append (0x13#8) = (0xffa68513#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem addi_a0_a3_m6_notrvc :
    Sail.BitVec.extractLsb ((((0xff#8).append (0xa6#8)).append (0x85#8)).append (0x13#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006dac** (`addi a0,a3,-6`). Writes `x10 := a3 - 6`. -/
theorem site_80006dac
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006dac#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10 (v13 + sign_extend (m := 64) (0xffa#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006dac hmem
  exact stepObs_alu σ i u (0x80006dac#64) vminstret (0xffa68513#32)
    (instruction.ITYPE (0xffa#12, regidx.Regidx 0x0d#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 (v13 + sign_extend (m := 64) (0xffa#12)) (0x13#8) (0x85#8) (0xa6#8) (0xff#8)
    hG hpc hminstret addi_a0_a3_m6_word addi_a0_a3_m6_notrvc
    (Vsa.Sim.DecodeTable.decode_ffa68513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_addi_a0_a3 σ (0x80006dac#64) (0xffa#12) v13 hx13)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006db0 — `ret` -/

/-- **Observational step at 0x80006db0** (`ret`). -/
theorem site_80006db0
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vra : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some vra)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006db0#64 : BitVec 64))
    (htgt : (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006db0 hmem
  exact site_exit_ret σ i u (0x80006db0#64) vminstret vra hG hpc hminstret hx1
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) htgt hi

/-! ### Site 0x80006db4 — `addi a0,a3,-4` = `addi x10,x13,0xffc` -/

theorem addi_a0_a3_m4_word :
    (((0xff#8).append (0xc6#8)).append (0x85#8)).append (0x13#8) = (0xffc68513#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem addi_a0_a3_m4_notrvc :
    Sail.BitVec.extractLsb ((((0xff#8).append (0xc6#8)).append (0x85#8)).append (0x13#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006db4** (`addi a0,a3,-4`). Writes `x10 := a3 - 4`. -/
theorem site_80006db4
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006db4#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10 (v13 + sign_extend (m := 64) (0xffc#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006db4 hmem
  exact stepObs_alu σ i u (0x80006db4#64) vminstret (0xffc68513#32)
    (instruction.ITYPE (0xffc#12, regidx.Regidx 0x0d#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 (v13 + sign_extend (m := 64) (0xffc#12)) (0x13#8) (0x85#8) (0xc6#8) (0xff#8)
    hG hpc hminstret addi_a0_a3_m4_word addi_a0_a3_m4_notrvc
    (Vsa.Sim.DecodeTable.decode_ffc68513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_addi_a0_a3 σ (0x80006db4#64) (0xffc#12) v13 hx13)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006db8 — `ret` -/

/-- **Observational step at 0x80006db8** (`ret`). -/
theorem site_80006db8
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vra : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some vra)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006db8#64 : BitVec 64))
    (htgt : (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006db8 hmem
  exact site_exit_ret σ i u (0x80006db8#64) vminstret vra hG hpc hminstret hx1
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) htgt hi

/-! ### Site 0x80006dbc — `addi a0,a3,-3` = `addi x10,x13,0xffd` -/

theorem addi_a0_a3_m3_word :
    (((0xff#8).append (0xd6#8)).append (0x85#8)).append (0x13#8) = (0xffd68513#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem addi_a0_a3_m3_notrvc :
    Sail.BitVec.extractLsb ((((0xff#8).append (0xd6#8)).append (0x85#8)).append (0x13#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006dbc** (`addi a0,a3,-3`). Writes `x10 := a3 - 3`. -/
theorem site_80006dbc
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006dbc#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10 (v13 + sign_extend (m := 64) (0xffd#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006dbc hmem
  exact stepObs_alu σ i u (0x80006dbc#64) vminstret (0xffd68513#32)
    (instruction.ITYPE (0xffd#12, regidx.Regidx 0x0d#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 (v13 + sign_extend (m := 64) (0xffd#12)) (0x13#8) (0x85#8) (0xd6#8) (0xff#8)
    hG hpc hminstret addi_a0_a3_m3_word addi_a0_a3_m3_notrvc
    (Vsa.Sim.DecodeTable.decode_ffd68513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_addi_a0_a3 σ (0x80006dbc#64) (0xffd#12) v13 hx13)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006dc0 — `ret` -/

/-- **Observational step at 0x80006dc0** (`ret`). -/
theorem site_80006dc0
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vra : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some vra)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006dc0#64 : BitVec 64))
    (htgt : (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006dc0 hmem
  exact site_exit_ret σ i u (0x80006dc0#64) vminstret vra hG hpc hminstret hx1
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) htgt hi

end Vsa.Sim
