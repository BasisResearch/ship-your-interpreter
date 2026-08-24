import Vsa.Sim.SnprintfSites
import Vsa.Sim.ValueSites
import Vsa.Sim.StrcpySites

/-!
# M3 Layer-3 — `SnprintfSites3` : the decimal-loop entry step battery (`_sn5`)

Sites for the segment between the sign block and the digit loop
(`experiments/M3-snprintf-lld.md` §1.4): the flag guard `bltz s4` at
`0x800080f8`, the flag mask `andi t1,t1,-129`, the fast/multi split
`li a5,9; bltu a5,a4` at `0x80008100/04`, and the multi-digit loop-entry block
`0x800082c8 … 0x800082f8` (buffer-top setup, five `sd` spills, one `ld` reload,
digit count/grouping-flag init, `mv s0,a4`, and the `j 0x8000831c` into the
do-while's mod-emit step).

Instruction words were decoded from the pinned code bytes
(`Code/SvfprintfSlice.lean`); the decode lemmas are the exhaustive
`DecodeTable.Batch*` shards.  Store sites use `exec_sd_val`
(`ValueSites`), the reload uses `exec_ld_total` (`StrcpySites` — total, no
byte-definedness needed since the value is dead downstream).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

private theorem misa_pre5 (σ : MState) (hG : GoodState σ) :
    (afterPrelude σ).regs.get? Register.misa = some ((Vsa.Sim.initMisa) : RegisterType Register.misa) := by
  rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa
private theorem priv_pre5 (σ : MState) (hG : GoodState σ) :
    (afterPrelude σ).regs.get? Register.cur_privilege = some (Privilege.Machine : RegisterType Register.cur_privilege) := by
  rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege
private theorem sec_pre5 (σ : MState) (hG : GoodState σ) :
    (afterPrelude σ).regs.get? Register.mseccfg = some ((0#64) : RegisterType Register.mseccfg) := by
  rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg

/-! ## Instruction-word assembly / not-RVC facts -/

theorem w_15c10b13_sn5 : (((0x15#8).append (0xc1#8)).append (0x0b#8)).append (0x13#8) = (0x15c10b13#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_15c10b13_sn5 : Sail.BitVec.extractLsb ((((0x15#8).append (0xc1#8)).append (0x0b#8)).append (0x13#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_03713823_sn5 : (((0x03#8).append (0x71#8)).append (0x38#8)).append (0x23#8) = (0x03713823#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_03713823_sn5 : Sail.BitVec.extractLsb ((((0x03#8).append (0x71#8)).append (0x38#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_03413c23_sn5 : (((0x03#8).append (0x41#8)).append (0x3c#8)).append (0x23#8) = (0x03413c23#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_03413c23_sn5 : Sail.BitVec.extractLsb ((((0x03#8).append (0x41#8)).append (0x3c#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_06813c23_sn5 : (((0x06#8).append (0x81#8)).append (0x3c#8)).append (0x23#8) = (0x06813c23#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_06813c23_sn5 : Sail.BitVec.extractLsb ((((0x06#8).append (0x81#8)).append (0x3c#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_06813a03_sn5 : (((0x06#8).append (0x81#8)).append (0x3a#8)).append (0x03#8) = (0x06813a03#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_06813a03_sn5 : Sail.BitVec.extractLsb ((((0x06#8).append (0x81#8)).append (0x3a#8)).append (0x03#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_000b0c93_sn5 : (((0x00#8).append (0x0b#8)).append (0x0c#8)).append (0x93#8) = (0x000b0c93#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_000b0c93_sn5 : Sail.BitVec.extractLsb ((((0x00#8).append (0x0b#8)).append (0x0c#8)).append (0x93#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_03c13023_sn5 : (((0x03#8).append (0xc1#8)).append (0x30#8)).append (0x23#8) = (0x03c13023#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_03c13023_sn5 : Sail.BitVec.extractLsb ((((0x03#8).append (0xc1#8)).append (0x30#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_02613423_sn5 : (((0x02#8).append (0x61#8)).append (0x34#8)).append (0x23#8) = (0x02613423#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_02613423_sn5 : Sail.BitVec.extractLsb ((((0x02#8).append (0x61#8)).append (0x34#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_00000b93_sn5 : (((0x00#8).append (0x00#8)).append (0x0b#8)).append (0x93#8) = (0x00000b93#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00000b93_sn5 : Sail.BitVec.extractLsb ((((0x00#8).append (0x00#8)).append (0x0b#8)).append (0x93#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_40037d93_sn5 : (((0x40#8).append (0x03#8)).append (0x7d#8)).append (0x93#8) = (0x40037d93#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_40037d93_sn5 : Sail.BitVec.extractLsb ((((0x40#8).append (0x03#8)).append (0x7d#8)).append (0x93#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_07613823_sn5 : (((0x07#8).append (0x61#8)).append (0x38#8)).append (0x23#8) = (0x07613823#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_07613823_sn5 : Sail.BitVec.extractLsb ((((0x07#8).append (0x61#8)).append (0x38#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_00070413_sn5 : (((0x00#8).append (0x07#8)).append (0x04#8)).append (0x13#8) = (0x00070413#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00070413_sn5 : Sail.BitVec.extractLsb ((((0x00#8).append (0x07#8)).append (0x04#8)).append (0x13#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_0240006f_sn5 : (((0x02#8).append (0x40#8)).append (0x00#8)).append (0x6f#8) = (0x0240006f#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_0240006f_sn5 : Sail.BitVec.extractLsb ((((0x02#8).append (0x40#8)).append (0x00#8)).append (0x6f#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_000a4463_sn5 : (((0x00#8).append (0x0a#8)).append (0x44#8)).append (0x63#8) = (0x000a4463#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_000a4463_sn5 : Sail.BitVec.extractLsb ((((0x00#8).append (0x0a#8)).append (0x44#8)).append (0x63#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_f7f37313_sn5 : (((0xf7#8).append (0xf3#8)).append (0x73#8)).append (0x13#8) = (0xf7f37313#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_f7f37313_sn5 : Sail.BitVec.extractLsb ((((0xf7#8).append (0xf3#8)).append (0x73#8)).append (0x13#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_1ce7e263_sn5 : (((0x1c#8).append (0xe7#8)).append (0xe2#8)).append (0x63#8) = (0x1ce7e263#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_1ce7e263_sn5 : Sail.BitVec.extractLsb ((((0x1c#8).append (0xe7#8)).append (0xe2#8)).append (0x63#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-! ## Pre-entry: the flag guard `bltz s4`, flag mask, and the fast/multi split -/

/-! ### 0x800080f8 — `bltz s4` (= `blt x20,x0,+8` → 0x80008100) -/
theorem site_800080f8_taken_sn5
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v20 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx20 : σ.regs.get? Register.x20 = some v20)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x800080f8#64 : BitVec 64))
    (hv : zopz0zI_s v20 (0#64) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x0008#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800080f8 hmem
  have hx20₂ : (afterNextPC (afterPrelude σ) (0x800080f8#64)).regs.get? Register.x20 = some v20 := by
    rw [get?_afterNextPC σ (0x800080f8#64) _ (by decide) (by decide)]; exact hx20
  exact stepObs_branch_taken σ i u (0x800080f8#64) vminstret (0x0008#13)
    (regidx.Regidx 0x14#5) (regidx.Regidx 0x00#5) bop.BLT (0x000a4463#32) (0x63#8) (0x44#8) (0x0a#8) (0x00#8)
    hG hpc hminstret w_000a4463_sn5 nr_000a4463_sn5
    (Vsa.Sim.DecodeTable.decode_000a4463 (afterPrelude σ) (misa_pre5 σ hG) (priv_pre5 σ hG) (sec_pre5 σ hG))
    (execute_btype_blt_taken (0x0008#13) (regidx.Regidx 0x14#5) (regidx.Regidx 0x00#5) v20 (0#64)
      (0x800080f8#64) (Vsa.Sim.initMisa) (afterNextPC (afterPrelude σ) (0x800080f8#64))
      (rX_bits_x20 _ v20 hx20₂) (rX_bits_zero _)
      (by rw [get?_afterNextPC σ (0x800080f8#64) _ (by decide) (by decide)]; exact hpc)
      (by rw [get?_afterNextPC σ (0x800080f8#64) _ (by decide) (by decide)]; exact hG.misa)
      (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_800080f8_nottaken_sn5
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v20 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx20 : σ.regs.get? Register.x20 = some v20)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x800080f8#64 : BitVec 64))
    (hv : zopz0zI_s v20 (0#64) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800080f8 hmem
  have hx20₂ : (afterNextPC (afterPrelude σ) (0x800080f8#64)).regs.get? Register.x20 = some v20 := by
    rw [get?_afterNextPC σ (0x800080f8#64) _ (by decide) (by decide)]; exact hx20
  exact stepObs_branch_nottaken σ i u (0x800080f8#64) vminstret (0x0008#13)
    (regidx.Regidx 0x14#5) (regidx.Regidx 0x00#5) bop.BLT (0x000a4463#32) (0x63#8) (0x44#8) (0x0a#8) (0x00#8)
    hG hpc hminstret w_000a4463_sn5 nr_000a4463_sn5
    (Vsa.Sim.DecodeTable.decode_000a4463 (afterPrelude σ) (misa_pre5 σ hG) (priv_pre5 σ hG) (sec_pre5 σ hG))
    (execute_btype_blt_nottaken (0x0008#13) (regidx.Regidx 0x14#5) (regidx.Regidx 0x00#5) v20 (0#64)
      (afterNextPC (afterPrelude σ) (0x800080f8#64))
      (rX_bits_x20 _ v20 hx20₂) (rX_bits_zero _) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x800080fc — `andi t1,t1,-129` (clear flag bit 7; bit 10 untouched) -/
theorem site_800080fc_sn5
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v6 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx6 : σ.regs.get? Register.x6 = some v6)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x800080fc#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x6 (v6 &&& sign_extend (m := 64) (0xf7f#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800080fc hmem
  have hx6₂ : (afterNextPC (afterPrelude σ) (0x800080fc#64)).regs.get? Register.x6 = some v6 := by
    rw [get?_afterNextPC σ (0x800080fc#64) _ (by decide) (by decide)]; exact hx6
  exact stepObs_alu σ i u (0x800080fc#64) vminstret (0xf7f37313#32)
    (instruction.ITYPE (0xf7f#12, regidx.Regidx 0x06#5, regidx.Regidx 0x06#5, iop.ANDI))
    Register.x6 (v6 &&& sign_extend (m := 64) (0xf7f#12)) (0x13#8) (0x73#8) (0xf3#8) (0xf7#8)
    hG hpc hminstret w_f7f37313_sn5 nr_f7f37313_sn5
    (Vsa.Sim.DecodeTable.decode_f7f37313 (afterPrelude σ) (misa_pre5 σ hG) (priv_pre5 σ hG) (sec_pre5 σ hG))
    (execute_itype_andi_char (0xf7f#12) (regidx.Regidx 0x06#5) (regidx.Regidx 0x06#5) v6
      (afterNextPC (afterPrelude σ) (0x800080fc#64))
      (sigma3_alu σ (0x800080fc#64) Register.x6 (v6 &&& sign_extend (m := 64) (0xf7f#12)))
      (rX_bits_x6 _ v6 hx6₂) (wX_bits_x6 _ (v6 &&& sign_extend (m := 64) (0xf7f#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80008100 — `li a5,9` -/
theorem site_80008100_sn5
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x80008100#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x15 ((0#64) + sign_extend (m := 64) (0x009#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80008100 hmem
  exact stepObs_alu σ i u (0x80008100#64) vminstret (0x00900793#32)
    (instruction.ITYPE (0x009#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0f#5, iop.ADDI))
    Register.x15 ((0#64) + sign_extend (m := 64) (0x009#12)) (0x93#8) (0x07#8) (0x90#8) (0x00#8)
    hG hpc hminstret w_00900793_sn nr_00900793_sn
    (Vsa.Sim.DecodeTable.decode_00900793 (afterPrelude σ) (misa_pre5 σ hG) (priv_pre5 σ hG) (sec_pre5 σ hG))
    (execute_itype_addi_char (0x009#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0f#5) (0#64)
      (afterNextPC (afterPrelude σ) (0x80008100#64))
      (sigma3_alu σ (0x80008100#64) Register.x15 ((0#64) + sign_extend (m := 64) (0x009#12)))
      (rX_bits_zero _) (wX_bits_x15 _ ((0#64) + sign_extend (m := 64) (0x009#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80008104 — `bltu a5,a4,+452` → 0x800082c8 (magnitude > 9: multi-digit path) -/
theorem site_80008104_taken_sn5
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x80008104#64 : BitVec 64))
    (hv : zopz0zI_u v15 v14 = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x01c4#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80008104 hmem
  have hx15₂ : (afterNextPC (afterPrelude σ) (0x80008104#64)).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ (0x80008104#64) _ (by decide) (by decide)]; exact hx15
  have hx14₂ : (afterNextPC (afterPrelude σ) (0x80008104#64)).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ (0x80008104#64) _ (by decide) (by decide)]; exact hx14
  exact stepObs_branch_taken σ i u (0x80008104#64) vminstret (0x01c4#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0e#5) bop.BLTU (0x1ce7e263#32) (0x63#8) (0xe2#8) (0xe7#8) (0x1c#8)
    hG hpc hminstret w_1ce7e263_sn5 nr_1ce7e263_sn5
    (Vsa.Sim.DecodeTable.decode_1ce7e263 (afterPrelude σ) (misa_pre5 σ hG) (priv_pre5 σ hG) (sec_pre5 σ hG))
    (execute_btype_bltu_taken (0x01c4#13) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0e#5) v15 v14
      (0x80008104#64) (Vsa.Sim.initMisa) (afterNextPC (afterPrelude σ) (0x80008104#64))
      (rX_bits_x15 _ v15 hx15₂) (rX_bits_x14 _ v14 hx14₂)
      (by rw [get?_afterNextPC σ (0x80008104#64) _ (by decide) (by decide)]; exact hpc)
      (by rw [get?_afterNextPC σ (0x80008104#64) _ (by decide) (by decide)]; exact hG.misa)
      (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## The multi-digit loop-entry block `0x800082c8 … 0x800082f8` -/

/-! ### 0x800082c8 — `addi s6,sp,348` (s6 := buffer top) -/
theorem site_800082c8_sn5
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v2 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x800082c8#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x22 (v2 + sign_extend (m := 64) (0x15c#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800082c8 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x800082c8#64)).regs.get? Register.x2 = some v2 := by
    rw [get?_afterNextPC σ (0x800082c8#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x800082c8#64) vminstret (0x15c10b13#32)
    (instruction.ITYPE (0x15c#12, regidx.Regidx 0x02#5, regidx.Regidx 0x16#5, iop.ADDI))
    Register.x22 (v2 + sign_extend (m := 64) (0x15c#12)) (0x13#8) (0x0b#8) (0xc1#8) (0x15#8)
    hG hpc hminstret w_15c10b13_sn5 nr_15c10b13_sn5
    (Vsa.Sim.DecodeTable.decode_15c10b13 (afterPrelude σ) (misa_pre5 σ hG) (priv_pre5 σ hG) (sec_pre5 σ hG))
    (execute_itype_addi_char (0x15c#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x16#5) v2
      (afterNextPC (afterPrelude σ) (0x800082c8#64))
      (sigma3_alu σ (0x800082c8#64) Register.x22 (v2 + sign_extend (m := 64) (0x15c#12)))
      (rX_bits_x2 _ v2 hx2₂) (wX_bits_x22 _ (v2 + sign_extend (m := 64) (0x15c#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x800082cc — `sd s7,48(sp)` (spill) -/
theorem site_800082cc_sn5
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp vdata : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hdata : σ.regs.get? Register.x23 = some vdata)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x800082cc#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x030#12)).toNat)
    (hahiram : (vsp + sign_extend (m := 64) (0x030#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (vsp + sign_extend (m := 64) (0x030#12)).toNat)
    (haalign : (vsp + sign_extend (m := 64) (0x030#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x800082cc#64)).mem
        (vsp + sign_extend (m := 64) (0x030#12)).toNat (sdData_val vdata) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x800082cc#64)).mem
            (vsp + sign_extend (m := 64) (0x030#12)).toNat (sdData_val vdata))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800082cc hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x800082cc#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x800082cc#64) _ (by decide) (by decide)]; exact hx2
  have hdata₂ : (afterNextPC (afterPrelude σ) (0x800082cc#64)).regs.get? Register.x23 = some vdata := by
    rw [get?_afterNextPC σ (0x800082cc#64) _ (by decide) (by decide)]; exact hdata
  exact stepObs_store σ i u (0x800082cc#64) vminstret (0x03713823#32)
    (instruction.STORE (0x030#12, regidx.Regidx 0x17#5, regidx.Regidx 0x02#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x800082cc#64)).mem
      (vsp + sign_extend (m := 64) (0x030#12)).toNat (sdData_val vdata))
    (0x23#8) (0x38#8) (0x71#8) (0x03#8)
    hG hpc hminstret w_03713823_sn5 nr_03713823_sn5
    (Vsa.Sim.DecodeTable.decode_03713823 (afterPrelude σ) (misa_pre5 σ hG) (priv_pre5 σ hG) (sec_pre5 σ hG))
    (exec_sd_val σ (0x800082cc#64) (0x030#12) (regidx.Regidx 0x17#5) (regidx.Regidx 0x02#5)
      vsp vdata hG (rX_bits_x2 _ vsp hx2₂) (rX_bits_x23 _ vdata hdata₂)
      halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x800082d0 — `sd s4,56(sp)` (spill) -/
theorem site_800082d0_sn5
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp vdata : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hdata : σ.regs.get? Register.x20 = some vdata)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x800082d0#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x038#12)).toNat)
    (hahiram : (vsp + sign_extend (m := 64) (0x038#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (vsp + sign_extend (m := 64) (0x038#12)).toNat)
    (haalign : (vsp + sign_extend (m := 64) (0x038#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x800082d0#64)).mem
        (vsp + sign_extend (m := 64) (0x038#12)).toNat (sdData_val vdata) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x800082d0#64)).mem
            (vsp + sign_extend (m := 64) (0x038#12)).toNat (sdData_val vdata))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800082d0 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x800082d0#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x800082d0#64) _ (by decide) (by decide)]; exact hx2
  have hdata₂ : (afterNextPC (afterPrelude σ) (0x800082d0#64)).regs.get? Register.x20 = some vdata := by
    rw [get?_afterNextPC σ (0x800082d0#64) _ (by decide) (by decide)]; exact hdata
  exact stepObs_store σ i u (0x800082d0#64) vminstret (0x03413c23#32)
    (instruction.STORE (0x038#12, regidx.Regidx 0x14#5, regidx.Regidx 0x02#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x800082d0#64)).mem
      (vsp + sign_extend (m := 64) (0x038#12)).toNat (sdData_val vdata))
    (0x23#8) (0x3c#8) (0x41#8) (0x03#8)
    hG hpc hminstret w_03413c23_sn5 nr_03413c23_sn5
    (Vsa.Sim.DecodeTable.decode_03413c23 (afterPrelude σ) (misa_pre5 σ hG) (priv_pre5 σ hG) (sec_pre5 σ hG))
    (exec_sd_val σ (0x800082d0#64) (0x038#12) (regidx.Regidx 0x14#5) (regidx.Regidx 0x02#5)
      vsp vdata hG (rX_bits_x2 _ vsp hx2₂) (rX_bits_x20 _ vdata hdata₂)
      halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x800082d4 — `sd s0,120(sp)` (spill) -/
theorem site_800082d4_sn5
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp vdata : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hdata : σ.regs.get? Register.x8 = some vdata)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x800082d4#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x078#12)).toNat)
    (hahiram : (vsp + sign_extend (m := 64) (0x078#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (vsp + sign_extend (m := 64) (0x078#12)).toNat)
    (haalign : (vsp + sign_extend (m := 64) (0x078#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x800082d4#64)).mem
        (vsp + sign_extend (m := 64) (0x078#12)).toNat (sdData_val vdata) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x800082d4#64)).mem
            (vsp + sign_extend (m := 64) (0x078#12)).toNat (sdData_val vdata))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800082d4 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x800082d4#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x800082d4#64) _ (by decide) (by decide)]; exact hx2
  have hdata₂ : (afterNextPC (afterPrelude σ) (0x800082d4#64)).regs.get? Register.x8 = some vdata := by
    rw [get?_afterNextPC σ (0x800082d4#64) _ (by decide) (by decide)]; exact hdata
  exact stepObs_store σ i u (0x800082d4#64) vminstret (0x06813c23#32)
    (instruction.STORE (0x078#12, regidx.Regidx 0x08#5, regidx.Regidx 0x02#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x800082d4#64)).mem
      (vsp + sign_extend (m := 64) (0x078#12)).toNat (sdData_val vdata))
    (0x23#8) (0x3c#8) (0x81#8) (0x06#8)
    hG hpc hminstret w_06813c23_sn5 nr_06813c23_sn5
    (Vsa.Sim.DecodeTable.decode_06813c23 (afterPrelude σ) (misa_pre5 σ hG) (priv_pre5 σ hG) (sec_pre5 σ hG))
    (exec_sd_val σ (0x800082d4#64) (0x078#12) (regidx.Regidx 0x08#5) (regidx.Regidx 0x02#5)
      vsp vdata hG (rX_bits_x2 _ vsp hx2₂) (rX_bits_x8 _ vdata hdata₂)
      halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x800082d8 — `ld s4,104(sp)` (reload; value irrelevant downstream) -/
theorem site_800082d8_sn5
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x800082d8#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x068#12)).toNat)
    (hhiram : (vsp + sign_extend (m := 64) (0x068#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vsp + sign_extend (m := 64) (0x068#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vsp + sign_extend (m := 64) (0x068#12)).toNat)
    (halign : (vsp + sign_extend (m := 64) (0x068#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x20
          (sign_extend (m := 64)
            (ldBytesT (afterNextPC (afterPrelude σ) (0x800082d8#64)) (vsp + sign_extend (m := 64) (0x068#12))))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800082d8 hmem
  exact stepObs_alu σ i u (0x800082d8#64) vminstret (0x06813a03#32)
    (instruction.LOAD (0x068#12, regidx.Regidx 0x02#5, regidx.Regidx 0x14#5, false, 8))
    Register.x20
    (sign_extend (m := 64)
      (ldBytesT (afterNextPC (afterPrelude σ) (0x800082d8#64)) (vsp + sign_extend (m := 64) (0x068#12))))
    (0x03#8) (0x3a#8) (0x81#8) (0x06#8)
    hG hpc hminstret w_06813a03_sn5 nr_06813a03_sn5
    (Vsa.Sim.DecodeTable.decode_06813a03 (afterPrelude σ) (misa_pre5 σ hG) (priv_pre5 σ hG) (sec_pre5 σ hG))
    (exec_ld_total σ (0x800082d8#64) (0x068#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x14#5) vsp _ hG
      (rX_bits_x2 _ vsp
        (by rw [get?_afterNextPC σ (0x800082d8#64) _ (by decide) (by decide)]; exact hx2))
      (wX_bits_x20 _ (sign_extend (m := 64)
        (ldBytesT (afterNextPC (afterPrelude σ) (0x800082d8#64)) (vsp + sign_extend (m := 64) (0x068#12)))))
      hlo hhiram hhtif halign)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x800082dc — `mv s9,s6` (write cursor := top) -/
theorem site_800082dc_sn5
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v22 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx22 : σ.regs.get? Register.x22 = some v22)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x800082dc#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x25 (v22 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800082dc hmem
  have hx22₂ : (afterNextPC (afterPrelude σ) (0x800082dc#64)).regs.get? Register.x22 = some v22 := by
    rw [get?_afterNextPC σ (0x800082dc#64) _ (by decide) (by decide)]; exact hx22
  exact stepObs_alu σ i u (0x800082dc#64) vminstret (0x000b0c93#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x16#5, regidx.Regidx 0x19#5, iop.ADDI))
    Register.x25 (v22 + sign_extend (m := 64) (0x000#12)) (0x93#8) (0x0c#8) (0x0b#8) (0x00#8)
    hG hpc hminstret w_000b0c93_sn5 nr_000b0c93_sn5
    (Vsa.Sim.DecodeTable.decode_000b0c93 (afterPrelude σ) (misa_pre5 σ hG) (priv_pre5 σ hG) (sec_pre5 σ hG))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x16#5) (regidx.Regidx 0x19#5) v22
      (afterNextPC (afterPrelude σ) (0x800082dc#64))
      (sigma3_alu σ (0x800082dc#64) Register.x25 (v22 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x22 _ v22 hx22₂) (wX_bits_x25 _ (v22 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x800082e0 — `sd t3,32(sp)` (spill) -/
theorem site_800082e0_sn5
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp vdata : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hdata : σ.regs.get? Register.x28 = some vdata)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x800082e0#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x020#12)).toNat)
    (hahiram : (vsp + sign_extend (m := 64) (0x020#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (vsp + sign_extend (m := 64) (0x020#12)).toNat)
    (haalign : (vsp + sign_extend (m := 64) (0x020#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x800082e0#64)).mem
        (vsp + sign_extend (m := 64) (0x020#12)).toNat (sdData_val vdata) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x800082e0#64)).mem
            (vsp + sign_extend (m := 64) (0x020#12)).toNat (sdData_val vdata))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800082e0 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x800082e0#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x800082e0#64) _ (by decide) (by decide)]; exact hx2
  have hdata₂ : (afterNextPC (afterPrelude σ) (0x800082e0#64)).regs.get? Register.x28 = some vdata := by
    rw [get?_afterNextPC σ (0x800082e0#64) _ (by decide) (by decide)]; exact hdata
  exact stepObs_store σ i u (0x800082e0#64) vminstret (0x03c13023#32)
    (instruction.STORE (0x020#12, regidx.Regidx 0x1c#5, regidx.Regidx 0x02#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x800082e0#64)).mem
      (vsp + sign_extend (m := 64) (0x020#12)).toNat (sdData_val vdata))
    (0x23#8) (0x30#8) (0xc1#8) (0x03#8)
    hG hpc hminstret w_03c13023_sn5 nr_03c13023_sn5
    (Vsa.Sim.DecodeTable.decode_03c13023 (afterPrelude σ) (misa_pre5 σ hG) (priv_pre5 σ hG) (sec_pre5 σ hG))
    (exec_sd_val σ (0x800082e0#64) (0x020#12) (regidx.Regidx 0x1c#5) (regidx.Regidx 0x02#5)
      vsp vdata hG (rX_bits_x2 _ vsp hx2₂) (rX_bits_x28 _ vdata hdata₂)
      halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x800082e4 — `sd t1,40(sp)` (spill) -/
theorem site_800082e4_sn5
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp vdata : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hdata : σ.regs.get? Register.x6 = some vdata)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x800082e4#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x028#12)).toNat)
    (hahiram : (vsp + sign_extend (m := 64) (0x028#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (vsp + sign_extend (m := 64) (0x028#12)).toNat)
    (haalign : (vsp + sign_extend (m := 64) (0x028#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x800082e4#64)).mem
        (vsp + sign_extend (m := 64) (0x028#12)).toNat (sdData_val vdata) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x800082e4#64)).mem
            (vsp + sign_extend (m := 64) (0x028#12)).toNat (sdData_val vdata))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800082e4 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x800082e4#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x800082e4#64) _ (by decide) (by decide)]; exact hx2
  have hdata₂ : (afterNextPC (afterPrelude σ) (0x800082e4#64)).regs.get? Register.x6 = some vdata := by
    rw [get?_afterNextPC σ (0x800082e4#64) _ (by decide) (by decide)]; exact hdata
  exact stepObs_store σ i u (0x800082e4#64) vminstret (0x02613423#32)
    (instruction.STORE (0x028#12, regidx.Regidx 0x06#5, regidx.Regidx 0x02#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x800082e4#64)).mem
      (vsp + sign_extend (m := 64) (0x028#12)).toNat (sdData_val vdata))
    (0x23#8) (0x34#8) (0x61#8) (0x02#8)
    hG hpc hminstret w_02613423_sn5 nr_02613423_sn5
    (Vsa.Sim.DecodeTable.decode_02613423 (afterPrelude σ) (misa_pre5 σ hG) (priv_pre5 σ hG) (sec_pre5 σ hG))
    (exec_sd_val σ (0x800082e4#64) (0x028#12) (regidx.Regidx 0x06#5) (regidx.Regidx 0x02#5)
      vsp vdata hG (rX_bits_x2 _ vsp hx2₂) (rX_bits_x6 _ vdata hdata₂)
      halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x800082e8 — `li s7,0` (digit count := 0) -/
theorem site_800082e8_sn5
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x800082e8#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x23 ((0#64) + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800082e8 hmem
  exact stepObs_alu σ i u (0x800082e8#64) vminstret (0x00000b93#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x00#5, regidx.Regidx 0x17#5, iop.ADDI))
    Register.x23 ((0#64) + sign_extend (m := 64) (0x000#12)) (0x93#8) (0x0b#8) (0x00#8) (0x00#8)
    hG hpc hminstret w_00000b93_sn5 nr_00000b93_sn5
    (Vsa.Sim.DecodeTable.decode_00000b93 (afterPrelude σ) (misa_pre5 σ hG) (priv_pre5 σ hG) (sec_pre5 σ hG))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x17#5) (0#64)
      (afterNextPC (afterPrelude σ) (0x800082e8#64))
      (sigma3_alu σ (0x800082e8#64) Register.x23 ((0#64) + sign_extend (m := 64) (0x000#12)))
      (rX_bits_zero _) (wX_bits_x23 _ ((0#64) + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x800082ec — `andi s11,t1,1024` (grouping flag; 0 for `%lld`) -/
theorem site_800082ec_sn5
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v6 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx6 : σ.regs.get? Register.x6 = some v6)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x800082ec#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x27 (v6 &&& sign_extend (m := 64) (0x400#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800082ec hmem
  have hx6₂ : (afterNextPC (afterPrelude σ) (0x800082ec#64)).regs.get? Register.x6 = some v6 := by
    rw [get?_afterNextPC σ (0x800082ec#64) _ (by decide) (by decide)]; exact hx6
  exact stepObs_alu σ i u (0x800082ec#64) vminstret (0x40037d93#32)
    (instruction.ITYPE (0x400#12, regidx.Regidx 0x06#5, regidx.Regidx 0x1b#5, iop.ANDI))
    Register.x27 (v6 &&& sign_extend (m := 64) (0x400#12)) (0x93#8) (0x7d#8) (0x03#8) (0x40#8)
    hG hpc hminstret w_40037d93_sn5 nr_40037d93_sn5
    (Vsa.Sim.DecodeTable.decode_40037d93 (afterPrelude σ) (misa_pre5 σ hG) (priv_pre5 σ hG) (sec_pre5 σ hG))
    (execute_itype_andi_char (0x400#12) (regidx.Regidx 0x06#5) (regidx.Regidx 0x1b#5) v6
      (afterNextPC (afterPrelude σ) (0x800082ec#64))
      (sigma3_alu σ (0x800082ec#64) Register.x27 (v6 &&& sign_extend (m := 64) (0x400#12)))
      (rX_bits_x6 _ v6 hx6₂) (wX_bits_x27 _ (v6 &&& sign_extend (m := 64) (0x400#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x800082f0 — `sd s6,112(sp)` (spill) -/
theorem site_800082f0_sn5
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp vdata : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hdata : σ.regs.get? Register.x22 = some vdata)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x800082f0#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x070#12)).toNat)
    (hahiram : (vsp + sign_extend (m := 64) (0x070#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (vsp + sign_extend (m := 64) (0x070#12)).toNat)
    (haalign : (vsp + sign_extend (m := 64) (0x070#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x800082f0#64)).mem
        (vsp + sign_extend (m := 64) (0x070#12)).toNat (sdData_val vdata) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x800082f0#64)).mem
            (vsp + sign_extend (m := 64) (0x070#12)).toNat (sdData_val vdata))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800082f0 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x800082f0#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x800082f0#64) _ (by decide) (by decide)]; exact hx2
  have hdata₂ : (afterNextPC (afterPrelude σ) (0x800082f0#64)).regs.get? Register.x22 = some vdata := by
    rw [get?_afterNextPC σ (0x800082f0#64) _ (by decide) (by decide)]; exact hdata
  exact stepObs_store σ i u (0x800082f0#64) vminstret (0x07613823#32)
    (instruction.STORE (0x070#12, regidx.Regidx 0x16#5, regidx.Regidx 0x02#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x800082f0#64)).mem
      (vsp + sign_extend (m := 64) (0x070#12)).toNat (sdData_val vdata))
    (0x23#8) (0x38#8) (0x61#8) (0x07#8)
    hG hpc hminstret w_07613823_sn5 nr_07613823_sn5
    (Vsa.Sim.DecodeTable.decode_07613823 (afterPrelude σ) (misa_pre5 σ hG) (priv_pre5 σ hG) (sec_pre5 σ hG))
    (exec_sd_val σ (0x800082f0#64) (0x070#12) (regidx.Regidx 0x16#5) (regidx.Regidx 0x02#5)
      vsp vdata hG (rX_bits_x2 _ vsp hx2₂) (rX_bits_x22 _ vdata hdata₂)
      halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x800082f4 — `mv s0,a4` (running value := magnitude) -/
theorem site_800082f4_sn5
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x800082f4#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x8 (v14 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800082f4 hmem
  have hx14₂ : (afterNextPC (afterPrelude σ) (0x800082f4#64)).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ (0x800082f4#64) _ (by decide) (by decide)]; exact hx14
  exact stepObs_alu σ i u (0x800082f4#64) vminstret (0x00070413#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x08#5, iop.ADDI))
    Register.x8 (v14 + sign_extend (m := 64) (0x000#12)) (0x13#8) (0x04#8) (0x07#8) (0x00#8)
    hG hpc hminstret w_00070413_sn5 nr_00070413_sn5
    (Vsa.Sim.DecodeTable.decode_00070413 (afterPrelude σ) (misa_pre5 σ hG) (priv_pre5 σ hG) (sec_pre5 σ hG))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x08#5) v14
      (afterNextPC (afterPrelude σ) (0x800082f4#64))
      (sigma3_alu σ (0x800082f4#64) Register.x8 (v14 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x14 _ v14 hx14₂) (wX_bits_x8 _ (v14 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x800082f8 — `j 0x8000831c` (enter the do-while at the mod-emit step) -/
theorem site_800082f8_sn5
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x800082f8#64 : BitVec 64))
    (htgt : (pc + sign_extend (m := 64) (0x000024#21)).toNat % 4 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vminstret (pc + sign_extend (m := 64) (0x000024#21))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800082f8 hmem
  exact stepObs_j σ i u (0x800082f8#64) vminstret (0x0240006f#32) (0x000024#21)
    (0x6f#8) (0x00#8) (0x40#8) (0x02#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) (by decide) w_0240006f_sn5
    (Vsa.Sim.DecodeTable.decode_0240006f (afterPrelude σ) (misa_pre5 σ hG) (priv_pre5 σ hG) (sec_pre5 σ hG))
    htgt hi

end Vsa.Sim
