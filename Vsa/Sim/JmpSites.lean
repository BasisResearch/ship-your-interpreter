import Vsa.Sim.ValueSites
import Vsa.Sim.DivSites
import Vsa.Sim.Code.Setjmp
import Vsa.Sim.Code.Longjmp

/-!
# Layer 3 — per-site observational step lemmas for `setjmp` / `longjmp`

One `StepObs` lemma per instruction of newlib RV64 soft-float `setjmp`
(`0x80006ffc`, 16 insts: 14 `sd` + `li a0,0` + `ret`) and `longjmp`
(`0x8000703c`, 17 insts: 14 `ld` + `seqz`/`add` + `ret`).

Stores use `exec_sd_val` (width-8 `sd`, base = `a0`, offset = the slot). Loads
are **ALU-class** sites (`sign_extend` of the dword → `sigmaPost_alu`), via
`exec_ld` from `ValueSites`. `seqz a0,a1` is `SLTIU a0,a1,1`; `add a0,a0,a1` is
`RTYPE ADD`. Everything reuses the `stepObs_*` wrappers, `decode_*` table,
`writeMap8`/`sdData_val`.  Byte-word facts get an `_jmp` suffix (collision sweep).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Byte-word / non-RVC facts -/

theorem w_00153023_jmp : ((((0x00#8).append (0x15#8)).append (0x30#8)).append (0x23#8)) = (0x00153023#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00153023_jmp : Sail.BitVec.extractLsb ((((0x00#8).append (0x15#8)).append (0x30#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_00853423_jmp : ((((0x00#8).append (0x85#8)).append (0x34#8)).append (0x23#8)) = (0x00853423#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00853423_jmp : Sail.BitVec.extractLsb ((((0x00#8).append (0x85#8)).append (0x34#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_00953823_jmp : ((((0x00#8).append (0x95#8)).append (0x38#8)).append (0x23#8)) = (0x00953823#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00953823_jmp : Sail.BitVec.extractLsb ((((0x00#8).append (0x95#8)).append (0x38#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_01253c23_jmp : ((((0x01#8).append (0x25#8)).append (0x3c#8)).append (0x23#8)) = (0x01253c23#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_01253c23_jmp : Sail.BitVec.extractLsb ((((0x01#8).append (0x25#8)).append (0x3c#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_03353023_jmp : ((((0x03#8).append (0x35#8)).append (0x30#8)).append (0x23#8)) = (0x03353023#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_03353023_jmp : Sail.BitVec.extractLsb ((((0x03#8).append (0x35#8)).append (0x30#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_03453423_jmp : ((((0x03#8).append (0x45#8)).append (0x34#8)).append (0x23#8)) = (0x03453423#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_03453423_jmp : Sail.BitVec.extractLsb ((((0x03#8).append (0x45#8)).append (0x34#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_03553823_jmp : ((((0x03#8).append (0x55#8)).append (0x38#8)).append (0x23#8)) = (0x03553823#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_03553823_jmp : Sail.BitVec.extractLsb ((((0x03#8).append (0x55#8)).append (0x38#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_03653c23_jmp : ((((0x03#8).append (0x65#8)).append (0x3c#8)).append (0x23#8)) = (0x03653c23#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_03653c23_jmp : Sail.BitVec.extractLsb ((((0x03#8).append (0x65#8)).append (0x3c#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_05753023_jmp : ((((0x05#8).append (0x75#8)).append (0x30#8)).append (0x23#8)) = (0x05753023#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_05753023_jmp : Sail.BitVec.extractLsb ((((0x05#8).append (0x75#8)).append (0x30#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_05853423_jmp : ((((0x05#8).append (0x85#8)).append (0x34#8)).append (0x23#8)) = (0x05853423#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_05853423_jmp : Sail.BitVec.extractLsb ((((0x05#8).append (0x85#8)).append (0x34#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_05953823_jmp : ((((0x05#8).append (0x95#8)).append (0x38#8)).append (0x23#8)) = (0x05953823#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_05953823_jmp : Sail.BitVec.extractLsb ((((0x05#8).append (0x95#8)).append (0x38#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_05a53c23_jmp : ((((0x05#8).append (0xa5#8)).append (0x3c#8)).append (0x23#8)) = (0x05a53c23#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_05a53c23_jmp : Sail.BitVec.extractLsb ((((0x05#8).append (0xa5#8)).append (0x3c#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_07b53023_jmp : ((((0x07#8).append (0xb5#8)).append (0x30#8)).append (0x23#8)) = (0x07b53023#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_07b53023_jmp : Sail.BitVec.extractLsb ((((0x07#8).append (0xb5#8)).append (0x30#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_06253423_jmp : ((((0x06#8).append (0x25#8)).append (0x34#8)).append (0x23#8)) = (0x06253423#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_06253423_jmp : Sail.BitVec.extractLsb ((((0x06#8).append (0x25#8)).append (0x34#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_00000513_jmp : ((((0x00#8).append (0x00#8)).append (0x05#8)).append (0x13#8)) = (0x00000513#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00000513_jmp : Sail.BitVec.extractLsb ((((0x00#8).append (0x00#8)).append (0x05#8)).append (0x13#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_00008067_jmp : ((((0x00#8).append (0x00#8)).append (0x80#8)).append (0x67#8)) = (0x00008067#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00008067_jmp : Sail.BitVec.extractLsb ((((0x00#8).append (0x00#8)).append (0x80#8)).append (0x67#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_00053083_jmp : ((((0x00#8).append (0x05#8)).append (0x30#8)).append (0x83#8)) = (0x00053083#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00053083_jmp : Sail.BitVec.extractLsb ((((0x00#8).append (0x05#8)).append (0x30#8)).append (0x83#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_00853403_jmp : ((((0x00#8).append (0x85#8)).append (0x34#8)).append (0x03#8)) = (0x00853403#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00853403_jmp : Sail.BitVec.extractLsb ((((0x00#8).append (0x85#8)).append (0x34#8)).append (0x03#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_01053483_jmp : ((((0x01#8).append (0x05#8)).append (0x34#8)).append (0x83#8)) = (0x01053483#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_01053483_jmp : Sail.BitVec.extractLsb ((((0x01#8).append (0x05#8)).append (0x34#8)).append (0x83#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_01853903_jmp : ((((0x01#8).append (0x85#8)).append (0x39#8)).append (0x03#8)) = (0x01853903#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_01853903_jmp : Sail.BitVec.extractLsb ((((0x01#8).append (0x85#8)).append (0x39#8)).append (0x03#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_02053983_jmp : ((((0x02#8).append (0x05#8)).append (0x39#8)).append (0x83#8)) = (0x02053983#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_02053983_jmp : Sail.BitVec.extractLsb ((((0x02#8).append (0x05#8)).append (0x39#8)).append (0x83#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_02853a03_jmp : ((((0x02#8).append (0x85#8)).append (0x3a#8)).append (0x03#8)) = (0x02853a03#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_02853a03_jmp : Sail.BitVec.extractLsb ((((0x02#8).append (0x85#8)).append (0x3a#8)).append (0x03#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_03053a83_jmp : ((((0x03#8).append (0x05#8)).append (0x3a#8)).append (0x83#8)) = (0x03053a83#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_03053a83_jmp : Sail.BitVec.extractLsb ((((0x03#8).append (0x05#8)).append (0x3a#8)).append (0x83#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_03853b03_jmp : ((((0x03#8).append (0x85#8)).append (0x3b#8)).append (0x03#8)) = (0x03853b03#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_03853b03_jmp : Sail.BitVec.extractLsb ((((0x03#8).append (0x85#8)).append (0x3b#8)).append (0x03#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_04053b83_jmp : ((((0x04#8).append (0x05#8)).append (0x3b#8)).append (0x83#8)) = (0x04053b83#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_04053b83_jmp : Sail.BitVec.extractLsb ((((0x04#8).append (0x05#8)).append (0x3b#8)).append (0x83#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_04853c03_jmp : ((((0x04#8).append (0x85#8)).append (0x3c#8)).append (0x03#8)) = (0x04853c03#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_04853c03_jmp : Sail.BitVec.extractLsb ((((0x04#8).append (0x85#8)).append (0x3c#8)).append (0x03#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_05053c83_jmp : ((((0x05#8).append (0x05#8)).append (0x3c#8)).append (0x83#8)) = (0x05053c83#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_05053c83_jmp : Sail.BitVec.extractLsb ((((0x05#8).append (0x05#8)).append (0x3c#8)).append (0x83#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_05853d03_jmp : ((((0x05#8).append (0x85#8)).append (0x3d#8)).append (0x03#8)) = (0x05853d03#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_05853d03_jmp : Sail.BitVec.extractLsb ((((0x05#8).append (0x85#8)).append (0x3d#8)).append (0x03#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_06053d83_jmp : ((((0x06#8).append (0x05#8)).append (0x3d#8)).append (0x83#8)) = (0x06053d83#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_06053d83_jmp : Sail.BitVec.extractLsb ((((0x06#8).append (0x05#8)).append (0x3d#8)).append (0x83#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_06853103_jmp : ((((0x06#8).append (0x85#8)).append (0x31#8)).append (0x03#8)) = (0x06853103#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_06853103_jmp : Sail.BitVec.extractLsb ((((0x06#8).append (0x85#8)).append (0x31#8)).append (0x03#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_0015b513_jmp : ((((0x00#8).append (0x15#8)).append (0xb5#8)).append (0x13#8)) = (0x0015b513#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_0015b513_jmp : Sail.BitVec.extractLsb ((((0x00#8).append (0x15#8)).append (0xb5#8)).append (0x13#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_00b50533_jmp : ((((0x00#8).append (0xb5#8)).append (0x05#8)).append (0x33#8)) = (0x00b50533#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00b50533_jmp : Sail.BitVec.extractLsb ((((0x00#8).append (0xb5#8)).append (0x05#8)).append (0x33#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-! ## setjmp: the 14 `sd rX, off(a0)` sites (base = a0 = x10) -/

/-- **setjmp store @ 0x80006ffc** (`sd x1,0(a0)`): write `x1` (8 bytes) at `a0 + 0x000`. -/
theorem site_80006ffc_jmp
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 vd : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hxd : σ.regs.get? Register.x1 = some vd)
    (hmem : SetjmpLoaded σ.mem)
    (hpcv : pc = (0x80006ffc#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v10 + sign_extend (m := 64) (0x000#12)).toNat)
    (hahiram : (v10 + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (v10 + sign_extend (m := 64) (0x000#12)).toNat)
    (haalign : (v10 + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x80006ffc#64)).mem
        (v10 + sign_extend (m := 64) (0x000#12)).toNat (sdData_val vd) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x80006ffc#64)).mem
            (v10 + sign_extend (m := 64) (0x000#12)).toNat (sdData_val vd))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := setjmp_at_80006ffc hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80006ffc#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x80006ffc#64) _ (by decide) (by decide)]; exact hx10
  have hxd₂ : (afterNextPC (afterPrelude σ) (0x80006ffc#64)).regs.get? Register.x1 = some vd := by
    rw [get?_afterNextPC σ (0x80006ffc#64) _ (by decide) (by decide)]; exact hxd
  exact stepObs_store σ i u (0x80006ffc#64) vminstret (0x00153023#32)
    (instruction.STORE (0x000#12, regidx.Regidx 0x01#5, regidx.Regidx 0x0a#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80006ffc#64)).mem
      (v10 + sign_extend (m := 64) (0x000#12)).toNat (sdData_val vd))
    (0x23#8) (0x30#8) (0x15#8) (0x00#8)
    hG hpc hminstret w_00153023_jmp nr_00153023_jmp
    (Vsa.Sim.DecodeTable.decode_00153023 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80006ffc#64) (0x000#12) (regidx.Regidx 0x01#5) (regidx.Regidx 0x0a#5)
      v10 vd hG (rX_bits_x10 _ v10 hx10₂) (rX_bits_x1 _ vd hxd₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **setjmp store @ 0x80007000** (`sd x8,8(a0)`): write `x8` (8 bytes) at `a0 + 0x008`. -/
theorem site_80007000_jmp
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 vd : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hxd : σ.regs.get? Register.x8 = some vd)
    (hmem : SetjmpLoaded σ.mem)
    (hpcv : pc = (0x80007000#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v10 + sign_extend (m := 64) (0x008#12)).toNat)
    (hahiram : (v10 + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (v10 + sign_extend (m := 64) (0x008#12)).toNat)
    (haalign : (v10 + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x80007000#64)).mem
        (v10 + sign_extend (m := 64) (0x008#12)).toNat (sdData_val vd) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x80007000#64)).mem
            (v10 + sign_extend (m := 64) (0x008#12)).toNat (sdData_val vd))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := setjmp_at_80007000 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80007000#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x80007000#64) _ (by decide) (by decide)]; exact hx10
  have hxd₂ : (afterNextPC (afterPrelude σ) (0x80007000#64)).regs.get? Register.x8 = some vd := by
    rw [get?_afterNextPC σ (0x80007000#64) _ (by decide) (by decide)]; exact hxd
  exact stepObs_store σ i u (0x80007000#64) vminstret (0x00853423#32)
    (instruction.STORE (0x008#12, regidx.Regidx 0x08#5, regidx.Regidx 0x0a#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80007000#64)).mem
      (v10 + sign_extend (m := 64) (0x008#12)).toNat (sdData_val vd))
    (0x23#8) (0x34#8) (0x85#8) (0x00#8)
    hG hpc hminstret w_00853423_jmp nr_00853423_jmp
    (Vsa.Sim.DecodeTable.decode_00853423 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80007000#64) (0x008#12) (regidx.Regidx 0x08#5) (regidx.Regidx 0x0a#5)
      v10 vd hG (rX_bits_x10 _ v10 hx10₂) (rX_bits_x8 _ vd hxd₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **setjmp store @ 0x80007004** (`sd x9,16(a0)`): write `x9` (8 bytes) at `a0 + 0x010`. -/
theorem site_80007004_jmp
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 vd : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hxd : σ.regs.get? Register.x9 = some vd)
    (hmem : SetjmpLoaded σ.mem)
    (hpcv : pc = (0x80007004#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v10 + sign_extend (m := 64) (0x010#12)).toNat)
    (hahiram : (v10 + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (v10 + sign_extend (m := 64) (0x010#12)).toNat)
    (haalign : (v10 + sign_extend (m := 64) (0x010#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x80007004#64)).mem
        (v10 + sign_extend (m := 64) (0x010#12)).toNat (sdData_val vd) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x80007004#64)).mem
            (v10 + sign_extend (m := 64) (0x010#12)).toNat (sdData_val vd))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := setjmp_at_80007004 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80007004#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x80007004#64) _ (by decide) (by decide)]; exact hx10
  have hxd₂ : (afterNextPC (afterPrelude σ) (0x80007004#64)).regs.get? Register.x9 = some vd := by
    rw [get?_afterNextPC σ (0x80007004#64) _ (by decide) (by decide)]; exact hxd
  exact stepObs_store σ i u (0x80007004#64) vminstret (0x00953823#32)
    (instruction.STORE (0x010#12, regidx.Regidx 0x09#5, regidx.Regidx 0x0a#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80007004#64)).mem
      (v10 + sign_extend (m := 64) (0x010#12)).toNat (sdData_val vd))
    (0x23#8) (0x38#8) (0x95#8) (0x00#8)
    hG hpc hminstret w_00953823_jmp nr_00953823_jmp
    (Vsa.Sim.DecodeTable.decode_00953823 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80007004#64) (0x010#12) (regidx.Regidx 0x09#5) (regidx.Regidx 0x0a#5)
      v10 vd hG (rX_bits_x10 _ v10 hx10₂) (rX_bits_x9 _ vd hxd₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **setjmp store @ 0x80007008** (`sd x18,24(a0)`): write `x18` (8 bytes) at `a0 + 0x018`. -/
theorem site_80007008_jmp
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 vd : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hxd : σ.regs.get? Register.x18 = some vd)
    (hmem : SetjmpLoaded σ.mem)
    (hpcv : pc = (0x80007008#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v10 + sign_extend (m := 64) (0x018#12)).toNat)
    (hahiram : (v10 + sign_extend (m := 64) (0x018#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (v10 + sign_extend (m := 64) (0x018#12)).toNat)
    (haalign : (v10 + sign_extend (m := 64) (0x018#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x80007008#64)).mem
        (v10 + sign_extend (m := 64) (0x018#12)).toNat (sdData_val vd) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x80007008#64)).mem
            (v10 + sign_extend (m := 64) (0x018#12)).toNat (sdData_val vd))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := setjmp_at_80007008 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80007008#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x80007008#64) _ (by decide) (by decide)]; exact hx10
  have hxd₂ : (afterNextPC (afterPrelude σ) (0x80007008#64)).regs.get? Register.x18 = some vd := by
    rw [get?_afterNextPC σ (0x80007008#64) _ (by decide) (by decide)]; exact hxd
  exact stepObs_store σ i u (0x80007008#64) vminstret (0x01253c23#32)
    (instruction.STORE (0x018#12, regidx.Regidx 0x12#5, regidx.Regidx 0x0a#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80007008#64)).mem
      (v10 + sign_extend (m := 64) (0x018#12)).toNat (sdData_val vd))
    (0x23#8) (0x3c#8) (0x25#8) (0x01#8)
    hG hpc hminstret w_01253c23_jmp nr_01253c23_jmp
    (Vsa.Sim.DecodeTable.decode_01253c23 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80007008#64) (0x018#12) (regidx.Regidx 0x12#5) (regidx.Regidx 0x0a#5)
      v10 vd hG (rX_bits_x10 _ v10 hx10₂) (rX_bits_x18 _ vd hxd₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **setjmp store @ 0x8000700c** (`sd x19,32(a0)`): write `x19` (8 bytes) at `a0 + 0x020`. -/
theorem site_8000700c_jmp
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 vd : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hxd : σ.regs.get? Register.x19 = some vd)
    (hmem : SetjmpLoaded σ.mem)
    (hpcv : pc = (0x8000700c#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v10 + sign_extend (m := 64) (0x020#12)).toNat)
    (hahiram : (v10 + sign_extend (m := 64) (0x020#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (v10 + sign_extend (m := 64) (0x020#12)).toNat)
    (haalign : (v10 + sign_extend (m := 64) (0x020#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x8000700c#64)).mem
        (v10 + sign_extend (m := 64) (0x020#12)).toNat (sdData_val vd) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x8000700c#64)).mem
            (v10 + sign_extend (m := 64) (0x020#12)).toNat (sdData_val vd))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := setjmp_at_8000700c hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x8000700c#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x8000700c#64) _ (by decide) (by decide)]; exact hx10
  have hxd₂ : (afterNextPC (afterPrelude σ) (0x8000700c#64)).regs.get? Register.x19 = some vd := by
    rw [get?_afterNextPC σ (0x8000700c#64) _ (by decide) (by decide)]; exact hxd
  exact stepObs_store σ i u (0x8000700c#64) vminstret (0x03353023#32)
    (instruction.STORE (0x020#12, regidx.Regidx 0x13#5, regidx.Regidx 0x0a#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x8000700c#64)).mem
      (v10 + sign_extend (m := 64) (0x020#12)).toNat (sdData_val vd))
    (0x23#8) (0x30#8) (0x35#8) (0x03#8)
    hG hpc hminstret w_03353023_jmp nr_03353023_jmp
    (Vsa.Sim.DecodeTable.decode_03353023 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x8000700c#64) (0x020#12) (regidx.Regidx 0x13#5) (regidx.Regidx 0x0a#5)
      v10 vd hG (rX_bits_x10 _ v10 hx10₂) (rX_bits_x19 _ vd hxd₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **setjmp store @ 0x80007010** (`sd x20,40(a0)`): write `x20` (8 bytes) at `a0 + 0x028`. -/
theorem site_80007010_jmp
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 vd : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hxd : σ.regs.get? Register.x20 = some vd)
    (hmem : SetjmpLoaded σ.mem)
    (hpcv : pc = (0x80007010#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v10 + sign_extend (m := 64) (0x028#12)).toNat)
    (hahiram : (v10 + sign_extend (m := 64) (0x028#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (v10 + sign_extend (m := 64) (0x028#12)).toNat)
    (haalign : (v10 + sign_extend (m := 64) (0x028#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x80007010#64)).mem
        (v10 + sign_extend (m := 64) (0x028#12)).toNat (sdData_val vd) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x80007010#64)).mem
            (v10 + sign_extend (m := 64) (0x028#12)).toNat (sdData_val vd))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := setjmp_at_80007010 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80007010#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x80007010#64) _ (by decide) (by decide)]; exact hx10
  have hxd₂ : (afterNextPC (afterPrelude σ) (0x80007010#64)).regs.get? Register.x20 = some vd := by
    rw [get?_afterNextPC σ (0x80007010#64) _ (by decide) (by decide)]; exact hxd
  exact stepObs_store σ i u (0x80007010#64) vminstret (0x03453423#32)
    (instruction.STORE (0x028#12, regidx.Regidx 0x14#5, regidx.Regidx 0x0a#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80007010#64)).mem
      (v10 + sign_extend (m := 64) (0x028#12)).toNat (sdData_val vd))
    (0x23#8) (0x34#8) (0x45#8) (0x03#8)
    hG hpc hminstret w_03453423_jmp nr_03453423_jmp
    (Vsa.Sim.DecodeTable.decode_03453423 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80007010#64) (0x028#12) (regidx.Regidx 0x14#5) (regidx.Regidx 0x0a#5)
      v10 vd hG (rX_bits_x10 _ v10 hx10₂) (rX_bits_x20 _ vd hxd₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **setjmp store @ 0x80007014** (`sd x21,48(a0)`): write `x21` (8 bytes) at `a0 + 0x030`. -/
theorem site_80007014_jmp
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 vd : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hxd : σ.regs.get? Register.x21 = some vd)
    (hmem : SetjmpLoaded σ.mem)
    (hpcv : pc = (0x80007014#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v10 + sign_extend (m := 64) (0x030#12)).toNat)
    (hahiram : (v10 + sign_extend (m := 64) (0x030#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (v10 + sign_extend (m := 64) (0x030#12)).toNat)
    (haalign : (v10 + sign_extend (m := 64) (0x030#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x80007014#64)).mem
        (v10 + sign_extend (m := 64) (0x030#12)).toNat (sdData_val vd) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x80007014#64)).mem
            (v10 + sign_extend (m := 64) (0x030#12)).toNat (sdData_val vd))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := setjmp_at_80007014 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80007014#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x80007014#64) _ (by decide) (by decide)]; exact hx10
  have hxd₂ : (afterNextPC (afterPrelude σ) (0x80007014#64)).regs.get? Register.x21 = some vd := by
    rw [get?_afterNextPC σ (0x80007014#64) _ (by decide) (by decide)]; exact hxd
  exact stepObs_store σ i u (0x80007014#64) vminstret (0x03553823#32)
    (instruction.STORE (0x030#12, regidx.Regidx 0x15#5, regidx.Regidx 0x0a#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80007014#64)).mem
      (v10 + sign_extend (m := 64) (0x030#12)).toNat (sdData_val vd))
    (0x23#8) (0x38#8) (0x55#8) (0x03#8)
    hG hpc hminstret w_03553823_jmp nr_03553823_jmp
    (Vsa.Sim.DecodeTable.decode_03553823 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80007014#64) (0x030#12) (regidx.Regidx 0x15#5) (regidx.Regidx 0x0a#5)
      v10 vd hG (rX_bits_x10 _ v10 hx10₂) (rX_bits_x21 _ vd hxd₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **setjmp store @ 0x80007018** (`sd x22,56(a0)`): write `x22` (8 bytes) at `a0 + 0x038`. -/
theorem site_80007018_jmp
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 vd : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hxd : σ.regs.get? Register.x22 = some vd)
    (hmem : SetjmpLoaded σ.mem)
    (hpcv : pc = (0x80007018#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v10 + sign_extend (m := 64) (0x038#12)).toNat)
    (hahiram : (v10 + sign_extend (m := 64) (0x038#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (v10 + sign_extend (m := 64) (0x038#12)).toNat)
    (haalign : (v10 + sign_extend (m := 64) (0x038#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x80007018#64)).mem
        (v10 + sign_extend (m := 64) (0x038#12)).toNat (sdData_val vd) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x80007018#64)).mem
            (v10 + sign_extend (m := 64) (0x038#12)).toNat (sdData_val vd))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := setjmp_at_80007018 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80007018#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x80007018#64) _ (by decide) (by decide)]; exact hx10
  have hxd₂ : (afterNextPC (afterPrelude σ) (0x80007018#64)).regs.get? Register.x22 = some vd := by
    rw [get?_afterNextPC σ (0x80007018#64) _ (by decide) (by decide)]; exact hxd
  exact stepObs_store σ i u (0x80007018#64) vminstret (0x03653c23#32)
    (instruction.STORE (0x038#12, regidx.Regidx 0x16#5, regidx.Regidx 0x0a#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80007018#64)).mem
      (v10 + sign_extend (m := 64) (0x038#12)).toNat (sdData_val vd))
    (0x23#8) (0x3c#8) (0x65#8) (0x03#8)
    hG hpc hminstret w_03653c23_jmp nr_03653c23_jmp
    (Vsa.Sim.DecodeTable.decode_03653c23 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80007018#64) (0x038#12) (regidx.Regidx 0x16#5) (regidx.Regidx 0x0a#5)
      v10 vd hG (rX_bits_x10 _ v10 hx10₂) (rX_bits_x22 _ vd hxd₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **setjmp store @ 0x8000701c** (`sd x23,64(a0)`): write `x23` (8 bytes) at `a0 + 0x040`. -/
theorem site_8000701c_jmp
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 vd : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hxd : σ.regs.get? Register.x23 = some vd)
    (hmem : SetjmpLoaded σ.mem)
    (hpcv : pc = (0x8000701c#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v10 + sign_extend (m := 64) (0x040#12)).toNat)
    (hahiram : (v10 + sign_extend (m := 64) (0x040#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (v10 + sign_extend (m := 64) (0x040#12)).toNat)
    (haalign : (v10 + sign_extend (m := 64) (0x040#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x8000701c#64)).mem
        (v10 + sign_extend (m := 64) (0x040#12)).toNat (sdData_val vd) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x8000701c#64)).mem
            (v10 + sign_extend (m := 64) (0x040#12)).toNat (sdData_val vd))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := setjmp_at_8000701c hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x8000701c#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x8000701c#64) _ (by decide) (by decide)]; exact hx10
  have hxd₂ : (afterNextPC (afterPrelude σ) (0x8000701c#64)).regs.get? Register.x23 = some vd := by
    rw [get?_afterNextPC σ (0x8000701c#64) _ (by decide) (by decide)]; exact hxd
  exact stepObs_store σ i u (0x8000701c#64) vminstret (0x05753023#32)
    (instruction.STORE (0x040#12, regidx.Regidx 0x17#5, regidx.Regidx 0x0a#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x8000701c#64)).mem
      (v10 + sign_extend (m := 64) (0x040#12)).toNat (sdData_val vd))
    (0x23#8) (0x30#8) (0x75#8) (0x05#8)
    hG hpc hminstret w_05753023_jmp nr_05753023_jmp
    (Vsa.Sim.DecodeTable.decode_05753023 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x8000701c#64) (0x040#12) (regidx.Regidx 0x17#5) (regidx.Regidx 0x0a#5)
      v10 vd hG (rX_bits_x10 _ v10 hx10₂) (rX_bits_x23 _ vd hxd₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **setjmp store @ 0x80007020** (`sd x24,72(a0)`): write `x24` (8 bytes) at `a0 + 0x048`. -/
theorem site_80007020_jmp
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 vd : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hxd : σ.regs.get? Register.x24 = some vd)
    (hmem : SetjmpLoaded σ.mem)
    (hpcv : pc = (0x80007020#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v10 + sign_extend (m := 64) (0x048#12)).toNat)
    (hahiram : (v10 + sign_extend (m := 64) (0x048#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (v10 + sign_extend (m := 64) (0x048#12)).toNat)
    (haalign : (v10 + sign_extend (m := 64) (0x048#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x80007020#64)).mem
        (v10 + sign_extend (m := 64) (0x048#12)).toNat (sdData_val vd) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x80007020#64)).mem
            (v10 + sign_extend (m := 64) (0x048#12)).toNat (sdData_val vd))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := setjmp_at_80007020 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80007020#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x80007020#64) _ (by decide) (by decide)]; exact hx10
  have hxd₂ : (afterNextPC (afterPrelude σ) (0x80007020#64)).regs.get? Register.x24 = some vd := by
    rw [get?_afterNextPC σ (0x80007020#64) _ (by decide) (by decide)]; exact hxd
  exact stepObs_store σ i u (0x80007020#64) vminstret (0x05853423#32)
    (instruction.STORE (0x048#12, regidx.Regidx 0x18#5, regidx.Regidx 0x0a#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80007020#64)).mem
      (v10 + sign_extend (m := 64) (0x048#12)).toNat (sdData_val vd))
    (0x23#8) (0x34#8) (0x85#8) (0x05#8)
    hG hpc hminstret w_05853423_jmp nr_05853423_jmp
    (Vsa.Sim.DecodeTable.decode_05853423 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80007020#64) (0x048#12) (regidx.Regidx 0x18#5) (regidx.Regidx 0x0a#5)
      v10 vd hG (rX_bits_x10 _ v10 hx10₂) (rX_bits_x24 _ vd hxd₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **setjmp store @ 0x80007024** (`sd x25,80(a0)`): write `x25` (8 bytes) at `a0 + 0x050`. -/
theorem site_80007024_jmp
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 vd : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hxd : σ.regs.get? Register.x25 = some vd)
    (hmem : SetjmpLoaded σ.mem)
    (hpcv : pc = (0x80007024#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v10 + sign_extend (m := 64) (0x050#12)).toNat)
    (hahiram : (v10 + sign_extend (m := 64) (0x050#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (v10 + sign_extend (m := 64) (0x050#12)).toNat)
    (haalign : (v10 + sign_extend (m := 64) (0x050#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x80007024#64)).mem
        (v10 + sign_extend (m := 64) (0x050#12)).toNat (sdData_val vd) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x80007024#64)).mem
            (v10 + sign_extend (m := 64) (0x050#12)).toNat (sdData_val vd))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := setjmp_at_80007024 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80007024#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x80007024#64) _ (by decide) (by decide)]; exact hx10
  have hxd₂ : (afterNextPC (afterPrelude σ) (0x80007024#64)).regs.get? Register.x25 = some vd := by
    rw [get?_afterNextPC σ (0x80007024#64) _ (by decide) (by decide)]; exact hxd
  exact stepObs_store σ i u (0x80007024#64) vminstret (0x05953823#32)
    (instruction.STORE (0x050#12, regidx.Regidx 0x19#5, regidx.Regidx 0x0a#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80007024#64)).mem
      (v10 + sign_extend (m := 64) (0x050#12)).toNat (sdData_val vd))
    (0x23#8) (0x38#8) (0x95#8) (0x05#8)
    hG hpc hminstret w_05953823_jmp nr_05953823_jmp
    (Vsa.Sim.DecodeTable.decode_05953823 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80007024#64) (0x050#12) (regidx.Regidx 0x19#5) (regidx.Regidx 0x0a#5)
      v10 vd hG (rX_bits_x10 _ v10 hx10₂) (rX_bits_x25 _ vd hxd₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **setjmp store @ 0x80007028** (`sd x26,88(a0)`): write `x26` (8 bytes) at `a0 + 0x058`. -/
theorem site_80007028_jmp
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 vd : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hxd : σ.regs.get? Register.x26 = some vd)
    (hmem : SetjmpLoaded σ.mem)
    (hpcv : pc = (0x80007028#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v10 + sign_extend (m := 64) (0x058#12)).toNat)
    (hahiram : (v10 + sign_extend (m := 64) (0x058#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (v10 + sign_extend (m := 64) (0x058#12)).toNat)
    (haalign : (v10 + sign_extend (m := 64) (0x058#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x80007028#64)).mem
        (v10 + sign_extend (m := 64) (0x058#12)).toNat (sdData_val vd) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x80007028#64)).mem
            (v10 + sign_extend (m := 64) (0x058#12)).toNat (sdData_val vd))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := setjmp_at_80007028 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80007028#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x80007028#64) _ (by decide) (by decide)]; exact hx10
  have hxd₂ : (afterNextPC (afterPrelude σ) (0x80007028#64)).regs.get? Register.x26 = some vd := by
    rw [get?_afterNextPC σ (0x80007028#64) _ (by decide) (by decide)]; exact hxd
  exact stepObs_store σ i u (0x80007028#64) vminstret (0x05a53c23#32)
    (instruction.STORE (0x058#12, regidx.Regidx 0x1a#5, regidx.Regidx 0x0a#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80007028#64)).mem
      (v10 + sign_extend (m := 64) (0x058#12)).toNat (sdData_val vd))
    (0x23#8) (0x3c#8) (0xa5#8) (0x05#8)
    hG hpc hminstret w_05a53c23_jmp nr_05a53c23_jmp
    (Vsa.Sim.DecodeTable.decode_05a53c23 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80007028#64) (0x058#12) (regidx.Regidx 0x1a#5) (regidx.Regidx 0x0a#5)
      v10 vd hG (rX_bits_x10 _ v10 hx10₂) (rX_bits_x26 _ vd hxd₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **setjmp store @ 0x8000702c** (`sd x27,96(a0)`): write `x27` (8 bytes) at `a0 + 0x060`. -/
theorem site_8000702c_jmp
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 vd : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hxd : σ.regs.get? Register.x27 = some vd)
    (hmem : SetjmpLoaded σ.mem)
    (hpcv : pc = (0x8000702c#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v10 + sign_extend (m := 64) (0x060#12)).toNat)
    (hahiram : (v10 + sign_extend (m := 64) (0x060#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (v10 + sign_extend (m := 64) (0x060#12)).toNat)
    (haalign : (v10 + sign_extend (m := 64) (0x060#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x8000702c#64)).mem
        (v10 + sign_extend (m := 64) (0x060#12)).toNat (sdData_val vd) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x8000702c#64)).mem
            (v10 + sign_extend (m := 64) (0x060#12)).toNat (sdData_val vd))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := setjmp_at_8000702c hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x8000702c#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x8000702c#64) _ (by decide) (by decide)]; exact hx10
  have hxd₂ : (afterNextPC (afterPrelude σ) (0x8000702c#64)).regs.get? Register.x27 = some vd := by
    rw [get?_afterNextPC σ (0x8000702c#64) _ (by decide) (by decide)]; exact hxd
  exact stepObs_store σ i u (0x8000702c#64) vminstret (0x07b53023#32)
    (instruction.STORE (0x060#12, regidx.Regidx 0x1b#5, regidx.Regidx 0x0a#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x8000702c#64)).mem
      (v10 + sign_extend (m := 64) (0x060#12)).toNat (sdData_val vd))
    (0x23#8) (0x30#8) (0xb5#8) (0x07#8)
    hG hpc hminstret w_07b53023_jmp nr_07b53023_jmp
    (Vsa.Sim.DecodeTable.decode_07b53023 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x8000702c#64) (0x060#12) (regidx.Regidx 0x1b#5) (regidx.Regidx 0x0a#5)
      v10 vd hG (rX_bits_x10 _ v10 hx10₂) (rX_bits_x27 _ vd hxd₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **setjmp store @ 0x80007030** (`sd x2,104(a0)`): write `x2` (8 bytes) at `a0 + 0x068`. -/
theorem site_80007030_jmp
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 vd : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hxd : σ.regs.get? Register.x2 = some vd)
    (hmem : SetjmpLoaded σ.mem)
    (hpcv : pc = (0x80007030#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v10 + sign_extend (m := 64) (0x068#12)).toNat)
    (hahiram : (v10 + sign_extend (m := 64) (0x068#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (v10 + sign_extend (m := 64) (0x068#12)).toNat)
    (haalign : (v10 + sign_extend (m := 64) (0x068#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x80007030#64)).mem
        (v10 + sign_extend (m := 64) (0x068#12)).toNat (sdData_val vd) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x80007030#64)).mem
            (v10 + sign_extend (m := 64) (0x068#12)).toNat (sdData_val vd))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := setjmp_at_80007030 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80007030#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x80007030#64) _ (by decide) (by decide)]; exact hx10
  have hxd₂ : (afterNextPC (afterPrelude σ) (0x80007030#64)).regs.get? Register.x2 = some vd := by
    rw [get?_afterNextPC σ (0x80007030#64) _ (by decide) (by decide)]; exact hxd
  exact stepObs_store σ i u (0x80007030#64) vminstret (0x06253423#32)
    (instruction.STORE (0x068#12, regidx.Regidx 0x02#5, regidx.Regidx 0x0a#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80007030#64)).mem
      (v10 + sign_extend (m := 64) (0x068#12)).toNat (sdData_val vd))
    (0x23#8) (0x34#8) (0x25#8) (0x06#8)
    hG hpc hminstret w_06253423_jmp nr_06253423_jmp
    (Vsa.Sim.DecodeTable.decode_06253423 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80007030#64) (0x068#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x0a#5)
      v10 vd hG (rX_bits_x10 _ v10 hx10₂) (rX_bits_x2 _ vd hxd₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## setjmp: `li a0,0` @ 0x80007034 (`addi a0,x0,0`, rd = x10). -/
theorem site_80007034_jmp
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : SetjmpLoaded σ.mem)
    (hpcv : pc = (0x80007034#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10 ((0#64) + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := setjmp_at_80007034 hmem
  exact stepObs_alu σ i u (0x80007034#64) vminstret (0x00000513#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 ((0#64) + sign_extend (m := 64) (0x000#12)) (0x13#8) (0x05#8) (0x00#8) (0x00#8)
    hG hpc hminstret w_00000513_jmp nr_00000513_jmp
    (Vsa.Sim.DecodeTable.decode_00000513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_li_a0_0 σ (0x80007034#64))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## setjmp: `ret` @ 0x80007038 (`jalr x0,ra,0`). -/
theorem site_80007038_jmp
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vra : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some vra)
    (hmem : SetjmpLoaded σ.mem)
    (hpcv : pc = (0x80007038#64 : BitVec 64))
    (htgt : (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := setjmp_at_80007038 hmem
  have hx1₂ : (rX_bits (regidx.Regidx 0x01#5)).run (afterNextPC (afterPrelude σ) (0x80007038#64))
      = .ok vra (afterNextPC (afterPrelude σ) (0x80007038#64)) := by
    apply rX_bits_x1
    rw [get?_afterNextPC σ (0x80007038#64) _ (by decide) (by decide)]; exact hx1
  exact stepObs_jr σ i u (0x80007038#64) vminstret vra (0x00008067#32) (0x000#12)
    (regidx.Regidx 0x01#5) (0x67#8) (0x80#8) (0x00#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    nr_00008067_jmp w_00008067_jmp
    (Vsa.Sim.DecodeTable.decode_00008067 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    hx1₂ htgt hi

/-! ## longjmp: the 14 `ld rX, off(a0)` ALU-class sites (base = a0 = x10) -/

/-- **longjmp load @ 0x8000703c** (`ld x1,0(a0)`): read 8 bytes at `a0 + 0x000` into `x1`. -/
theorem site_8000703c_jmp
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : LongjmpLoaded σ.mem)
    (hpcv : pc = (0x8000703c#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v10 + sign_extend (m := 64) (0x000#12)).toNat)
    (hhiram : (v10 + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v10 + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v10 + sign_extend (m := 64) (0x000#12)).toNat)
    (halign : (v10 + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0)
    (h0 : σ.mem[(v10 + sign_extend (m := 64) (0x000#12)).toNat]? = some b0)
    (h1 : σ.mem[(v10 + sign_extend (m := 64) (0x000#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(v10 + sign_extend (m := 64) (0x000#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(v10 + sign_extend (m := 64) (0x000#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(v10 + sign_extend (m := 64) (0x000#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(v10 + sign_extend (m := 64) (0x000#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(v10 + sign_extend (m := 64) (0x000#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(v10 + sign_extend (m := 64) (0x000#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x1
          (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := longjmp_at_8000703c hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x8000703c#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x8000703c#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_alu σ i u (0x8000703c#64) vminstret (0x00053083#32)
    (instruction.LOAD (0x000#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x01#5, false, 8))
    Register.x1 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))) (0x83#8) (0x30#8) (0x05#8) (0x00#8)
    hG hpc hminstret w_00053083_jmp nr_00053083_jmp
    (Vsa.Sim.DecodeTable.decode_00053083 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x8000703c#64) (0x000#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x01#5)
      (sigma3_alu σ (0x8000703c#64) Register.x1 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      v10 b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x10 _ v10 hx10₂)
      (wX_bits_x1 _ (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **longjmp load @ 0x80007040** (`ld x8,8(a0)`): read 8 bytes at `a0 + 0x008` into `x8`. -/
theorem site_80007040_jmp
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : LongjmpLoaded σ.mem)
    (hpcv : pc = (0x80007040#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v10 + sign_extend (m := 64) (0x008#12)).toNat)
    (hhiram : (v10 + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v10 + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v10 + sign_extend (m := 64) (0x008#12)).toNat)
    (halign : (v10 + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0)
    (h0 : σ.mem[(v10 + sign_extend (m := 64) (0x008#12)).toNat]? = some b0)
    (h1 : σ.mem[(v10 + sign_extend (m := 64) (0x008#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(v10 + sign_extend (m := 64) (0x008#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(v10 + sign_extend (m := 64) (0x008#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(v10 + sign_extend (m := 64) (0x008#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(v10 + sign_extend (m := 64) (0x008#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(v10 + sign_extend (m := 64) (0x008#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(v10 + sign_extend (m := 64) (0x008#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x8
          (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := longjmp_at_80007040 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80007040#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x80007040#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_alu σ i u (0x80007040#64) vminstret (0x00853403#32)
    (instruction.LOAD (0x008#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x08#5, false, 8))
    Register.x8 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))) (0x03#8) (0x34#8) (0x85#8) (0x00#8)
    hG hpc hminstret w_00853403_jmp nr_00853403_jmp
    (Vsa.Sim.DecodeTable.decode_00853403 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80007040#64) (0x008#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x08#5)
      (sigma3_alu σ (0x80007040#64) Register.x8 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      v10 b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x10 _ v10 hx10₂)
      (wX_bits_x8 _ (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **longjmp load @ 0x80007044** (`ld x9,16(a0)`): read 8 bytes at `a0 + 0x010` into `x9`. -/
theorem site_80007044_jmp
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : LongjmpLoaded σ.mem)
    (hpcv : pc = (0x80007044#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v10 + sign_extend (m := 64) (0x010#12)).toNat)
    (hhiram : (v10 + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v10 + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v10 + sign_extend (m := 64) (0x010#12)).toNat)
    (halign : (v10 + sign_extend (m := 64) (0x010#12)).toNat % 8 = 0)
    (h0 : σ.mem[(v10 + sign_extend (m := 64) (0x010#12)).toNat]? = some b0)
    (h1 : σ.mem[(v10 + sign_extend (m := 64) (0x010#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(v10 + sign_extend (m := 64) (0x010#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(v10 + sign_extend (m := 64) (0x010#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(v10 + sign_extend (m := 64) (0x010#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(v10 + sign_extend (m := 64) (0x010#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(v10 + sign_extend (m := 64) (0x010#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(v10 + sign_extend (m := 64) (0x010#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x9
          (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := longjmp_at_80007044 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80007044#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x80007044#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_alu σ i u (0x80007044#64) vminstret (0x01053483#32)
    (instruction.LOAD (0x010#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x09#5, false, 8))
    Register.x9 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))) (0x83#8) (0x34#8) (0x05#8) (0x01#8)
    hG hpc hminstret w_01053483_jmp nr_01053483_jmp
    (Vsa.Sim.DecodeTable.decode_01053483 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80007044#64) (0x010#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x09#5)
      (sigma3_alu σ (0x80007044#64) Register.x9 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      v10 b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x10 _ v10 hx10₂)
      (wX_bits_x9 _ (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **longjmp load @ 0x80007048** (`ld x18,24(a0)`): read 8 bytes at `a0 + 0x018` into `x18`. -/
theorem site_80007048_jmp
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : LongjmpLoaded σ.mem)
    (hpcv : pc = (0x80007048#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v10 + sign_extend (m := 64) (0x018#12)).toNat)
    (hhiram : (v10 + sign_extend (m := 64) (0x018#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v10 + sign_extend (m := 64) (0x018#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v10 + sign_extend (m := 64) (0x018#12)).toNat)
    (halign : (v10 + sign_extend (m := 64) (0x018#12)).toNat % 8 = 0)
    (h0 : σ.mem[(v10 + sign_extend (m := 64) (0x018#12)).toNat]? = some b0)
    (h1 : σ.mem[(v10 + sign_extend (m := 64) (0x018#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(v10 + sign_extend (m := 64) (0x018#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(v10 + sign_extend (m := 64) (0x018#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(v10 + sign_extend (m := 64) (0x018#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(v10 + sign_extend (m := 64) (0x018#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(v10 + sign_extend (m := 64) (0x018#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(v10 + sign_extend (m := 64) (0x018#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x18
          (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := longjmp_at_80007048 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80007048#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x80007048#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_alu σ i u (0x80007048#64) vminstret (0x01853903#32)
    (instruction.LOAD (0x018#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x12#5, false, 8))
    Register.x18 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))) (0x03#8) (0x39#8) (0x85#8) (0x01#8)
    hG hpc hminstret w_01853903_jmp nr_01853903_jmp
    (Vsa.Sim.DecodeTable.decode_01853903 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80007048#64) (0x018#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x12#5)
      (sigma3_alu σ (0x80007048#64) Register.x18 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      v10 b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x10 _ v10 hx10₂)
      (wX_bits_x18 _ (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **longjmp load @ 0x8000704c** (`ld x19,32(a0)`): read 8 bytes at `a0 + 0x020` into `x19`. -/
theorem site_8000704c_jmp
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : LongjmpLoaded σ.mem)
    (hpcv : pc = (0x8000704c#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v10 + sign_extend (m := 64) (0x020#12)).toNat)
    (hhiram : (v10 + sign_extend (m := 64) (0x020#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v10 + sign_extend (m := 64) (0x020#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v10 + sign_extend (m := 64) (0x020#12)).toNat)
    (halign : (v10 + sign_extend (m := 64) (0x020#12)).toNat % 8 = 0)
    (h0 : σ.mem[(v10 + sign_extend (m := 64) (0x020#12)).toNat]? = some b0)
    (h1 : σ.mem[(v10 + sign_extend (m := 64) (0x020#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(v10 + sign_extend (m := 64) (0x020#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(v10 + sign_extend (m := 64) (0x020#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(v10 + sign_extend (m := 64) (0x020#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(v10 + sign_extend (m := 64) (0x020#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(v10 + sign_extend (m := 64) (0x020#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(v10 + sign_extend (m := 64) (0x020#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x19
          (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := longjmp_at_8000704c hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x8000704c#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x8000704c#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_alu σ i u (0x8000704c#64) vminstret (0x02053983#32)
    (instruction.LOAD (0x020#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x13#5, false, 8))
    Register.x19 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))) (0x83#8) (0x39#8) (0x05#8) (0x02#8)
    hG hpc hminstret w_02053983_jmp nr_02053983_jmp
    (Vsa.Sim.DecodeTable.decode_02053983 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x8000704c#64) (0x020#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x13#5)
      (sigma3_alu σ (0x8000704c#64) Register.x19 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      v10 b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x10 _ v10 hx10₂)
      (wX_bits_x19 _ (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **longjmp load @ 0x80007050** (`ld x20,40(a0)`): read 8 bytes at `a0 + 0x028` into `x20`. -/
theorem site_80007050_jmp
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : LongjmpLoaded σ.mem)
    (hpcv : pc = (0x80007050#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v10 + sign_extend (m := 64) (0x028#12)).toNat)
    (hhiram : (v10 + sign_extend (m := 64) (0x028#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v10 + sign_extend (m := 64) (0x028#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v10 + sign_extend (m := 64) (0x028#12)).toNat)
    (halign : (v10 + sign_extend (m := 64) (0x028#12)).toNat % 8 = 0)
    (h0 : σ.mem[(v10 + sign_extend (m := 64) (0x028#12)).toNat]? = some b0)
    (h1 : σ.mem[(v10 + sign_extend (m := 64) (0x028#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(v10 + sign_extend (m := 64) (0x028#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(v10 + sign_extend (m := 64) (0x028#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(v10 + sign_extend (m := 64) (0x028#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(v10 + sign_extend (m := 64) (0x028#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(v10 + sign_extend (m := 64) (0x028#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(v10 + sign_extend (m := 64) (0x028#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x20
          (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := longjmp_at_80007050 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80007050#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x80007050#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_alu σ i u (0x80007050#64) vminstret (0x02853a03#32)
    (instruction.LOAD (0x028#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x14#5, false, 8))
    Register.x20 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))) (0x03#8) (0x3a#8) (0x85#8) (0x02#8)
    hG hpc hminstret w_02853a03_jmp nr_02853a03_jmp
    (Vsa.Sim.DecodeTable.decode_02853a03 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80007050#64) (0x028#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x14#5)
      (sigma3_alu σ (0x80007050#64) Register.x20 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      v10 b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x10 _ v10 hx10₂)
      (wX_bits_x20 _ (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **longjmp load @ 0x80007054** (`ld x21,48(a0)`): read 8 bytes at `a0 + 0x030` into `x21`. -/
theorem site_80007054_jmp
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : LongjmpLoaded σ.mem)
    (hpcv : pc = (0x80007054#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v10 + sign_extend (m := 64) (0x030#12)).toNat)
    (hhiram : (v10 + sign_extend (m := 64) (0x030#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v10 + sign_extend (m := 64) (0x030#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v10 + sign_extend (m := 64) (0x030#12)).toNat)
    (halign : (v10 + sign_extend (m := 64) (0x030#12)).toNat % 8 = 0)
    (h0 : σ.mem[(v10 + sign_extend (m := 64) (0x030#12)).toNat]? = some b0)
    (h1 : σ.mem[(v10 + sign_extend (m := 64) (0x030#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(v10 + sign_extend (m := 64) (0x030#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(v10 + sign_extend (m := 64) (0x030#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(v10 + sign_extend (m := 64) (0x030#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(v10 + sign_extend (m := 64) (0x030#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(v10 + sign_extend (m := 64) (0x030#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(v10 + sign_extend (m := 64) (0x030#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x21
          (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := longjmp_at_80007054 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80007054#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x80007054#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_alu σ i u (0x80007054#64) vminstret (0x03053a83#32)
    (instruction.LOAD (0x030#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x15#5, false, 8))
    Register.x21 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))) (0x83#8) (0x3a#8) (0x05#8) (0x03#8)
    hG hpc hminstret w_03053a83_jmp nr_03053a83_jmp
    (Vsa.Sim.DecodeTable.decode_03053a83 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80007054#64) (0x030#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x15#5)
      (sigma3_alu σ (0x80007054#64) Register.x21 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      v10 b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x10 _ v10 hx10₂)
      (wX_bits_x21 _ (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **longjmp load @ 0x80007058** (`ld x22,56(a0)`): read 8 bytes at `a0 + 0x038` into `x22`. -/
theorem site_80007058_jmp
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : LongjmpLoaded σ.mem)
    (hpcv : pc = (0x80007058#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v10 + sign_extend (m := 64) (0x038#12)).toNat)
    (hhiram : (v10 + sign_extend (m := 64) (0x038#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v10 + sign_extend (m := 64) (0x038#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v10 + sign_extend (m := 64) (0x038#12)).toNat)
    (halign : (v10 + sign_extend (m := 64) (0x038#12)).toNat % 8 = 0)
    (h0 : σ.mem[(v10 + sign_extend (m := 64) (0x038#12)).toNat]? = some b0)
    (h1 : σ.mem[(v10 + sign_extend (m := 64) (0x038#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(v10 + sign_extend (m := 64) (0x038#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(v10 + sign_extend (m := 64) (0x038#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(v10 + sign_extend (m := 64) (0x038#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(v10 + sign_extend (m := 64) (0x038#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(v10 + sign_extend (m := 64) (0x038#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(v10 + sign_extend (m := 64) (0x038#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x22
          (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := longjmp_at_80007058 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80007058#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x80007058#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_alu σ i u (0x80007058#64) vminstret (0x03853b03#32)
    (instruction.LOAD (0x038#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x16#5, false, 8))
    Register.x22 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))) (0x03#8) (0x3b#8) (0x85#8) (0x03#8)
    hG hpc hminstret w_03853b03_jmp nr_03853b03_jmp
    (Vsa.Sim.DecodeTable.decode_03853b03 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80007058#64) (0x038#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x16#5)
      (sigma3_alu σ (0x80007058#64) Register.x22 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      v10 b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x10 _ v10 hx10₂)
      (wX_bits_x22 _ (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **longjmp load @ 0x8000705c** (`ld x23,64(a0)`): read 8 bytes at `a0 + 0x040` into `x23`. -/
theorem site_8000705c_jmp
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : LongjmpLoaded σ.mem)
    (hpcv : pc = (0x8000705c#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v10 + sign_extend (m := 64) (0x040#12)).toNat)
    (hhiram : (v10 + sign_extend (m := 64) (0x040#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v10 + sign_extend (m := 64) (0x040#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v10 + sign_extend (m := 64) (0x040#12)).toNat)
    (halign : (v10 + sign_extend (m := 64) (0x040#12)).toNat % 8 = 0)
    (h0 : σ.mem[(v10 + sign_extend (m := 64) (0x040#12)).toNat]? = some b0)
    (h1 : σ.mem[(v10 + sign_extend (m := 64) (0x040#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(v10 + sign_extend (m := 64) (0x040#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(v10 + sign_extend (m := 64) (0x040#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(v10 + sign_extend (m := 64) (0x040#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(v10 + sign_extend (m := 64) (0x040#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(v10 + sign_extend (m := 64) (0x040#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(v10 + sign_extend (m := 64) (0x040#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x23
          (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := longjmp_at_8000705c hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x8000705c#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x8000705c#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_alu σ i u (0x8000705c#64) vminstret (0x04053b83#32)
    (instruction.LOAD (0x040#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x17#5, false, 8))
    Register.x23 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))) (0x83#8) (0x3b#8) (0x05#8) (0x04#8)
    hG hpc hminstret w_04053b83_jmp nr_04053b83_jmp
    (Vsa.Sim.DecodeTable.decode_04053b83 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x8000705c#64) (0x040#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x17#5)
      (sigma3_alu σ (0x8000705c#64) Register.x23 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      v10 b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x10 _ v10 hx10₂)
      (wX_bits_x23 _ (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **longjmp load @ 0x80007060** (`ld x24,72(a0)`): read 8 bytes at `a0 + 0x048` into `x24`. -/
theorem site_80007060_jmp
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : LongjmpLoaded σ.mem)
    (hpcv : pc = (0x80007060#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v10 + sign_extend (m := 64) (0x048#12)).toNat)
    (hhiram : (v10 + sign_extend (m := 64) (0x048#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v10 + sign_extend (m := 64) (0x048#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v10 + sign_extend (m := 64) (0x048#12)).toNat)
    (halign : (v10 + sign_extend (m := 64) (0x048#12)).toNat % 8 = 0)
    (h0 : σ.mem[(v10 + sign_extend (m := 64) (0x048#12)).toNat]? = some b0)
    (h1 : σ.mem[(v10 + sign_extend (m := 64) (0x048#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(v10 + sign_extend (m := 64) (0x048#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(v10 + sign_extend (m := 64) (0x048#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(v10 + sign_extend (m := 64) (0x048#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(v10 + sign_extend (m := 64) (0x048#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(v10 + sign_extend (m := 64) (0x048#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(v10 + sign_extend (m := 64) (0x048#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x24
          (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := longjmp_at_80007060 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80007060#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x80007060#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_alu σ i u (0x80007060#64) vminstret (0x04853c03#32)
    (instruction.LOAD (0x048#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x18#5, false, 8))
    Register.x24 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))) (0x03#8) (0x3c#8) (0x85#8) (0x04#8)
    hG hpc hminstret w_04853c03_jmp nr_04853c03_jmp
    (Vsa.Sim.DecodeTable.decode_04853c03 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80007060#64) (0x048#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x18#5)
      (sigma3_alu σ (0x80007060#64) Register.x24 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      v10 b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x10 _ v10 hx10₂)
      (wX_bits_x24 _ (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **longjmp load @ 0x80007064** (`ld x25,80(a0)`): read 8 bytes at `a0 + 0x050` into `x25`. -/
theorem site_80007064_jmp
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : LongjmpLoaded σ.mem)
    (hpcv : pc = (0x80007064#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v10 + sign_extend (m := 64) (0x050#12)).toNat)
    (hhiram : (v10 + sign_extend (m := 64) (0x050#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v10 + sign_extend (m := 64) (0x050#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v10 + sign_extend (m := 64) (0x050#12)).toNat)
    (halign : (v10 + sign_extend (m := 64) (0x050#12)).toNat % 8 = 0)
    (h0 : σ.mem[(v10 + sign_extend (m := 64) (0x050#12)).toNat]? = some b0)
    (h1 : σ.mem[(v10 + sign_extend (m := 64) (0x050#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(v10 + sign_extend (m := 64) (0x050#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(v10 + sign_extend (m := 64) (0x050#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(v10 + sign_extend (m := 64) (0x050#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(v10 + sign_extend (m := 64) (0x050#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(v10 + sign_extend (m := 64) (0x050#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(v10 + sign_extend (m := 64) (0x050#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x25
          (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := longjmp_at_80007064 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80007064#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x80007064#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_alu σ i u (0x80007064#64) vminstret (0x05053c83#32)
    (instruction.LOAD (0x050#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x19#5, false, 8))
    Register.x25 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))) (0x83#8) (0x3c#8) (0x05#8) (0x05#8)
    hG hpc hminstret w_05053c83_jmp nr_05053c83_jmp
    (Vsa.Sim.DecodeTable.decode_05053c83 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80007064#64) (0x050#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x19#5)
      (sigma3_alu σ (0x80007064#64) Register.x25 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      v10 b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x10 _ v10 hx10₂)
      (wX_bits_x25 _ (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **longjmp load @ 0x80007068** (`ld x26,88(a0)`): read 8 bytes at `a0 + 0x058` into `x26`. -/
theorem site_80007068_jmp
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : LongjmpLoaded σ.mem)
    (hpcv : pc = (0x80007068#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v10 + sign_extend (m := 64) (0x058#12)).toNat)
    (hhiram : (v10 + sign_extend (m := 64) (0x058#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v10 + sign_extend (m := 64) (0x058#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v10 + sign_extend (m := 64) (0x058#12)).toNat)
    (halign : (v10 + sign_extend (m := 64) (0x058#12)).toNat % 8 = 0)
    (h0 : σ.mem[(v10 + sign_extend (m := 64) (0x058#12)).toNat]? = some b0)
    (h1 : σ.mem[(v10 + sign_extend (m := 64) (0x058#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(v10 + sign_extend (m := 64) (0x058#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(v10 + sign_extend (m := 64) (0x058#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(v10 + sign_extend (m := 64) (0x058#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(v10 + sign_extend (m := 64) (0x058#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(v10 + sign_extend (m := 64) (0x058#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(v10 + sign_extend (m := 64) (0x058#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x26
          (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := longjmp_at_80007068 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80007068#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x80007068#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_alu σ i u (0x80007068#64) vminstret (0x05853d03#32)
    (instruction.LOAD (0x058#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x1a#5, false, 8))
    Register.x26 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))) (0x03#8) (0x3d#8) (0x85#8) (0x05#8)
    hG hpc hminstret w_05853d03_jmp nr_05853d03_jmp
    (Vsa.Sim.DecodeTable.decode_05853d03 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80007068#64) (0x058#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x1a#5)
      (sigma3_alu σ (0x80007068#64) Register.x26 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      v10 b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x10 _ v10 hx10₂)
      (wX_bits_x26 _ (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **longjmp load @ 0x8000706c** (`ld x27,96(a0)`): read 8 bytes at `a0 + 0x060` into `x27`. -/
theorem site_8000706c_jmp
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : LongjmpLoaded σ.mem)
    (hpcv : pc = (0x8000706c#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v10 + sign_extend (m := 64) (0x060#12)).toNat)
    (hhiram : (v10 + sign_extend (m := 64) (0x060#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v10 + sign_extend (m := 64) (0x060#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v10 + sign_extend (m := 64) (0x060#12)).toNat)
    (halign : (v10 + sign_extend (m := 64) (0x060#12)).toNat % 8 = 0)
    (h0 : σ.mem[(v10 + sign_extend (m := 64) (0x060#12)).toNat]? = some b0)
    (h1 : σ.mem[(v10 + sign_extend (m := 64) (0x060#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(v10 + sign_extend (m := 64) (0x060#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(v10 + sign_extend (m := 64) (0x060#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(v10 + sign_extend (m := 64) (0x060#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(v10 + sign_extend (m := 64) (0x060#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(v10 + sign_extend (m := 64) (0x060#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(v10 + sign_extend (m := 64) (0x060#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x27
          (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := longjmp_at_8000706c hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x8000706c#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x8000706c#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_alu σ i u (0x8000706c#64) vminstret (0x06053d83#32)
    (instruction.LOAD (0x060#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x1b#5, false, 8))
    Register.x27 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))) (0x83#8) (0x3d#8) (0x05#8) (0x06#8)
    hG hpc hminstret w_06053d83_jmp nr_06053d83_jmp
    (Vsa.Sim.DecodeTable.decode_06053d83 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x8000706c#64) (0x060#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x1b#5)
      (sigma3_alu σ (0x8000706c#64) Register.x27 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      v10 b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x10 _ v10 hx10₂)
      (wX_bits_x27 _ (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **longjmp load @ 0x80007070** (`ld x2,104(a0)`): read 8 bytes at `a0 + 0x068` into `x2`. -/
theorem site_80007070_jmp
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : LongjmpLoaded σ.mem)
    (hpcv : pc = (0x80007070#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v10 + sign_extend (m := 64) (0x068#12)).toNat)
    (hhiram : (v10 + sign_extend (m := 64) (0x068#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v10 + sign_extend (m := 64) (0x068#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v10 + sign_extend (m := 64) (0x068#12)).toNat)
    (halign : (v10 + sign_extend (m := 64) (0x068#12)).toNat % 8 = 0)
    (h0 : σ.mem[(v10 + sign_extend (m := 64) (0x068#12)).toNat]? = some b0)
    (h1 : σ.mem[(v10 + sign_extend (m := 64) (0x068#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(v10 + sign_extend (m := 64) (0x068#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(v10 + sign_extend (m := 64) (0x068#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(v10 + sign_extend (m := 64) (0x068#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(v10 + sign_extend (m := 64) (0x068#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(v10 + sign_extend (m := 64) (0x068#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(v10 + sign_extend (m := 64) (0x068#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x2
          (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := longjmp_at_80007070 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80007070#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x80007070#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_alu σ i u (0x80007070#64) vminstret (0x06853103#32)
    (instruction.LOAD (0x068#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x02#5, false, 8))
    Register.x2 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))) (0x03#8) (0x31#8) (0x85#8) (0x06#8)
    hG hpc hminstret w_06853103_jmp nr_06853103_jmp
    (Vsa.Sim.DecodeTable.decode_06853103 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80007070#64) (0x068#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x02#5)
      (sigma3_alu σ (0x80007070#64) Register.x2 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      v10 b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x10 _ v10 hx10₂)
      (wX_bits_x2 _ (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## longjmp: `seqz a0,a1` @ 0x80007074 (`SLTIU a0,a1,1`, rd = x10, rs1 = x11). -/

theorem exec_seqz_jmp (σ : MState) (pc : BitVec 64) (v11 : BitVec 64)
    (hx11 : σ.regs.get? Register.x11 = some v11) :
    (execute (instruction.ITYPE (0x001#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0a#5, iop.SLTIU))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x10
            (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v11 (sign_extend (m := 64) (0x001#12)))))) := by
  have hx11₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx11
  exact execute_itype_sltiu_char (0x001#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0a#5) v11
    (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x10
      (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v11 (sign_extend (m := 64) (0x001#12))))))
    (rX_bits_x11 _ v11 hx11₂)
    (wX_bits_x10 _ (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v11 (sign_extend (m := 64) (0x001#12))))))

theorem site_80007074_jmp
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : LongjmpLoaded σ.mem)
    (hpcv : pc = (0x80007074#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10
          (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v11 (sign_extend (m := 64) (0x001#12)))))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := longjmp_at_80007074 hmem
  exact stepObs_alu σ i u (0x80007074#64) vminstret (0x0015b513#32)
    (instruction.ITYPE (0x001#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0a#5, iop.SLTIU))
    Register.x10 (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v11 (sign_extend (m := 64) (0x001#12)))))
    (0x13#8) (0xb5#8) (0x15#8) (0x00#8)
    hG hpc hminstret w_0015b513_jmp nr_0015b513_jmp
    (Vsa.Sim.DecodeTable.decode_0015b513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_seqz_jmp σ (0x80007074#64) v11 hx11)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## longjmp: `add a0,a0,a1` @ 0x80007078 (`RTYPE ADD`, rs2 = x11, rs1 = x10, rd = x10). -/

theorem exec_add_jmp (σ : MState) (pc : BitVec 64) (v10 v11 : BitVec 64)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hx11 : σ.regs.get? Register.x11 = some v11) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0b#5, regidx.Regidx 0x0a#5, regidx.Regidx 0x0a#5, rop.ADD))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x10 (v10 + v11)) := by
  have hx10₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx10
  have hx11₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx11
  exact execute_rtype_add_char (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0a#5)
    v10 v11 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x10 (v10 + v11))
    (rX_bits_x10 _ v10 hx10₂) (rX_bits_x11 _ v11 hx11₂)
    (wX_bits_x10 _ (v10 + v11))

theorem site_80007078_jmp
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : LongjmpLoaded σ.mem)
    (hpcv : pc = (0x80007078#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x10 (v10 + v11)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := longjmp_at_80007078 hmem
  exact stepObs_alu σ i u (0x80007078#64) vminstret (0x00b50533#32)
    (instruction.RTYPE (regidx.Regidx 0x0b#5, regidx.Regidx 0x0a#5, regidx.Regidx 0x0a#5, rop.ADD))
    Register.x10 (v10 + v11) (0x33#8) (0x05#8) (0xb5#8) (0x00#8)
    hG hpc hminstret w_00b50533_jmp nr_00b50533_jmp
    (Vsa.Sim.DecodeTable.decode_00b50533 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_add_jmp σ (0x80007078#64) v10 v11 hx10 hx11)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## longjmp: `ret` @ 0x8000707c (`jalr x0,ra,0`). -/
theorem site_8000707c_jmp
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vra : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some vra)
    (hmem : LongjmpLoaded σ.mem)
    (hpcv : pc = (0x8000707c#64 : BitVec 64))
    (htgt : (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := longjmp_at_8000707c hmem
  have hx1₂ : (rX_bits (regidx.Regidx 0x01#5)).run (afterNextPC (afterPrelude σ) (0x8000707c#64))
      = .ok vra (afterNextPC (afterPrelude σ) (0x8000707c#64)) := by
    apply rX_bits_x1
    rw [get?_afterNextPC σ (0x8000707c#64) _ (by decide) (by decide)]; exact hx1
  exact stepObs_jr σ i u (0x8000707c#64) vminstret vra (0x00008067#32) (0x000#12)
    (regidx.Regidx 0x01#5) (0x67#8) (0x80#8) (0x00#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    nr_00008067_jmp w_00008067_jmp
    (Vsa.Sim.DecodeTable.decode_00008067 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    hx1₂ htgt hi

end Vsa.Sim
