import Vsa.Sim.ValueSites
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part08
import Vsa.Sim.DecodeTable.Batch01Part15
import Vsa.Sim.DecodeTable.Batch01Part18
import Vsa.Sim.DecodeTable.Batch02Part21
import Vsa.Sim.DecodeTable.Batch03Part17
import Vsa.Sim.DecodeTable.Batch03Part21
import Vsa.Sim.DecodeTable.Batch05Part10
import Vsa.Sim.DecodeTable.Batch06Part16
import Vsa.Sim.DecodeTable.Batch06Part20
import Vsa.Sim.DecodeTable.Batch12Part19
import Vsa.Sim.DecodeTable.Batch16Part17
import Vsa.Sim.Code.Env_new

/-!
# Layer 3 — per-site observational step lemmas for `env_new`

One observational-step (`StepObs`) lemma per instruction of the success path of
`env_new` (`c/src/env.c`, @0x800029fc, 24 instructions in the census; the success
path is 15 instructions ending in `ret` at 0x80002a34, plus a NULL-error path
[0x80002a38, 0x80002a5c) that calls `exit` and never returns — see `EnvNewSpec`).

The success path (from `experiments/disasm.txt`):

```
29fc addi sp,sp,-16        ; ITYPE addi x2,x2,0xff0
2a00 sd   s0,0(sp)         ; STORE sd x8 @ x2+0
2a04 mv   s0,a0            ; ITYPE addi x8,x10,0
2a08 li   a0,32            ; ITYPE addi x10,x0,0x020
2a0c sd   ra,8(sp)         ; STORE sd x1 @ x2+8
2a10 jal  malloc           ; JAL x1, 0x001d80  → 0x80004790
2a14 beqz a0,80002a38      ; BTYPE beq x10,x0  (NULL-error path)
2a18 ld   ra,8(sp)         ; LOAD ld x1, 8(x2)
2a1c sd   s0,24(a0)        ; STORE sd x8 @ x10+24  (parent field)
2a20 ld   s0,0(sp)         ; LOAD ld x8, 0(x2)
2a24 sd   zero,0(a0)       ; STORE sd x0 @ x10+0   (count=cap=0)
2a28 sd   zero,8(a0)       ; STORE sd x0 @ x10+8   (names=NULL)
2a2c sd   zero,16(a0)      ; STORE sd x0 @ x10+16  (vals=NULL)
2a30 addi sp,sp,16         ; ITYPE addi x2,x2,0x010
2a34 ret                   ; JALR x0, 0(x1)
```

**Loads are ALU-class sites.** A `ld rd,off(rs1)` writes a GPR with
`sign_extend (dword)`, so its observation is `sigmaPost_alu σ pc vm rd v` (via
`exec_ld` from `ValueSites`) — consumed by `obs_alu_*`/`frame_alu`, exactly like
an `addi`. The stores use `exec_sd_val` (width-8 `sd`).

Reuses the execution machinery from `ValueSites` and imports the required decode
parts directly. It also reuses the shared byte-word facts
`w_00053423`/`w_00008067` (+ their `nr_`). The 13 fresh instruction words get
`_env`-suffixed byte-word facts (collision sweep).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Byte-word / non-RVC facts for the 13 fresh `env_new` instruction words -/

theorem w_ff010113_env : (((0xff#8).append (0x01#8)).append (0x01#8)).append (0x13#8) = (0xff010113#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_ff010113_env : Sail.BitVec.extractLsb ((((0xff#8).append (0x01#8)).append (0x01#8)).append (0x13#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_00813023_env : (((0x00#8).append (0x81#8)).append (0x30#8)).append (0x23#8) = (0x00813023#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00813023_env : Sail.BitVec.extractLsb ((((0x00#8).append (0x81#8)).append (0x30#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_00050413_env : (((0x00#8).append (0x05#8)).append (0x04#8)).append (0x13#8) = (0x00050413#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00050413_env : Sail.BitVec.extractLsb ((((0x00#8).append (0x05#8)).append (0x04#8)).append (0x13#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_02000513_env : (((0x02#8).append (0x00#8)).append (0x05#8)).append (0x13#8) = (0x02000513#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_02000513_env : Sail.BitVec.extractLsb ((((0x02#8).append (0x00#8)).append (0x05#8)).append (0x13#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_00113423_env : (((0x00#8).append (0x11#8)).append (0x34#8)).append (0x23#8) = (0x00113423#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00113423_env : Sail.BitVec.extractLsb ((((0x00#8).append (0x11#8)).append (0x34#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_581010ef_env : (((0x58#8).append (0x10#8)).append (0x10#8)).append (0xef#8) = (0x581010ef#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_581010ef_env : Sail.BitVec.extractLsb ((((0x58#8).append (0x10#8)).append (0x10#8)).append (0xef#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_02050263_env : (((0x02#8).append (0x05#8)).append (0x02#8)).append (0x63#8) = (0x02050263#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_02050263_env : Sail.BitVec.extractLsb ((((0x02#8).append (0x05#8)).append (0x02#8)).append (0x63#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_00813083_env : (((0x00#8).append (0x81#8)).append (0x30#8)).append (0x83#8) = (0x00813083#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00813083_env : Sail.BitVec.extractLsb ((((0x00#8).append (0x81#8)).append (0x30#8)).append (0x83#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_00853c23_env : (((0x00#8).append (0x85#8)).append (0x3c#8)).append (0x23#8) = (0x00853c23#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00853c23_env : Sail.BitVec.extractLsb ((((0x00#8).append (0x85#8)).append (0x3c#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_00013403_env : (((0x00#8).append (0x01#8)).append (0x34#8)).append (0x03#8) = (0x00013403#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00013403_env : Sail.BitVec.extractLsb ((((0x00#8).append (0x01#8)).append (0x34#8)).append (0x03#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_00053023_env : (((0x00#8).append (0x05#8)).append (0x30#8)).append (0x23#8) = (0x00053023#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00053023_env : Sail.BitVec.extractLsb ((((0x00#8).append (0x05#8)).append (0x30#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_00053823_env : (((0x00#8).append (0x05#8)).append (0x38#8)).append (0x23#8) = (0x00053823#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00053823_env : Sail.BitVec.extractLsb ((((0x00#8).append (0x05#8)).append (0x38#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_01010113_env : (((0x01#8).append (0x01#8)).append (0x01#8)).append (0x13#8) = (0x01010113#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_01010113_env : Sail.BitVec.extractLsb ((((0x01#8).append (0x01#8)).append (0x01#8)).append (0x13#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-! ## Site 0x800029fc (`addi sp,sp,-16`): `x2 := x2 + sext 0xff0`. -/
theorem site_800029fc_env
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hmem : Env_newLoaded σ.mem)
    (hpcv : pc = (0x800029fc#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x2 (vsp + sign_extend (m := 64) (0xff0#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_new_at_800029fc hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x800029fc#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x800029fc#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x800029fc#64) vminstret (0xff010113#32)
    (instruction.ITYPE (0xff0#12, regidx.Regidx 0x02#5, regidx.Regidx 0x02#5, iop.ADDI))
    Register.x2 (vsp + sign_extend (m := 64) (0xff0#12)) (0x13#8) (0x01#8) (0x01#8) (0xff#8)
    hG hpc hminstret w_ff010113_env nr_ff010113_env
    (Vsa.Sim.DecodeTable.decode_ff010113 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0xff0#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x02#5) vsp
      (afterNextPC (afterPrelude σ) (0x800029fc#64))
      (sigma3_alu σ (0x800029fc#64) Register.x2 (vsp + sign_extend (m := 64) (0xff0#12)))
      (rX_bits_x2 _ vsp hx2₂) (wX_bits_x2 _ (vsp + sign_extend (m := 64) (0xff0#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80002a00 (`sd s0,0(sp)`): store `x8` (8 bytes) @ `x2+0`. -/
theorem site_80002a00_env
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp v8 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hx8 : σ.regs.get? Register.x8 = some v8)
    (hmem : Env_newLoaded σ.mem)
    (hpcv : pc = (0x80002a00#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x000#12)).toNat)
    (hahiram : (vsp + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (vsp + sign_extend (m := 64) (0x000#12)).toNat)
    (haalign : (vsp + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x80002a00#64)).mem
        (vsp + sign_extend (m := 64) (0x000#12)).toNat (sdData_val v8) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x80002a00#64)).mem
            (vsp + sign_extend (m := 64) (0x000#12)).toNat (sdData_val v8))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_new_at_80002a00 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80002a00#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x80002a00#64) _ (by decide) (by decide)]; exact hx2
  have hx8₂ : (afterNextPC (afterPrelude σ) (0x80002a00#64)).regs.get? Register.x8 = some v8 := by
    rw [get?_afterNextPC σ (0x80002a00#64) _ (by decide) (by decide)]; exact hx8
  exact stepObs_store σ i u (0x80002a00#64) vminstret (0x00813023#32)
    (instruction.STORE (0x000#12, regidx.Regidx 0x08#5, regidx.Regidx 0x02#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80002a00#64)).mem
      (vsp + sign_extend (m := 64) (0x000#12)).toNat (sdData_val v8))
    (0x23#8) (0x30#8) (0x81#8) (0x00#8)
    hG hpc hminstret w_00813023_env nr_00813023_env
    (Vsa.Sim.DecodeTable.decode_00813023 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80002a00#64) (0x000#12) (regidx.Regidx 0x08#5) (regidx.Regidx 0x02#5)
      vsp v8 hG (rX_bits_x2 _ vsp hx2₂) (rX_bits_x8 _ v8 hx8₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80002a04 (`mv s0,a0`): `x8 := x10 + sext 0`. -/
theorem site_80002a04_env
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : Env_newLoaded σ.mem)
    (hpcv : pc = (0x80002a04#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x8 (v10 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_new_at_80002a04 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80002a04#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x80002a04#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_alu σ i u (0x80002a04#64) vminstret (0x00050413#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x08#5, iop.ADDI))
    Register.x8 (v10 + sign_extend (m := 64) (0x000#12)) (0x13#8) (0x04#8) (0x05#8) (0x00#8)
    hG hpc hminstret w_00050413_env nr_00050413_env
    (Vsa.Sim.DecodeTable.decode_00050413 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x08#5) v10
      (afterNextPC (afterPrelude σ) (0x80002a04#64))
      (sigma3_alu σ (0x80002a04#64) Register.x8 (v10 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x10 _ v10 hx10₂) (wX_bits_x8 _ (v10 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80002a08 (`li a0,32`): `x10 := 0 + sext 0x020`. -/
theorem site_80002a08_env
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Env_newLoaded σ.mem)
    (hpcv : pc = (0x80002a08#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10 ((0#64) + sign_extend (m := 64) (0x020#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_new_at_80002a08 hmem
  exact stepObs_alu σ i u (0x80002a08#64) vminstret (0x02000513#32)
    (instruction.ITYPE (0x020#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 ((0#64) + sign_extend (m := 64) (0x020#12)) (0x13#8) (0x05#8) (0x00#8) (0x02#8)
    hG hpc hminstret w_02000513_env nr_02000513_env
    (Vsa.Sim.DecodeTable.decode_02000513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x020#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0a#5) (0#64)
      (afterNextPC (afterPrelude σ) (0x80002a08#64))
      (sigma3_alu σ (0x80002a08#64) Register.x10 ((0#64) + sign_extend (m := 64) (0x020#12)))
      (rX_bits_zero _) (wX_bits_x10 _ ((0#64) + sign_extend (m := 64) (0x020#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80002a0c (`sd ra,8(sp)`): store `x1` (8 bytes) @ `x2+8`. -/
theorem site_80002a0c_env
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp v1 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hx1 : σ.regs.get? Register.x1 = some v1)
    (hmem : Env_newLoaded σ.mem)
    (hpcv : pc = (0x80002a0c#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x008#12)).toNat)
    (hahiram : (vsp + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (vsp + sign_extend (m := 64) (0x008#12)).toNat)
    (haalign : (vsp + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x80002a0c#64)).mem
        (vsp + sign_extend (m := 64) (0x008#12)).toNat (sdData_val v1) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x80002a0c#64)).mem
            (vsp + sign_extend (m := 64) (0x008#12)).toNat (sdData_val v1))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_new_at_80002a0c hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80002a0c#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x80002a0c#64) _ (by decide) (by decide)]; exact hx2
  have hx1₂ : (afterNextPC (afterPrelude σ) (0x80002a0c#64)).regs.get? Register.x1 = some v1 := by
    rw [get?_afterNextPC σ (0x80002a0c#64) _ (by decide) (by decide)]; exact hx1
  exact stepObs_store σ i u (0x80002a0c#64) vminstret (0x00113423#32)
    (instruction.STORE (0x008#12, regidx.Regidx 0x01#5, regidx.Regidx 0x02#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80002a0c#64)).mem
      (vsp + sign_extend (m := 64) (0x008#12)).toNat (sdData_val v1))
    (0x23#8) (0x34#8) (0x11#8) (0x00#8)
    hG hpc hminstret w_00113423_env nr_00113423_env
    (Vsa.Sim.DecodeTable.decode_00113423 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80002a0c#64) (0x008#12) (regidx.Regidx 0x01#5) (regidx.Regidx 0x02#5)
      vsp v1 hG (rX_bits_x2 _ vsp hx2₂) (rX_bits_x1 _ v1 hx1₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80002a10 (`jal malloc`): `x1 := pc+4`, `PC := pc + sext 0x001d80` = mallocEntry. -/
theorem site_80002a10_env
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Env_newLoaded σ.mem)
    (hpcv : pc = (0x80002a10#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jal σ pc vminstret (0x001d80#21) Register.x1 (BitVec.addInt pc 4)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_new_at_80002a10 hmem
  exact stepObs_jal σ i u (0x80002a10#64) vminstret (0x581010ef#32) (0x001d80#21)
    (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x80002a10#64) 4)
    (0xef#8) (0x10#8) (0x10#8) (0x58#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    nr_581010ef_env w_581010ef_env
    (Vsa.Sim.DecodeTable.decode_581010ef (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (wX_bits_x1 _ (BitVec.addInt (0x80002a10#64) 4)) hi

/-! ## Site 0x80002a14 (`beqz a0,...`, not taken): `x10 ≠ 0` ⇒ fall to 0x80002a18. -/
theorem site_80002a14_nottaken_env
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : Env_newLoaded σ.mem)
    (hpcv : pc = (0x80002a14#64 : BitVec 64)) (hv : (v10 == 0#64) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_new_at_80002a14 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80002a14#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x80002a14#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_branch_nottaken σ i u (0x80002a14#64) vminstret (0x0024#13)
    (regidx.Regidx 0x0a#5) (regidx.Regidx 0x00#5) bop.BEQ (0x02050263#32)
    (0x63#8) (0x02#8) (0x05#8) (0x02#8)
    hG hpc hminstret w_02050263_env nr_02050263_env
    (Vsa.Sim.DecodeTable.decode_02050263 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_btype_beq_nottaken (0x0024#13) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x00#5)
      v10 (0#64) (afterNextPC (afterPrelude σ) (0x80002a14#64))
      (rX_bits_x10 _ v10 hx10₂) (rX_bits_zero _) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80002a18 (`ld ra,8(sp)`): ALU-class; `x1 := sext (dword @ x2+8)`. -/
theorem site_80002a18_env
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hmem : Env_newLoaded σ.mem)
    (hpcv : pc = (0x80002a18#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x008#12)).toNat)
    (hhiram : (vsp + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vsp + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vsp + sign_extend (m := 64) (0x008#12)).toNat)
    (halign : (vsp + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0)
    (h0 : σ.mem[(vsp + sign_extend (m := 64) (0x008#12)).toNat]? = some b0)
    (h1 : σ.mem[(vsp + sign_extend (m := 64) (0x008#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(vsp + sign_extend (m := 64) (0x008#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(vsp + sign_extend (m := 64) (0x008#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(vsp + sign_extend (m := 64) (0x008#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(vsp + sign_extend (m := 64) (0x008#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(vsp + sign_extend (m := 64) (0x008#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(vsp + sign_extend (m := 64) (0x008#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x1
          (sign_extend (m := 64)
            ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
              : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_new_at_80002a18 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80002a18#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x80002a18#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x80002a18#64) vminstret (0x00813083#32)
    (instruction.LOAD (0x008#12, regidx.Regidx 0x02#5, regidx.Regidx 0x01#5, false, 8))
    Register.x1
    (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x83#8) (0x30#8) (0x81#8) (0x00#8)
    hG hpc hminstret w_00813083_env nr_00813083_env
    (Vsa.Sim.DecodeTable.decode_00813083 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80002a18#64) (0x008#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x01#5)
      (sigma3_alu σ (0x80002a18#64) Register.x1
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      vsp b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x2 _ vsp hx2₂)
      (wX_bits_x1 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80002a1c (`sd s0,24(a0)`): store `x8` (8 bytes) @ `x10+24` (parent field). -/
theorem site_80002a1c_env
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 v8 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hx8 : σ.regs.get? Register.x8 = some v8)
    (hmem : Env_newLoaded σ.mem)
    (hpcv : pc = (0x80002a1c#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v10 + sign_extend (m := 64) (0x018#12)).toNat)
    (hahiram : (v10 + sign_extend (m := 64) (0x018#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (v10 + sign_extend (m := 64) (0x018#12)).toNat)
    (haalign : (v10 + sign_extend (m := 64) (0x018#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x80002a1c#64)).mem
        (v10 + sign_extend (m := 64) (0x018#12)).toNat (sdData_val v8) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x80002a1c#64)).mem
            (v10 + sign_extend (m := 64) (0x018#12)).toNat (sdData_val v8))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_new_at_80002a1c hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80002a1c#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x80002a1c#64) _ (by decide) (by decide)]; exact hx10
  have hx8₂ : (afterNextPC (afterPrelude σ) (0x80002a1c#64)).regs.get? Register.x8 = some v8 := by
    rw [get?_afterNextPC σ (0x80002a1c#64) _ (by decide) (by decide)]; exact hx8
  exact stepObs_store σ i u (0x80002a1c#64) vminstret (0x00853c23#32)
    (instruction.STORE (0x018#12, regidx.Regidx 0x08#5, regidx.Regidx 0x0a#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80002a1c#64)).mem
      (v10 + sign_extend (m := 64) (0x018#12)).toNat (sdData_val v8))
    (0x23#8) (0x3c#8) (0x85#8) (0x00#8)
    hG hpc hminstret w_00853c23_env nr_00853c23_env
    (Vsa.Sim.DecodeTable.decode_00853c23 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80002a1c#64) (0x018#12) (regidx.Regidx 0x08#5) (regidx.Regidx 0x0a#5)
      v10 v8 hG (rX_bits_x10 _ v10 hx10₂) (rX_bits_x8 _ v8 hx8₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80002a20 (`ld s0,0(sp)`): ALU-class; `x8 := sext (dword @ x2+0)`. -/
theorem site_80002a20_env
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hmem : Env_newLoaded σ.mem)
    (hpcv : pc = (0x80002a20#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x000#12)).toNat)
    (hhiram : (vsp + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vsp + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vsp + sign_extend (m := 64) (0x000#12)).toNat)
    (halign : (vsp + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0)
    (h0 : σ.mem[(vsp + sign_extend (m := 64) (0x000#12)).toNat]? = some b0)
    (h1 : σ.mem[(vsp + sign_extend (m := 64) (0x000#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(vsp + sign_extend (m := 64) (0x000#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(vsp + sign_extend (m := 64) (0x000#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(vsp + sign_extend (m := 64) (0x000#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(vsp + sign_extend (m := 64) (0x000#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(vsp + sign_extend (m := 64) (0x000#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(vsp + sign_extend (m := 64) (0x000#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x8
          (sign_extend (m := 64)
            ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
              : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_new_at_80002a20 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80002a20#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x80002a20#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x80002a20#64) vminstret (0x00013403#32)
    (instruction.LOAD (0x000#12, regidx.Regidx 0x02#5, regidx.Regidx 0x08#5, false, 8))
    Register.x8
    (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x03#8) (0x34#8) (0x01#8) (0x00#8)
    hG hpc hminstret w_00013403_env nr_00013403_env
    (Vsa.Sim.DecodeTable.decode_00013403 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80002a20#64) (0x000#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x08#5)
      (sigma3_alu σ (0x80002a20#64) Register.x8
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      vsp b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x2 _ vsp hx2₂)
      (wX_bits_x8 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80002a24 (`sd zero,0(a0)`): store 0 (8 bytes) @ `x10+0` (count=cap=0). -/
theorem site_80002a24_env
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : Env_newLoaded σ.mem)
    (hpcv : pc = (0x80002a24#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v10 + sign_extend (m := 64) (0x000#12)).toNat)
    (hahiram : (v10 + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (v10 + sign_extend (m := 64) (0x000#12)).toNat)
    (haalign : (v10 + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x80002a24#64)).mem
        (v10 + sign_extend (m := 64) (0x000#12)).toNat (sdData_val (0#64)) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x80002a24#64)).mem
            (v10 + sign_extend (m := 64) (0x000#12)).toNat (sdData_val (0#64)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_new_at_80002a24 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80002a24#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x80002a24#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_store σ i u (0x80002a24#64) vminstret (0x00053023#32)
    (instruction.STORE (0x000#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80002a24#64)).mem
      (v10 + sign_extend (m := 64) (0x000#12)).toNat (sdData_val (0#64)))
    (0x23#8) (0x30#8) (0x05#8) (0x00#8)
    hG hpc hminstret w_00053023_env nr_00053023_env
    (Vsa.Sim.DecodeTable.decode_00053023 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80002a24#64) (0x000#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0a#5)
      v10 (0#64) hG (rX_bits_x10 _ v10 hx10₂) (rX_bits_zero _) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80002a28 (`sd zero,8(a0)`): store 0 (8 bytes) @ `x10+8` (names=NULL). -/
theorem site_80002a28_env
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : Env_newLoaded σ.mem)
    (hpcv : pc = (0x80002a28#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v10 + sign_extend (m := 64) (0x008#12)).toNat)
    (hahiram : (v10 + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (v10 + sign_extend (m := 64) (0x008#12)).toNat)
    (haalign : (v10 + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x80002a28#64)).mem
        (v10 + sign_extend (m := 64) (0x008#12)).toNat (sdData_val (0#64)) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x80002a28#64)).mem
            (v10 + sign_extend (m := 64) (0x008#12)).toNat (sdData_val (0#64)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_new_at_80002a28 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80002a28#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x80002a28#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_store σ i u (0x80002a28#64) vminstret (0x00053423#32)
    (instruction.STORE (0x008#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80002a28#64)).mem
      (v10 + sign_extend (m := 64) (0x008#12)).toNat (sdData_val (0#64)))
    (0x23#8) (0x34#8) (0x05#8) (0x00#8)
    hG hpc hminstret w_00053423 nr_00053423
    (Vsa.Sim.DecodeTable.decode_00053423 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80002a28#64) (0x008#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0a#5)
      v10 (0#64) hG (rX_bits_x10 _ v10 hx10₂) (rX_bits_zero _) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80002a2c (`sd zero,16(a0)`): store 0 (8 bytes) @ `x10+16` (vals=NULL). -/
theorem site_80002a2c_env
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : Env_newLoaded σ.mem)
    (hpcv : pc = (0x80002a2c#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v10 + sign_extend (m := 64) (0x010#12)).toNat)
    (hahiram : (v10 + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (v10 + sign_extend (m := 64) (0x010#12)).toNat)
    (haalign : (v10 + sign_extend (m := 64) (0x010#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x80002a2c#64)).mem
        (v10 + sign_extend (m := 64) (0x010#12)).toNat (sdData_val (0#64)) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x80002a2c#64)).mem
            (v10 + sign_extend (m := 64) (0x010#12)).toNat (sdData_val (0#64)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_new_at_80002a2c hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80002a2c#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x80002a2c#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_store σ i u (0x80002a2c#64) vminstret (0x00053823#32)
    (instruction.STORE (0x010#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80002a2c#64)).mem
      (v10 + sign_extend (m := 64) (0x010#12)).toNat (sdData_val (0#64)))
    (0x23#8) (0x38#8) (0x05#8) (0x00#8)
    hG hpc hminstret w_00053823_env nr_00053823_env
    (Vsa.Sim.DecodeTable.decode_00053823 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80002a2c#64) (0x010#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0a#5)
      v10 (0#64) hG (rX_bits_x10 _ v10 hx10₂) (rX_bits_zero _) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80002a30 (`addi sp,sp,16`): `x2 := x2 + sext 0x010`. -/
theorem site_80002a30_env
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hmem : Env_newLoaded σ.mem)
    (hpcv : pc = (0x80002a30#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x2 (vsp + sign_extend (m := 64) (0x010#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_new_at_80002a30 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80002a30#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x80002a30#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x80002a30#64) vminstret (0x01010113#32)
    (instruction.ITYPE (0x010#12, regidx.Regidx 0x02#5, regidx.Regidx 0x02#5, iop.ADDI))
    Register.x2 (vsp + sign_extend (m := 64) (0x010#12)) (0x13#8) (0x01#8) (0x01#8) (0x01#8)
    hG hpc hminstret w_01010113_env nr_01010113_env
    (Vsa.Sim.DecodeTable.decode_01010113 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x010#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x02#5) vsp
      (afterNextPC (afterPrelude σ) (0x80002a30#64))
      (sigma3_alu σ (0x80002a30#64) Register.x2 (vsp + sign_extend (m := 64) (0x010#12)))
      (rX_bits_x2 _ vsp hx2₂) (wX_bits_x2 _ (vsp + sign_extend (m := 64) (0x010#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80002a34 (`ret`): PC → bit-0-cleared `x1`. -/
theorem site_80002a34_env
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vra : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some vra)
    (hmem : Env_newLoaded σ.mem)
    (hpcv : pc = (0x80002a34#64 : BitVec 64))
    (htgt : (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_new_at_80002a34 hmem
  have hx1₂ : (rX_bits (regidx.Regidx 0x01#5)).run (afterNextPC (afterPrelude σ) (0x80002a34#64))
      = .ok vra (afterNextPC (afterPrelude σ) (0x80002a34#64)) := by
    apply rX_bits_x1
    rw [get?_afterNextPC σ (0x80002a34#64) _ (by decide) (by decide)]; exact hx1
  exact stepObs_jr σ i u (0x80002a34#64) vminstret vra (0x00008067#32) (0x000#12)
    (regidx.Regidx 0x01#5) (0x67#8) (0x80#8) (0x00#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    nr_00008067 w_00008067
    (Vsa.Sim.DecodeTable.decode_00008067 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    hx1₂ htgt hi

end Vsa.Sim
