import Vsa.Sim.ValueEqualSites
import Vsa.Sim.DecodeTable.Batch16Part17
import Vsa.Sim.DecodeTable.Batch12Part21
import Vsa.Sim.DecodeTable.Batch05Part10
import Vsa.Sim.DecodeTable.Batch03Part17
import Vsa.Sim.DecodeTable.Batch02Part21
import Vsa.Sim.DecodeTable.Batch03Part21
import Vsa.Sim.DecodeTable.Batch03Part20
import Vsa.Sim.DecodeTable.Batch02Part23

/-!
# Layer 3 — per-site observational step lemmas for the `str`-`str` handler of `value_equal`

The `str` handler (`0x800028c4 … 0x800028e4`) is the only `value_equal` handler with a
stack footprint (it spills `ra`):

```
0x800028c4  ld a1,8(a1)      ; a1 := *(a1+8)  = string ptr b        (word 0x0085b583)
0x800028c8  ld a0,8(a0)      ; a0 := *(a0+8)  = string ptr a        (word 0x00853503)
0x800028cc  addi sp,sp,-16   ; sp := entry_sp - 16                  (word 0xff010113)
0x800028d0  sd ra,8(sp)      ; mem[sp+8 .. sp+16) := ra             (word 0x00113423)
0x800028d4  jal strcmp       ; ra := 0x800028d8; PC := 0x80006ea0   (word 0x5cc040ef)
0x800028d8  ld ra,8(sp)      ; ra := *(sp+8) (restore)              (word 0x00813083)
0x800028dc  seqz a0,a0       ; a0 := (a0 == 0) ? 1 : 0              (word 0x00153513)
0x800028e0  addi sp,sp,16    ; sp := entry_sp (restore)             (word 0x01010113)
0x800028e4  ret              ; PC := ra (= r)                       (reuse `site_ret_gen`)
```

The `sd ra,8(sp)` writes the stack slot at `(entry_sp-16)+8 = entry_sp-8`; the spill
survives the `strcmp` call (which does not touch that slot) and is restored by `ld ra`.

All byte facts for these addresses come from `Value_equalLoaded` (`value_equal_at_*`).
Site bodies mirror `EnvNewSites` (store / jal / ld) and `ValueEqualSites` (alu / seqz /
ret): the write / no-read side goals are discharged inline by `BitVec.eq_of_toNat_eq;
decide` and the decode by the generated `DecodeTable.decode_*` lemmas.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Site 0x800028c4 (`ld a1,8(a1)`): `x11 := sext (dword @ x11+8)`. -/
theorem site_800028c4
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbufb : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some vbufb)
    (hmem : Value_equalLoaded σ.mem)
    (hpcv : pc = (0x800028c4#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vbufb + sign_extend (m := 64) (0x008#12)).toNat)
    (hhiram : (vbufb + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vbufb + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbufb + sign_extend (m := 64) (0x008#12)).toNat)
    (halign : (vbufb + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0)
    (h0 : σ.mem[(vbufb + sign_extend (m := 64) (0x008#12)).toNat]? = some b0)
    (h1 : σ.mem[(vbufb + sign_extend (m := 64) (0x008#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(vbufb + sign_extend (m := 64) (0x008#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(vbufb + sign_extend (m := 64) (0x008#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(vbufb + sign_extend (m := 64) (0x008#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(vbufb + sign_extend (m := 64) (0x008#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(vbufb + sign_extend (m := 64) (0x008#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(vbufb + sign_extend (m := 64) (0x008#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x11
          (sign_extend (m := 64)
            ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
              : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_equal_at_800028c4 hmem
  have hx11₂ : (afterNextPC (afterPrelude σ) (0x800028c4#64)).regs.get? Register.x11 = some vbufb := by
    rw [get?_afterNextPC σ (0x800028c4#64) _ (by decide) (by decide)]; exact hx11
  exact stepObs_alu σ i u (0x800028c4#64) vminstret (0x0085b583#32)
    (instruction.LOAD (0x008#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0b#5, false, 8))
    Register.x11 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x83#8) (0xb5#8) (0x85#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_0085b583 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x800028c4#64) (0x008#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0b#5)
      (sigma3_alu σ (0x800028c4#64) Register.x11 (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      vbufb b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x11 _ vbufb hx11₂)
      (wX_bits_x11 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x800028c8 (`ld a0,8(a0)`): `x10 := sext (dword @ x10+8)`. -/
theorem site_800028c8
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbufa : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some vbufa)
    (hmem : Value_equalLoaded σ.mem)
    (hpcv : pc = (0x800028c8#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vbufa + sign_extend (m := 64) (0x008#12)).toNat)
    (hhiram : (vbufa + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vbufa + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbufa + sign_extend (m := 64) (0x008#12)).toNat)
    (halign : (vbufa + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0)
    (h0 : σ.mem[(vbufa + sign_extend (m := 64) (0x008#12)).toNat]? = some b0)
    (h1 : σ.mem[(vbufa + sign_extend (m := 64) (0x008#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(vbufa + sign_extend (m := 64) (0x008#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(vbufa + sign_extend (m := 64) (0x008#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(vbufa + sign_extend (m := 64) (0x008#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(vbufa + sign_extend (m := 64) (0x008#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(vbufa + sign_extend (m := 64) (0x008#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(vbufa + sign_extend (m := 64) (0x008#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10
          (sign_extend (m := 64)
            ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
              : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_equal_at_800028c8 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x800028c8#64)).regs.get? Register.x10 = some vbufa := by
    rw [get?_afterNextPC σ (0x800028c8#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_alu σ i u (0x800028c8#64) vminstret (0x00853503#32)
    (instruction.LOAD (0x008#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0a#5, false, 8))
    Register.x10 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x03#8) (0x35#8) (0x85#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00853503 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x800028c8#64) (0x008#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0a#5)
      (sigma3_alu σ (0x800028c8#64) Register.x10 (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      vbufa b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x10 _ vbufa hx10₂)
      (wX_bits_x10 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x800028cc (`addi sp,sp,-16`): `x2 := x2 + sext 0xff0`. -/
theorem site_800028cc
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hmem : Value_equalLoaded σ.mem)
    (hpcv : pc = (0x800028cc#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x2 (vsp + sign_extend (m := 64) (0xff0#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_equal_at_800028cc hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x800028cc#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x800028cc#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x800028cc#64) vminstret (0xff010113#32)
    (instruction.ITYPE (0xff0#12, regidx.Regidx 0x02#5, regidx.Regidx 0x02#5, iop.ADDI))
    Register.x2 (vsp + sign_extend (m := 64) (0xff0#12)) (0x13#8) (0x01#8) (0x01#8) (0xff#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_ff010113 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0xff0#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x02#5) vsp
      (afterNextPC (afterPrelude σ) (0x800028cc#64))
      (sigma3_alu σ (0x800028cc#64) Register.x2 (vsp + sign_extend (m := 64) (0xff0#12)))
      (rX_bits_x2 _ vsp hx2₂) (wX_bits_x2 _ (vsp + sign_extend (m := 64) (0xff0#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x800028d0 (`sd ra,8(sp)`): store `x1` (8 bytes) @ `x2+8`. -/
theorem site_800028d0
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp v1 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hx1 : σ.regs.get? Register.x1 = some v1)
    (hmem : Value_equalLoaded σ.mem)
    (hpcv : pc = (0x800028d0#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x008#12)).toNat)
    (hahiram : (vsp + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (vsp + sign_extend (m := 64) (0x008#12)).toNat)
    (haalign : (vsp + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x800028d0#64)).mem
        (vsp + sign_extend (m := 64) (0x008#12)).toNat (sdData_val v1) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x800028d0#64)).mem
            (vsp + sign_extend (m := 64) (0x008#12)).toNat (sdData_val v1))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_equal_at_800028d0 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x800028d0#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x800028d0#64) _ (by decide) (by decide)]; exact hx2
  have hx1₂ : (afterNextPC (afterPrelude σ) (0x800028d0#64)).regs.get? Register.x1 = some v1 := by
    rw [get?_afterNextPC σ (0x800028d0#64) _ (by decide) (by decide)]; exact hx1
  exact stepObs_store σ i u (0x800028d0#64) vminstret (0x00113423#32)
    (instruction.STORE (0x008#12, regidx.Regidx 0x01#5, regidx.Regidx 0x02#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x800028d0#64)).mem
      (vsp + sign_extend (m := 64) (0x008#12)).toNat (sdData_val v1))
    (0x23#8) (0x34#8) (0x11#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00113423 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x800028d0#64) (0x008#12) (regidx.Regidx 0x01#5) (regidx.Regidx 0x02#5)
      vsp v1 hG (rX_bits_x2 _ vsp hx2₂) (rX_bits_x1 _ v1 hx1₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x800028d4 (`jal strcmp`): `x1 := pc+4`, `PC := pc + sext 0x0045cc` = strcmp entry. -/
theorem site_800028d4
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Value_equalLoaded σ.mem)
    (hpcv : pc = (0x800028d4#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jal σ pc vminstret (0x0045cc#21) Register.x1 (BitVec.addInt pc 4)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_equal_at_800028d4 hmem
  exact stepObs_jal σ i u (0x800028d4#64) vminstret (0x5cc040ef#32) (0x0045cc#21)
    (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x800028d4#64) 4)
    (0xef#8) (0x40#8) (0xc0#8) (0x5c#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    (by decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_5cc040ef (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (wX_bits_x1 _ (BitVec.addInt (0x800028d4#64) 4)) hi

/-! ## Site 0x800028d8 (`ld ra,8(sp)`): ALU-class; `x1 := sext (dword @ x2+8)`. -/
theorem site_800028d8
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hmem : Value_equalLoaded σ.mem)
    (hpcv : pc = (0x800028d8#64 : BitVec 64))
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
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_equal_at_800028d8 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x800028d8#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x800028d8#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x800028d8#64) vminstret (0x00813083#32)
    (instruction.LOAD (0x008#12, regidx.Regidx 0x02#5, regidx.Regidx 0x01#5, false, 8))
    Register.x1
    (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x83#8) (0x30#8) (0x81#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00813083 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x800028d8#64) (0x008#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x01#5)
      (sigma3_alu σ (0x800028d8#64) Register.x1
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

/-! ## Site 0x800028dc (`seqz a0,a0`): `x10 := zext (a0 <ᵤ 1)` = `(a0 == 0) ? 1 : 0`. -/
theorem site_800028dc
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : Value_equalLoaded σ.mem)
    (hpcv : pc = (0x800028dc#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10
          (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v10 (sign_extend (m := 64) (0x001#12)))))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_equal_at_800028dc hmem
  exact stepObs_alu σ i u (0x800028dc#64) vminstret (0x00153513#32)
    (instruction.ITYPE (0x001#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0a#5, iop.SLTIU))
    Register.x10 (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v10 (sign_extend (m := 64) (0x001#12)))))
    (0x13#8) (0x35#8) (0x15#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00153513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_seqz_a0 σ (0x800028dc#64) v10 hx10)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x800028e0 (`addi sp,sp,16`): `x2 := x2 + sext 0x010`. -/
theorem site_800028e0
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hmem : Value_equalLoaded σ.mem)
    (hpcv : pc = (0x800028e0#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x2 (vsp + sign_extend (m := 64) (0x010#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := value_equal_at_800028e0 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x800028e0#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x800028e0#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x800028e0#64) vminstret (0x01010113#32)
    (instruction.ITYPE (0x010#12, regidx.Regidx 0x02#5, regidx.Regidx 0x02#5, iop.ADDI))
    Register.x2 (vsp + sign_extend (m := 64) (0x010#12)) (0x13#8) (0x01#8) (0x01#8) (0x01#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_01010113 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x010#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x02#5) vsp
      (afterNextPC (afterPrelude σ) (0x800028e0#64))
      (sigma3_alu σ (0x800028e0#64) Register.x2 (vsp + sign_extend (m := 64) (0x010#12)))
      (rX_bits_x2 _ vsp hx2₂) (wX_bits_x2 _ (vsp + sign_extend (m := 64) (0x010#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

end Vsa.Sim
