import Vsa.Sim.ValueSites
import Vsa.Sim.Code.__ssputs_r
import Vsa.Sim.DecodeTable.Batch16Part01
import Vsa.Sim.DecodeTable.Batch06Part31
import Vsa.Sim.DecodeTable.Batch04Part10
import Vsa.Sim.DecodeTable.Batch06Part30
import Vsa.Sim.DecodeTable.Batch06Part28
import Vsa.Sim.DecodeTable.Batch01Part19
import Vsa.Sim.DecodeTable.Batch01Part22
import Vsa.Sim.DecodeTable.Batch08Part01
import Vsa.Sim.DecodeTable.Batch01Part24
import Vsa.Sim.DecodeTable.Batch01Part13
import Vsa.Sim.DecodeTable.Batch01Part26
import Vsa.Sim.DecodeTable.Batch01Part29
import Vsa.Sim.DecodeTable.Batch01Part14
import Vsa.Sim.DecodeTable.Batch15Part04
import Vsa.Sim.DecodeTable.Batch04Part09
import Vsa.Sim.DecodeTable.Batch01Part01
import Vsa.Sim.DecodeTable.Batch11Part19
import Vsa.Sim.DecodeTable.Batch03Part29
import Vsa.Sim.DecodeTable.Batch04Part21
import Vsa.Sim.DecodeTable.Batch04Part30
import Vsa.Sim.DecodeTable.Batch07Part17
import Vsa.Sim.DecodeTable.Batch07Part07
import Vsa.Sim.DecodeTable.Batch07Part23
import Vsa.Sim.DecodeTable.Batch01Part04

/-!
# M3 Layer-3 — `SsputsSites` : per-site step battery for the `__ssputs_r` fast path (`_sp`)

Per-site `StepObs` lemmas for the `__ssputs_r` fast path (`0x8001438c …
0x800143f0`): prologue (frame setup, spills of `s0/s1/ra`), the `bgeu a3,s1`
dispatch (only the NOT-taken — fast-path — site is built), argument marshalling
into the `memmove` call at `0x800069c4`, and the post-call cursor/space update +
epilogue restore + `ret`.

```
  8001438c: addi sp,sp,-64
  80014390: sd   s1,40(sp)
  80014394: lw   s1,12(a1)      s1 := space left in the sink
  80014398: sd   s0,48(sp)
  8001439c: sd   ra,56(sp)
  800143a0: mv   s0,a1
  800143a4: mv   a5,a2
  800143a8: bgeu a3,s1,…        NOT taken on the fast path (len < space)
  800143ac: sext.w a4,a3
  800143b0: ld   a0,0(s0)       a0 := cursor
  800143b4: mv   s1,a4
  800143b8: mv   a1,a5
  800143bc: mv   a2,s1
  800143c0: jal  ra,0x800069c4  memmove(cursor, buf, len)
  800143c4: lw   a4,12(s0)      ┐ space -= len (32-bit)
  800143c8: ld   a5,0(s0)       │ cursor += len
  800143cc: li   a0,0           │
  800143d0: subw a4,a4,s1       │
  800143d4: add  a5,a5,s1       │
  800143d8: sw   a4,12(s0)      │
  800143dc: sd   a5,0(s0)       ┘
  800143e0: ld   ra,56(sp)      ┐ epilogue
  800143e4: ld   s0,48(sp)      │
  800143e8: ld   s1,40(sp)      │
  800143ec: addi sp,sp,64       │
  800143f0: ret                 ┘
```
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- 0x8001438c: `addi sp,sp,-64`. -/
theorem site_1438c_sp (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v2 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hmem : Vsa.Sim.Code.__ssputs_rLoaded σ.mem)
    (hpcv : pc = (0x8001438c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x2
        (v2 + sign_extend (m := 64) (0xfc0#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__ssputs_r_at_8001438c hmem
  exact stepObs_alu σ i u (0x8001438c#64) vminstret (0xfc010113#32)
    (instruction.ITYPE (0xfc0#12, regidx.Regidx 0x02#5, regidx.Regidx 0x02#5, iop.ADDI))
    Register.x2 (v2 + sign_extend (m := 64) (0xfc0#12))
    (0x13#8) (0x01#8) (0x01#8) (0xfc#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_fc010113 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0xfc0#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x02#5) v2
      (afterNextPC (afterPrelude σ) (0x8001438c#64))
      (sigma3_alu σ (0x8001438c#64) Register.x2 (v2 + sign_extend (m := 64) (0xfc0#12)))
      (rX_bits_x2 _ v2
        (by rw [get?_afterNextPC σ (0x8001438c#64) _ (by decide) (by decide)]; exact hx2))
      (wX_bits_x2 _ (v2 + sign_extend (m := 64) (0xfc0#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80014390: `sd s1,40(sp)`. -/
theorem site_14390_sp (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v2 v9 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hx9 : σ.regs.get? Register.x9 = some v9)
    (hmem : Vsa.Sim.Code.__ssputs_rLoaded σ.mem)
    (hpcv : pc = (0x80014390#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x028#12)).toNat)
    (hahiram : (v2 + sign_extend (m := 64) (0x028#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (v2 + sign_extend (m := 64) (0x028#12)).toNat)
    (haalign : (v2 + sign_extend (m := 64) (0x028#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x80014390#64)).mem
        (v2 + sign_extend (m := 64) (0x028#12)).toNat (sdData_val v9) ∧
      ReadsLikePost σ' (sigmaPost_store σ pc vminstret
        (writeMap8 (afterNextPC (afterPrelude σ) (0x80014390#64)).mem
          (v2 + sign_extend (m := 64) (0x028#12)).toNat (sdData_val v9))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__ssputs_r_at_80014390 hmem
  exact stepObs_store σ i u (0x80014390#64) vminstret (0x02913423#32)
    (instruction.STORE (0x028#12, regidx.Regidx 0x09#5, regidx.Regidx 0x02#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80014390#64)).mem
      (v2 + sign_extend (m := 64) (0x028#12)).toNat (sdData_val v9))
    (0x23#8) (0x34#8) (0x91#8) (0x02#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_02913423 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80014390#64) (0x028#12) (regidx.Regidx 0x09#5) (regidx.Regidx 0x02#5)
      v2 v9 hG
      (rX_bits_x2 _ v2
        (by rw [get?_afterNextPC σ (0x80014390#64) _ (by decide) (by decide)]; exact hx2))
      (rX_bits_x9 _ v9
        (by rw [get?_afterNextPC σ (0x80014390#64) _ (by decide) (by decide)]; exact hx9))
      halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80014394: `lw s1,12(a1)` (`s1 := space left in the sink`). -/
theorem site_14394_sp (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : Vsa.Sim.Code.__ssputs_rLoaded σ.mem)
    (hpcv : pc = (0x80014394#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v11 + sign_extend (m := 64) (0x00c#12)).toNat)
    (hhiram : (v11 + sign_extend (m := 64) (0x00c#12)).toNat + 4 ≤ 0x100000000)
    (hhtif : (v11 + sign_extend (m := 64) (0x00c#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v11 + sign_extend (m := 64) (0x00c#12)).toNat)
    (halign : (v11 + sign_extend (m := 64) (0x00c#12)).toNat % 4 = 0)
    (h0 : σ.mem[(v11 + sign_extend (m := 64) (0x00c#12)).toNat]? = some b0)
    (h1 : σ.mem[(v11 + sign_extend (m := 64) (0x00c#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(v11 + sign_extend (m := 64) (0x00c#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(v11 + sign_extend (m := 64) (0x00c#12)).toNat + 3]? = some b3) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x9
        (sign_extend (m := 64)
          ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__ssputs_r_at_80014394 hmem
  exact stepObs_alu σ i u (0x80014394#64) vminstret (0x00c5a483#32)
    (instruction.LOAD (0x00c#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x09#5, false, 4))
    Register.x9 (sign_extend (m := 64)
      ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)))
    (0x83#8) (0xa4#8) (0xc5#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00c5a483 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lw σ (0x80014394#64) (0x00c#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x09#5)
      (sigma3_alu σ (0x80014394#64) Register.x9
        (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4))))
      v11 b0 b1 b2 b3 hG
      (rX_bits_x11 _ v11
        (by rw [get?_afterNextPC σ (0x80014394#64) _ (by decide) (by decide)]; exact hx11))
      (wX_bits_x9 _ (sign_extend (m := 64)
        ((((b3.append b2).append b1).append b0) : BitVec (8 * 4))))
      hlo hhiram hhtif halign h0 h1 h2 h3)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80014398: `sd s0,48(sp)`. -/
theorem site_14398_sp (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v2 v8 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hx8 : σ.regs.get? Register.x8 = some v8)
    (hmem : Vsa.Sim.Code.__ssputs_rLoaded σ.mem)
    (hpcv : pc = (0x80014398#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x030#12)).toNat)
    (hahiram : (v2 + sign_extend (m := 64) (0x030#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (v2 + sign_extend (m := 64) (0x030#12)).toNat)
    (haalign : (v2 + sign_extend (m := 64) (0x030#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x80014398#64)).mem
        (v2 + sign_extend (m := 64) (0x030#12)).toNat (sdData_val v8) ∧
      ReadsLikePost σ' (sigmaPost_store σ pc vminstret
        (writeMap8 (afterNextPC (afterPrelude σ) (0x80014398#64)).mem
          (v2 + sign_extend (m := 64) (0x030#12)).toNat (sdData_val v8))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__ssputs_r_at_80014398 hmem
  exact stepObs_store σ i u (0x80014398#64) vminstret (0x02813823#32)
    (instruction.STORE (0x030#12, regidx.Regidx 0x08#5, regidx.Regidx 0x02#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80014398#64)).mem
      (v2 + sign_extend (m := 64) (0x030#12)).toNat (sdData_val v8))
    (0x23#8) (0x38#8) (0x81#8) (0x02#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_02813823 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80014398#64) (0x030#12) (regidx.Regidx 0x08#5) (regidx.Regidx 0x02#5)
      v2 v8 hG
      (rX_bits_x2 _ v2
        (by rw [get?_afterNextPC σ (0x80014398#64) _ (by decide) (by decide)]; exact hx2))
      (rX_bits_x8 _ v8
        (by rw [get?_afterNextPC σ (0x80014398#64) _ (by decide) (by decide)]; exact hx8))
      halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x8001439c: `sd ra,56(sp)`. -/
theorem site_1439c_sp (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v2 v1 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hx1 : σ.regs.get? Register.x1 = some v1)
    (hmem : Vsa.Sim.Code.__ssputs_rLoaded σ.mem)
    (hpcv : pc = (0x8001439c#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x038#12)).toNat)
    (hahiram : (v2 + sign_extend (m := 64) (0x038#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (v2 + sign_extend (m := 64) (0x038#12)).toNat)
    (haalign : (v2 + sign_extend (m := 64) (0x038#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x8001439c#64)).mem
        (v2 + sign_extend (m := 64) (0x038#12)).toNat (sdData_val v1) ∧
      ReadsLikePost σ' (sigmaPost_store σ pc vminstret
        (writeMap8 (afterNextPC (afterPrelude σ) (0x8001439c#64)).mem
          (v2 + sign_extend (m := 64) (0x038#12)).toNat (sdData_val v1))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__ssputs_r_at_8001439c hmem
  exact stepObs_store σ i u (0x8001439c#64) vminstret (0x02113c23#32)
    (instruction.STORE (0x038#12, regidx.Regidx 0x01#5, regidx.Regidx 0x02#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x8001439c#64)).mem
      (v2 + sign_extend (m := 64) (0x038#12)).toNat (sdData_val v1))
    (0x23#8) (0x3c#8) (0x11#8) (0x02#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_02113c23 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x8001439c#64) (0x038#12) (regidx.Regidx 0x01#5) (regidx.Regidx 0x02#5)
      v2 v1 hG
      (rX_bits_x2 _ v2
        (by rw [get?_afterNextPC σ (0x8001439c#64) _ (by decide) (by decide)]; exact hx2))
      (rX_bits_x1 _ v1
        (by rw [get?_afterNextPC σ (0x8001439c#64) _ (by decide) (by decide)]; exact hx1))
      halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800143a0: `mv s0,a1`. -/
theorem site_143a0_sp (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : Vsa.Sim.Code.__ssputs_rLoaded σ.mem)
    (hpcv : pc = (0x800143a0#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x8
        (v11 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__ssputs_r_at_800143a0 hmem
  exact stepObs_alu σ i u (0x800143a0#64) vminstret (0x00058413#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x08#5, iop.ADDI))
    Register.x8 (v11 + sign_extend (m := 64) (0x000#12))
    (0x13#8) (0x84#8) (0x05#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00058413 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x08#5) v11
      (afterNextPC (afterPrelude σ) (0x800143a0#64))
      (sigma3_alu σ (0x800143a0#64) Register.x8 (v11 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x11 _ v11
        (by rw [get?_afterNextPC σ (0x800143a0#64) _ (by decide) (by decide)]; exact hx11))
      (wX_bits_x8 _ (v11 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800143a4: `mv a5,a2`. -/
theorem site_143a4_sp (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : Vsa.Sim.Code.__ssputs_rLoaded σ.mem)
    (hpcv : pc = (0x800143a4#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15
        (v12 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__ssputs_r_at_800143a4 hmem
  exact stepObs_alu σ i u (0x800143a4#64) vminstret (0x00060793#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x0c#5, regidx.Regidx 0x0f#5, iop.ADDI))
    Register.x15 (v12 + sign_extend (m := 64) (0x000#12))
    (0x93#8) (0x07#8) (0x06#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00060793 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0f#5) v12
      (afterNextPC (afterPrelude σ) (0x800143a4#64))
      (sigma3_alu σ (0x800143a4#64) Register.x15 (v12 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x12 _ v12
        (by rw [get?_afterNextPC σ (0x800143a4#64) _ (by decide) (by decide)]; exact hx12))
      (wX_bits_x15 _ (v12 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800143a8: `bgeu a3,s1 → 0x800143f4` (NOT taken: `len <ᵤ space`, the fast path). -/
theorem site_143a8_sp (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v13 v9 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hx9 : σ.regs.get? Register.x9 = some v9)
    (hmem : Vsa.Sim.Code.__ssputs_rLoaded σ.mem)
    (hpcv : pc = (0x800143a8#64 : BitVec 64))
    (hv : zopz0zKzJ_u v13 v9 = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__ssputs_r_at_800143a8 hmem
  exact stepObs_branch_nottaken σ i u (0x800143a8#64) vminstret (0x004c#13)
    (regidx.Regidx 0x0d#5) (regidx.Regidx 0x09#5) bop.BGEU (0x0496f663#32)
    (0x63#8) (0xf6#8) (0x96#8) (0x04#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_0496f663 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_btype_bgeu_nottaken (0x004c#13) (regidx.Regidx 0x0d#5) (regidx.Regidx 0x09#5)
      v13 v9 (afterNextPC (afterPrelude σ) (0x800143a8#64))
      (rX_bits_x13 _ v13
        (by rw [get?_afterNextPC σ (0x800143a8#64) _ (by decide) (by decide)]; exact hx13))
      (rX_bits_x9 _ v9
        (by rw [get?_afterNextPC σ (0x800143a8#64) _ (by decide) (by decide)]; exact hx9))
      hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800143ac: `sext.w a4,a3` (`addiw a4,a3,0`). -/
theorem site_143ac_sp (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : Vsa.Sim.Code.__ssputs_rLoaded σ.mem)
    (hpcv : pc = (0x800143ac#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x14
        (sign_extend (m := 64)
          (Sail.BitVec.extractLsb (v13 + sign_extend (m := 64) (0x000#12)) 31 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__ssputs_r_at_800143ac hmem
  exact stepObs_alu σ i u (0x800143ac#64) vminstret (0x0006871b#32)
    (instruction.ADDIW (0x000#12, regidx.Regidx 0x0d#5, regidx.Regidx 0x0e#5))
    Register.x14 (sign_extend (m := 64)
      (Sail.BitVec.extractLsb (v13 + sign_extend (m := 64) (0x000#12)) 31 0))
    (0x1b#8) (0x87#8) (0x06#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_0006871b (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_addiw_char (0x000#12) (regidx.Regidx 0x0d#5) (regidx.Regidx 0x0e#5) v13
      (afterNextPC (afterPrelude σ) (0x800143ac#64))
      (sigma3_alu σ (0x800143ac#64) Register.x14
        (sign_extend (m := 64)
          (Sail.BitVec.extractLsb (v13 + sign_extend (m := 64) (0x000#12)) 31 0)))
      (rX_bits_x13 _ v13
        (by rw [get?_afterNextPC σ (0x800143ac#64) _ (by decide) (by decide)]; exact hx13))
      (wX_bits_x14 _ (sign_extend (m := 64)
        (Sail.BitVec.extractLsb (v13 + sign_extend (m := 64) (0x000#12)) 31 0))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800143b0: `ld a0,0(s0)` (`a0 := cursor`). -/
theorem site_143b0_sp (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v8 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx8 : σ.regs.get? Register.x8 = some v8)
    (hmem : Vsa.Sim.Code.__ssputs_rLoaded σ.mem)
    (hpcv : pc = (0x800143b0#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v8 + sign_extend (m := 64) (0x000#12)).toNat)
    (hhiram : (v8 + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v8 + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v8 + sign_extend (m := 64) (0x000#12)).toNat)
    (halign : (v8 + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0)
    (h0 : σ.mem[(v8 + sign_extend (m := 64) (0x000#12)).toNat]? = some b0)
    (h1 : σ.mem[(v8 + sign_extend (m := 64) (0x000#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(v8 + sign_extend (m := 64) (0x000#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(v8 + sign_extend (m := 64) (0x000#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(v8 + sign_extend (m := 64) (0x000#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(v8 + sign_extend (m := 64) (0x000#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(v8 + sign_extend (m := 64) (0x000#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(v8 + sign_extend (m := 64) (0x000#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x10
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__ssputs_r_at_800143b0 hmem
  exact stepObs_alu σ i u (0x800143b0#64) vminstret (0x00043503#32)
    (instruction.LOAD (0x000#12, regidx.Regidx 0x08#5, regidx.Regidx 0x0a#5, false, 8))
    Register.x10 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x03#8) (0x35#8) (0x04#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00043503 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x800143b0#64) (0x000#12) (regidx.Regidx 0x08#5) (regidx.Regidx 0x0a#5)
      (sigma3_alu σ (0x800143b0#64) Register.x10
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      v8 b0 b1 b2 b3 b4 b5 b6 b7 hG
      (rX_bits_x8 _ v8
        (by rw [get?_afterNextPC σ (0x800143b0#64) _ (by decide) (by decide)]; exact hx8))
      (wX_bits_x10 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800143b4: `mv s1,a4`. -/
theorem site_143b4_sp (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : Vsa.Sim.Code.__ssputs_rLoaded σ.mem)
    (hpcv : pc = (0x800143b4#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x9
        (v14 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__ssputs_r_at_800143b4 hmem
  exact stepObs_alu σ i u (0x800143b4#64) vminstret (0x00070493#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x09#5, iop.ADDI))
    Register.x9 (v14 + sign_extend (m := 64) (0x000#12))
    (0x93#8) (0x04#8) (0x07#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00070493 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x09#5) v14
      (afterNextPC (afterPrelude σ) (0x800143b4#64))
      (sigma3_alu σ (0x800143b4#64) Register.x9 (v14 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x14 _ v14
        (by rw [get?_afterNextPC σ (0x800143b4#64) _ (by decide) (by decide)]; exact hx14))
      (wX_bits_x9 _ (v14 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800143b8: `mv a1,a5`. -/
theorem site_143b8_sp (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : Vsa.Sim.Code.__ssputs_rLoaded σ.mem)
    (hpcv : pc = (0x800143b8#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x11
        (v15 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__ssputs_r_at_800143b8 hmem
  exact stepObs_alu σ i u (0x800143b8#64) vminstret (0x00078593#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x0b#5, iop.ADDI))
    Register.x11 (v15 + sign_extend (m := 64) (0x000#12))
    (0x93#8) (0x85#8) (0x07#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00078593 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0b#5) v15
      (afterNextPC (afterPrelude σ) (0x800143b8#64))
      (sigma3_alu σ (0x800143b8#64) Register.x11 (v15 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x15 _ v15
        (by rw [get?_afterNextPC σ (0x800143b8#64) _ (by decide) (by decide)]; exact hx15))
      (wX_bits_x11 _ (v15 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800143bc: `mv a2,s1`. -/
theorem site_143bc_sp (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v9 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx9 : σ.regs.get? Register.x9 = some v9)
    (hmem : Vsa.Sim.Code.__ssputs_rLoaded σ.mem)
    (hpcv : pc = (0x800143bc#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x12
        (v9 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__ssputs_r_at_800143bc hmem
  exact stepObs_alu σ i u (0x800143bc#64) vminstret (0x00048613#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x09#5, regidx.Regidx 0x0c#5, iop.ADDI))
    Register.x12 (v9 + sign_extend (m := 64) (0x000#12))
    (0x13#8) (0x86#8) (0x04#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00048613 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x09#5) (regidx.Regidx 0x0c#5) v9
      (afterNextPC (afterPrelude σ) (0x800143bc#64))
      (sigma3_alu σ (0x800143bc#64) Register.x12 (v9 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x9 _ v9
        (by rw [get?_afterNextPC σ (0x800143bc#64) _ (by decide) (by decide)]; exact hx9))
      (wX_bits_x12 _ (v9 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800143c0: `jal ra,0x800069c4` (call `memmove`; link `ra := 0x800143c4`). -/
theorem site_143c0_sp (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Vsa.Sim.Code.__ssputs_rLoaded σ.mem)
    (hpcv : pc = (0x800143c0#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jal σ pc vminstret (0x1f2604#21) Register.x1 (BitVec.addInt pc 4)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__ssputs_r_at_800143c0 hmem
  refine stepObs_jal σ i u (0x800143c0#64) vminstret (0xe04f20ef#32) (0x1f2604#21)
    (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x800143c0#64) 4)
    (0xef#8) (0x20#8) (0x4f#8) (0xe0#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_e04f20ef (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) ?_ hi
  exact wX_bits_x1 _ (BitVec.addInt (0x800143c0#64) 4)

/-- 0x800143c4: `lw a4,12(s0)` (reload the space counter). -/
theorem site_143c4_sp (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v8 : BitVec 64)
    (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx8 : σ.regs.get? Register.x8 = some v8)
    (hmem : Vsa.Sim.Code.__ssputs_rLoaded σ.mem)
    (hpcv : pc = (0x800143c4#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v8 + sign_extend (m := 64) (0x00c#12)).toNat)
    (hhiram : (v8 + sign_extend (m := 64) (0x00c#12)).toNat + 4 ≤ 0x100000000)
    (hhtif : (v8 + sign_extend (m := 64) (0x00c#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v8 + sign_extend (m := 64) (0x00c#12)).toNat)
    (halign : (v8 + sign_extend (m := 64) (0x00c#12)).toNat % 4 = 0)
    (h0 : σ.mem[(v8 + sign_extend (m := 64) (0x00c#12)).toNat]? = some b0)
    (h1 : σ.mem[(v8 + sign_extend (m := 64) (0x00c#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(v8 + sign_extend (m := 64) (0x00c#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(v8 + sign_extend (m := 64) (0x00c#12)).toNat + 3]? = some b3) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x14
        (sign_extend (m := 64)
          ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__ssputs_r_at_800143c4 hmem
  exact stepObs_alu σ i u (0x800143c4#64) vminstret (0x00c42703#32)
    (instruction.LOAD (0x00c#12, regidx.Regidx 0x08#5, regidx.Regidx 0x0e#5, false, 4))
    Register.x14 (sign_extend (m := 64)
      ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)))
    (0x03#8) (0x27#8) (0xc4#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00c42703 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lw σ (0x800143c4#64) (0x00c#12) (regidx.Regidx 0x08#5) (regidx.Regidx 0x0e#5)
      (sigma3_alu σ (0x800143c4#64) Register.x14
        (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4))))
      v8 b0 b1 b2 b3 hG
      (rX_bits_x8 _ v8
        (by rw [get?_afterNextPC σ (0x800143c4#64) _ (by decide) (by decide)]; exact hx8))
      (wX_bits_x14 _ (sign_extend (m := 64)
        ((((b3.append b2).append b1).append b0) : BitVec (8 * 4))))
      hlo hhiram hhtif halign h0 h1 h2 h3)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800143c8: `ld a5,0(s0)` (reload the cursor). -/
theorem site_143c8_sp (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v8 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx8 : σ.regs.get? Register.x8 = some v8)
    (hmem : Vsa.Sim.Code.__ssputs_rLoaded σ.mem)
    (hpcv : pc = (0x800143c8#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v8 + sign_extend (m := 64) (0x000#12)).toNat)
    (hhiram : (v8 + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v8 + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v8 + sign_extend (m := 64) (0x000#12)).toNat)
    (halign : (v8 + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0)
    (h0 : σ.mem[(v8 + sign_extend (m := 64) (0x000#12)).toNat]? = some b0)
    (h1 : σ.mem[(v8 + sign_extend (m := 64) (0x000#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(v8 + sign_extend (m := 64) (0x000#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(v8 + sign_extend (m := 64) (0x000#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(v8 + sign_extend (m := 64) (0x000#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(v8 + sign_extend (m := 64) (0x000#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(v8 + sign_extend (m := 64) (0x000#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(v8 + sign_extend (m := 64) (0x000#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__ssputs_r_at_800143c8 hmem
  exact stepObs_alu σ i u (0x800143c8#64) vminstret (0x00043783#32)
    (instruction.LOAD (0x000#12, regidx.Regidx 0x08#5, regidx.Regidx 0x0f#5, false, 8))
    Register.x15 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x83#8) (0x37#8) (0x04#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00043783 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x800143c8#64) (0x000#12) (regidx.Regidx 0x08#5) (regidx.Regidx 0x0f#5)
      (sigma3_alu σ (0x800143c8#64) Register.x15
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      v8 b0 b1 b2 b3 b4 b5 b6 b7 hG
      (rX_bits_x8 _ v8
        (by rw [get?_afterNextPC σ (0x800143c8#64) _ (by decide) (by decide)]; exact hx8))
      (wX_bits_x15 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800143cc: `li a0,0` (the `__ssputs_r` success return value). -/
theorem site_143cc_sp (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Vsa.Sim.Code.__ssputs_rLoaded σ.mem)
    (hpcv : pc = (0x800143cc#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x10
        ((0#64) + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__ssputs_r_at_800143cc hmem
  exact stepObs_alu σ i u (0x800143cc#64) vminstret (0x00000513#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 ((0#64) + sign_extend (m := 64) (0x000#12))
    (0x13#8) (0x05#8) (0x00#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00000513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0a#5) (0#64)
      (afterNextPC (afterPrelude σ) (0x800143cc#64))
      (sigma3_alu σ (0x800143cc#64) Register.x10 ((0#64) + sign_extend (m := 64) (0x000#12)))
      (rX_bits_zero _) (wX_bits_x10 _ ((0#64) + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800143d0: `subw a4,a4,s1` (`space -= len`, 32-bit). -/
theorem site_143d0_sp (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 v9 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hx9 : σ.regs.get? Register.x9 = some v9)
    (hmem : Vsa.Sim.Code.__ssputs_rLoaded σ.mem)
    (hpcv : pc = (0x800143d0#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x14
        (sign_extend (m := 64)
          ((Sail.BitVec.extractLsb v14 31 0) - (Sail.BitVec.extractLsb v9 31 0)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__ssputs_r_at_800143d0 hmem
  exact stepObs_alu σ i u (0x800143d0#64) vminstret (0x4097073b#32)
    (instruction.RTYPEW (regidx.Regidx 0x09#5, regidx.Regidx 0x0e#5, regidx.Regidx 0x0e#5, ropw.SUBW))
    Register.x14 (sign_extend (m := 64)
      ((Sail.BitVec.extractLsb v14 31 0) - (Sail.BitVec.extractLsb v9 31 0)))
    (0x3b#8) (0x07#8) (0x97#8) (0x40#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_4097073b (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_rtypew_subw_char (regidx.Regidx 0x09#5) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0e#5)
      v14 v9 (afterNextPC (afterPrelude σ) (0x800143d0#64))
      (sigma3_alu σ (0x800143d0#64) Register.x14
        (sign_extend (m := 64)
          ((Sail.BitVec.extractLsb v14 31 0) - (Sail.BitVec.extractLsb v9 31 0))))
      (rX_bits_x14 _ v14
        (by rw [get?_afterNextPC σ (0x800143d0#64) _ (by decide) (by decide)]; exact hx14))
      (rX_bits_x9 _ v9
        (by rw [get?_afterNextPC σ (0x800143d0#64) _ (by decide) (by decide)]; exact hx9))
      (wX_bits_x14 _ (sign_extend (m := 64)
        ((Sail.BitVec.extractLsb v14 31 0) - (Sail.BitVec.extractLsb v9 31 0)))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800143d4: `add a5,a5,s1` (`cursor += len`). -/
theorem site_143d4_sp (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 v9 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hx9 : σ.regs.get? Register.x9 = some v9)
    (hmem : Vsa.Sim.Code.__ssputs_rLoaded σ.mem)
    (hpcv : pc = (0x800143d4#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (v15 + v9)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__ssputs_r_at_800143d4 hmem
  exact stepObs_alu σ i u (0x800143d4#64) vminstret (0x009787b3#32)
    (instruction.RTYPE (regidx.Regidx 0x09#5, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, rop.ADD))
    Register.x15 (v15 + v9)
    (0xb3#8) (0x87#8) (0x97#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_009787b3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_rtype_add_char (regidx.Regidx 0x09#5) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5)
      v15 v9 (afterNextPC (afterPrelude σ) (0x800143d4#64))
      (sigma3_alu σ (0x800143d4#64) Register.x15 (v15 + v9))
      (rX_bits_x15 _ v15
        (by rw [get?_afterNextPC σ (0x800143d4#64) _ (by decide) (by decide)]; exact hx15))
      (rX_bits_x9 _ v9
        (by rw [get?_afterNextPC σ (0x800143d4#64) _ (by decide) (by decide)]; exact hx9))
      (wX_bits_x15 _ (v15 + v9)))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800143d8: `sw a4,12(s0)` (store the updated space counter). -/
theorem site_143d8_sp (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v8 v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx8 : σ.regs.get? Register.x8 = some v8)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : Vsa.Sim.Code.__ssputs_rLoaded σ.mem)
    (hpcv : pc = (0x800143d8#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v8 + sign_extend (m := 64) (0x00c#12)).toNat)
    (hahiram : (v8 + sign_extend (m := 64) (0x00c#12)).toNat + 4 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (v8 + sign_extend (m := 64) (0x00c#12)).toNat)
    (haalign : (v8 + sign_extend (m := 64) (0x00c#12)).toNat % 4 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap4 (afterNextPC (afterPrelude σ) (0x800143d8#64)).mem
        (v8 + sign_extend (m := 64) (0x00c#12)).toNat (swData v14) ∧
      ReadsLikePost σ' (sigmaPost_store σ pc vminstret
        (writeMap4 (afterNextPC (afterPrelude σ) (0x800143d8#64)).mem
          (v8 + sign_extend (m := 64) (0x00c#12)).toNat (swData v14))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__ssputs_r_at_800143d8 hmem
  exact stepObs_store σ i u (0x800143d8#64) vminstret (0x00e42623#32)
    (instruction.STORE (0x00c#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x08#5, 4))
    (writeMap4 (afterNextPC (afterPrelude σ) (0x800143d8#64)).mem
      (v8 + sign_extend (m := 64) (0x00c#12)).toNat (swData v14))
    (0x23#8) (0x26#8) (0xe4#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00e42623 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sw σ (0x800143d8#64) (0x00c#12) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x08#5)
      v8 v14 hG
      (rX_bits_x8 _ v8
        (by rw [get?_afterNextPC σ (0x800143d8#64) _ (by decide) (by decide)]; exact hx8))
      (rX_bits_x14 _ v14
        (by rw [get?_afterNextPC σ (0x800143d8#64) _ (by decide) (by decide)]; exact hx14))
      halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800143dc: `sd a5,0(s0)` (store the advanced cursor). -/
theorem site_143dc_sp (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v8 v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx8 : σ.regs.get? Register.x8 = some v8)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : Vsa.Sim.Code.__ssputs_rLoaded σ.mem)
    (hpcv : pc = (0x800143dc#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v8 + sign_extend (m := 64) (0x000#12)).toNat)
    (hahiram : (v8 + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (v8 + sign_extend (m := 64) (0x000#12)).toNat)
    (haalign : (v8 + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x800143dc#64)).mem
        (v8 + sign_extend (m := 64) (0x000#12)).toNat (sdData_val v15) ∧
      ReadsLikePost σ' (sigmaPost_store σ pc vminstret
        (writeMap8 (afterNextPC (afterPrelude σ) (0x800143dc#64)).mem
          (v8 + sign_extend (m := 64) (0x000#12)).toNat (sdData_val v15))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__ssputs_r_at_800143dc hmem
  exact stepObs_store σ i u (0x800143dc#64) vminstret (0x00f43023#32)
    (instruction.STORE (0x000#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x08#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x800143dc#64)).mem
      (v8 + sign_extend (m := 64) (0x000#12)).toNat (sdData_val v15))
    (0x23#8) (0x30#8) (0xf4#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00f43023 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x800143dc#64) (0x000#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x08#5)
      v8 v15 hG
      (rX_bits_x8 _ v8
        (by rw [get?_afterNextPC σ (0x800143dc#64) _ (by decide) (by decide)]; exact hx8))
      (rX_bits_x15 _ v15
        (by rw [get?_afterNextPC σ (0x800143dc#64) _ (by decide) (by decide)]; exact hx15))
      halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800143e0: `ld ra,56(sp)` (restore the return address). -/
theorem site_143e0_sp (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v2 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hmem : Vsa.Sim.Code.__ssputs_rLoaded σ.mem)
    (hpcv : pc = (0x800143e0#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x038#12)).toNat)
    (hhiram : (v2 + sign_extend (m := 64) (0x038#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v2 + sign_extend (m := 64) (0x038#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v2 + sign_extend (m := 64) (0x038#12)).toNat)
    (halign : (v2 + sign_extend (m := 64) (0x038#12)).toNat % 8 = 0)
    (h0 : σ.mem[(v2 + sign_extend (m := 64) (0x038#12)).toNat]? = some b0)
    (h1 : σ.mem[(v2 + sign_extend (m := 64) (0x038#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(v2 + sign_extend (m := 64) (0x038#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(v2 + sign_extend (m := 64) (0x038#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(v2 + sign_extend (m := 64) (0x038#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(v2 + sign_extend (m := 64) (0x038#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(v2 + sign_extend (m := 64) (0x038#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(v2 + sign_extend (m := 64) (0x038#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x1
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__ssputs_r_at_800143e0 hmem
  exact stepObs_alu σ i u (0x800143e0#64) vminstret (0x03813083#32)
    (instruction.LOAD (0x038#12, regidx.Regidx 0x02#5, regidx.Regidx 0x01#5, false, 8))
    Register.x1 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x83#8) (0x30#8) (0x81#8) (0x03#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_03813083 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x800143e0#64) (0x038#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x01#5)
      (sigma3_alu σ (0x800143e0#64) Register.x1
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      v2 b0 b1 b2 b3 b4 b5 b6 b7 hG
      (rX_bits_x2 _ v2
        (by rw [get?_afterNextPC σ (0x800143e0#64) _ (by decide) (by decide)]; exact hx2))
      (wX_bits_x1 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800143e4: `ld s0,48(sp)` (restore `s0`). -/
theorem site_143e4_sp (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v2 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hmem : Vsa.Sim.Code.__ssputs_rLoaded σ.mem)
    (hpcv : pc = (0x800143e4#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x030#12)).toNat)
    (hhiram : (v2 + sign_extend (m := 64) (0x030#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v2 + sign_extend (m := 64) (0x030#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v2 + sign_extend (m := 64) (0x030#12)).toNat)
    (halign : (v2 + sign_extend (m := 64) (0x030#12)).toNat % 8 = 0)
    (h0 : σ.mem[(v2 + sign_extend (m := 64) (0x030#12)).toNat]? = some b0)
    (h1 : σ.mem[(v2 + sign_extend (m := 64) (0x030#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(v2 + sign_extend (m := 64) (0x030#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(v2 + sign_extend (m := 64) (0x030#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(v2 + sign_extend (m := 64) (0x030#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(v2 + sign_extend (m := 64) (0x030#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(v2 + sign_extend (m := 64) (0x030#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(v2 + sign_extend (m := 64) (0x030#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x8
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__ssputs_r_at_800143e4 hmem
  exact stepObs_alu σ i u (0x800143e4#64) vminstret (0x03013403#32)
    (instruction.LOAD (0x030#12, regidx.Regidx 0x02#5, regidx.Regidx 0x08#5, false, 8))
    Register.x8 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x03#8) (0x34#8) (0x01#8) (0x03#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_03013403 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x800143e4#64) (0x030#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x08#5)
      (sigma3_alu σ (0x800143e4#64) Register.x8
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      v2 b0 b1 b2 b3 b4 b5 b6 b7 hG
      (rX_bits_x2 _ v2
        (by rw [get?_afterNextPC σ (0x800143e4#64) _ (by decide) (by decide)]; exact hx2))
      (wX_bits_x8 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800143e8: `ld s1,40(sp)` (restore `s1`). -/
theorem site_143e8_sp (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v2 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hmem : Vsa.Sim.Code.__ssputs_rLoaded σ.mem)
    (hpcv : pc = (0x800143e8#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x028#12)).toNat)
    (hhiram : (v2 + sign_extend (m := 64) (0x028#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v2 + sign_extend (m := 64) (0x028#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v2 + sign_extend (m := 64) (0x028#12)).toNat)
    (halign : (v2 + sign_extend (m := 64) (0x028#12)).toNat % 8 = 0)
    (h0 : σ.mem[(v2 + sign_extend (m := 64) (0x028#12)).toNat]? = some b0)
    (h1 : σ.mem[(v2 + sign_extend (m := 64) (0x028#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(v2 + sign_extend (m := 64) (0x028#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(v2 + sign_extend (m := 64) (0x028#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(v2 + sign_extend (m := 64) (0x028#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(v2 + sign_extend (m := 64) (0x028#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(v2 + sign_extend (m := 64) (0x028#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(v2 + sign_extend (m := 64) (0x028#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x9
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__ssputs_r_at_800143e8 hmem
  exact stepObs_alu σ i u (0x800143e8#64) vminstret (0x02813483#32)
    (instruction.LOAD (0x028#12, regidx.Regidx 0x02#5, regidx.Regidx 0x09#5, false, 8))
    Register.x9 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x83#8) (0x34#8) (0x81#8) (0x02#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_02813483 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x800143e8#64) (0x028#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x09#5)
      (sigma3_alu σ (0x800143e8#64) Register.x9
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      v2 b0 b1 b2 b3 b4 b5 b6 b7 hG
      (rX_bits_x2 _ v2
        (by rw [get?_afterNextPC σ (0x800143e8#64) _ (by decide) (by decide)]; exact hx2))
      (wX_bits_x9 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800143ec: `addi sp,sp,64`. -/
theorem site_143ec_sp (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v2 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hmem : Vsa.Sim.Code.__ssputs_rLoaded σ.mem)
    (hpcv : pc = (0x800143ec#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x2
        (v2 + sign_extend (m := 64) (0x040#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__ssputs_r_at_800143ec hmem
  exact stepObs_alu σ i u (0x800143ec#64) vminstret (0x04010113#32)
    (instruction.ITYPE (0x040#12, regidx.Regidx 0x02#5, regidx.Regidx 0x02#5, iop.ADDI))
    Register.x2 (v2 + sign_extend (m := 64) (0x040#12))
    (0x13#8) (0x01#8) (0x01#8) (0x04#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_04010113 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x040#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x02#5) v2
      (afterNextPC (afterPrelude σ) (0x800143ec#64))
      (sigma3_alu σ (0x800143ec#64) Register.x2 (v2 + sign_extend (m := 64) (0x040#12)))
      (rX_bits_x2 _ v2
        (by rw [get?_afterNextPC σ (0x800143ec#64) _ (by decide) (by decide)]; exact hx2))
      (wX_bits_x2 _ (v2 + sign_extend (m := 64) (0x040#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800143f0: `ret`. -/
theorem site_143f0_sp (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vr : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some vr)
    (hmem : Vsa.Sim.Code.__ssputs_rLoaded σ.mem)
    (hpcv : pc = (0x800143f0#64 : BitVec 64))
    (htgt : (BitVec.update (vr + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret
          (BitVec.update (vr + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__ssputs_r_at_800143f0 hmem
  exact stepObs_jr σ i u (0x800143f0#64) vminstret vr (0x00008067#32) (0x000#12)
    (regidx.Regidx 0x01#5) (0x67#8) (0x80#8) (0x00#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00008067 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (rX_bits_x1 _ vr
      (by rw [get?_afterNextPC σ (0x800143f0#64) _ (by decide) (by decide)]; exact hx1))
    htgt hi

end Vsa.Sim
