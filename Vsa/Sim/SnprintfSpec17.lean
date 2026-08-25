import Vsa.Sim.SnprintfSpec11
import Vsa.Sim.DecodeTable.Batch12Part08
import Vsa.Sim.DecodeTable.Batch12Part03
import Vsa.Sim.DecodeTable.Batch12Part16
import Vsa.Sim.DecodeTable.Batch12Part18
import Vsa.Sim.DecodeTable.Batch11Part29
import Vsa.Sim.DecodeTable.Batch11Part04
import Vsa.Sim.DecodeTable.Batch10Part29
import Vsa.Sim.DecodeTable.Batch09Part29
import Vsa.Sim.DecodeTable.Batch09Part24
import Vsa.Sim.DecodeTable.Batch09Part25
import Vsa.Sim.DecodeTable.Batch09Part26
import Vsa.Sim.DecodeTable.Batch09Part22
import Vsa.Sim.DecodeTable.Batch08Part27
import Vsa.Sim.DecodeTable.Batch06Part10
import Vsa.Sim.DecodeTable.Batch05Part30
import Vsa.Sim.DecodeTable.Batch05Part31
import Vsa.Sim.DecodeTable.Batch05Part21
import Vsa.Sim.DecodeTable.Batch05Part22
import Vsa.Sim.DecodeTable.Batch05Part11
import Vsa.Sim.DecodeTable.Batch04Part24
import Vsa.Sim.DecodeTable.Batch04Part29
import Vsa.Sim.DecodeTable.Batch03Part15
import Vsa.Sim.DecodeTable.Batch03Part09
import Vsa.Sim.DecodeTable.Batch03Part18
import Vsa.Sim.DecodeTable.Batch02Part27
import Vsa.Sim.DecodeTable.Batch02Part17
import Vsa.Sim.DecodeTable.Batch02Part02
import Vsa.Sim.DecodeTable.Batch01Part11
import Vsa.Sim.DecodeTable.Batch01Part12

/-!
# M3 Layer-3 — `SnprintfSpec17` : second iovec entry + `__ssprint_r` call setup (`_i2`)

The flush continuation of `printEntryToSignIov_spec` (`SnprintfSpec11`), which
lands at `0x800078ac` with the sign-byte iovec built.  This file covers the
executed path that builds the SECOND iovec entry (the digit string) and enters
the string-sink flush routine `__ssprint_r`:

```
  78ac: li   a4,128
  78b0: beq  t0,a4,8548      NOT taken (t0 = flags&0x84 ≠ 0x80)
  78b4: subw s4,s4,s6        s4 := width − digit_count
  78b8: bgtz s4,7cec         NOT taken (no left padding: width ≤ len)
  78bc: andi a4,t1,256
  78c0: bnez a4,7e00         NOT taken (flags&0x100 = 0)
  78c4: lw   a5,232(sp)      a5 := iov count
  78c8: add  a2,a2,s6        a2 := cursor + digit_count
  78cc: sd   a2,240(sp)      store cursor
  78d0: addiw a5,a5,1        a5 := count + 1
  78d4: sd   s10,0(s7)       iov[k+1].iov_base := digit buffer base
  78d8: sd   s6,8(s7)        iov[k+1].iov_len  := digit count
  78dc: li   a4,7
  78e0: sw   a5,232(sp)      store count + 1
  78e4: blt  a4,a5,7bf4      NOT taken (count + 1 ≤ 7, no early flush)
  78e8: addi s7,s7,16        iov cursor += 16
  78ec: andi t1,t1,4
  78f0: beqz t1,78fc         taken (flags&4 = 0)
  78fc: mv   a5,t3           a5 := payload end
  7900: bge  t3,a6,7908      taken ⇒ a5 := t3 ; not taken ⇒ 7904
  7904: mv   a5,a6           a5 := len
  7908: ld   a4,16(sp)       a4 := running total
  790c: addw a5,a5,a4        a5 := total + max(t3, a6)
  7910: sd   a5,16(sp)       store total
  7914: bnez a2,8678         taken (cursor ≠ 0 — there is buffered output)
  8678: ld   a1,8(sp)        a1 := the string-sink cursor struct
  867c: addi a2,sp,224       a2 := &sink
  8680: mv   a0,s0           a0 := reent
  8684: jal  e908 <__ssprint_r>   call; ra := 0x80008688
```

`iov2Tail_spec` is the shared tail from `0x80007908` (either `bge` outcome);
`iov2ToSsprintCall_spec` composes the head with it and is stated with the
`bge` outcome as an `if`, so both outcomes are covered by one specification.
The postcondition is exactly the `__ssprint_r` ABI entry state: `a0` = the
reent pointer, `a1` = the string-sink cursor struct pointer, `a2` = the sink,
`ra` = the return point `0x80008688`, PC = `0x8000e908`, and the memory with
the second iovec entry, the bumped cursor/count/total fields written.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (SvfprintfSliceLoaded FlushPinsLoaded)

set_option maxHeartbeats 16000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- Slot facts survive a disjoint `writeMap4` (four inserts strictly above the
slot).  Local helper for the `sw`-store survival in this file. -/
theorem slotHolds_writeMap4_i2 (vsp : BitVec 64) (off : Nat) (v : BitVec 64)
    (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 4))
    (hslot : (vsp + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat + 8 ≤ a)
    (h : SlotHolds vsp off v mem) : SlotHolds vsp off v (writeMap4 mem a d) :=
  slotHolds_insert vsp off v _ _ _ (Or.inr (by omega))
    (slotHolds_insert vsp off v _ _ _ (Or.inr (by omega))
      (slotHolds_insert vsp off v _ _ _ (Or.inr (by omega))
        (slotHolds_insert vsp off v _ _ _ (Or.inr (by omega)) h)))

/-! ## The tail: `0x80007908` → the `jal` at `0x80008684` completed

Shared by both `bge t3,a6` outcomes; `vsel` is whichever of `t3`/`a6` the
branch selected (`a5` at entry). -/

theorem iov2Tail_spec
    (vsp vt0 vt6 v8 vc2 vlen vsubw vnd6 viov3 vbase vt3 vsel vstr vtot : BitVec 64)
    (c : Config)
    (hG : GoodState c.σ)
    (hpc : c.σ.regs.get? Register.PC = some (0x80007908#64))
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx5 : c.σ.regs.get? Register.x5 = some vt0)
    (hx6 : c.σ.regs.get? Register.x6 = some vt6)
    (hx8 : c.σ.regs.get? Register.x8 = some v8)
    (hx12 : c.σ.regs.get? Register.x12 = some vc2)
    (hx15 : c.σ.regs.get? Register.x15 = some vsel)
    (hx16 : c.σ.regs.get? Register.x16 = some vlen)
    (hx20 : c.σ.regs.get? Register.x20 = some vsubw)
    (hx22 : c.σ.regs.get? Register.x22 = some vnd6)
    (hx23 : c.σ.regs.get? Register.x23 = some viov3)
    (hx26 : c.σ.regs.get? Register.x26 = some vbase)
    (hx28 : c.σ.regs.get? Register.x28 = some vt3)
    (hload : SvfprintfSliceLoaded c.σ.mem)
    (hfp : FlushPinsLoaded c.σ.mem)
    (htot : SlotHolds vsp 0x010 vtot c.σ.mem)
    (hstr : SlotHolds vsp 0x008 vstr c.σ.mem)
    (hvc2 : ((vc2 != (0#64)) = true))
    (hsplo : tohostAddr + 16 + 64 ≤ vsp.toNat)
    (hsphi : vsp.toNat + 356 ≤ 0x100000000)
    (hspalign : vsp.toNat % 8 = 0)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x8000e908#64) ∧
      c'.σ.regs.get? Register.x1 = some (0x80008688#64) ∧
      c'.σ.regs.get? Register.x10 = some v8 ∧
      c'.σ.regs.get? Register.x11 = some vstr ∧
      c'.σ.regs.get? Register.x12 = some (vsp + sign_extend (m := 64) (0x0e0#12)) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.σ.regs.get? Register.x5 = some vt0 ∧
      c'.σ.regs.get? Register.x6 = some vt6 ∧
      c'.σ.regs.get? Register.x8 = some v8 ∧
      c'.σ.regs.get? Register.x16 = some vlen ∧
      c'.σ.regs.get? Register.x20 = some vsubw ∧
      c'.σ.regs.get? Register.x22 = some vnd6 ∧
      c'.σ.regs.get? Register.x23 = some viov3 ∧
      c'.σ.regs.get? Register.x26 = some vbase ∧
      c'.σ.regs.get? Register.x28 = some vt3 ∧
      c'.σ.mem = writeMap8 c.σ.mem
        (vsp + sign_extend (m := 64) (0x010#12)).toNat
        (sdData_val (sign_extend (m := 64)
          (Sail.BitVec.extractLsb vsel 31 0
            + Sail.BitVec.extractLsb vtot 31 0))) ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) ∧
      -- post-widening: mid-register preservation
      KeepRegs midRegs5 c.σ c'.σ := by
  have htohv : tohostAddr = 0x8001ad00 := rfl
  have hnw : vsp.toNat + 348 < 2 ^ 64 := by omega
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
  have hoff16 : (vsp + sign_extend (m := 64) (0x010#12)).toNat = vsp.toNat + 16 :=
    addoff_toNat_sn5 vsp (0x010#12) 16 (by omega) (by decide) hnw
  have hoff8 : (vsp + sign_extend (m := 64) (0x008#12)).toNat = vsp.toNat + 8 :=
    addoff_toNat_sn5 vsp (0x008#12) 8 (by omega) (by decide) hnw
  have hoff224 : (vsp + sign_extend (m := 64) (0x0e0#12)).toNat = vsp.toNat + 224 :=
    addoff_toNat_sn5 vsp (0x0e0#12) 224 (by omega) (by decide) hnw
  -- === 7908: ld a4,16(sp)  ⇒  x14 := vtot ===
  obtain ⟨hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7⟩ := htot
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80007908 hload
  have hx2n1 : (afterNextPC (afterPrelude c.σ) (0x80007908#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC c.σ (0x80007908#64) _ (by decide) (by decide)]; exact hx2
  obtain ⟨σ1, i1, hs1s, hi1, hG1, hmem1, hobs1⟩ :=
    stepObs_alu c.σ c.tick c.steps (0x80007908#64) vmi0 (0x01013703#32)
      (instruction.LOAD (0x010#12, regidx.Regidx 0x02#5, regidx.Regidx 0x0e#5, false, 8))
      Register.x14 (sign_extend (m := 64)
        (((((((((sdData_val vtot).extractLsb' 56 8).append ((sdData_val vtot).extractLsb' 48 8)).append
          ((sdData_val vtot).extractLsb' 40 8)).append ((sdData_val vtot).extractLsb' 32 8)).append
          ((sdData_val vtot).extractLsb' 24 8)).append ((sdData_val vtot).extractLsb' 16 8)).append
          ((sdData_val vtot).extractLsb' 8 8)).append ((sdData_val vtot).extractLsb' 0 8)
          : BitVec (8 * 8)))
      (0x03#8) (0x37#8) (0x01#8) (0x01#8)
      hG hpc hmi0 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_01013703 (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (exec_ld c.σ (0x80007908#64) (0x010#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x0e#5)
        (sigma3_alu c.σ (0x80007908#64) Register.x14 (sign_extend (m := 64)
          (((((((((sdData_val vtot).extractLsb' 56 8).append ((sdData_val vtot).extractLsb' 48 8)).append
            ((sdData_val vtot).extractLsb' 40 8)).append ((sdData_val vtot).extractLsb' 32 8)).append
            ((sdData_val vtot).extractLsb' 24 8)).append ((sdData_val vtot).extractLsb' 16 8)).append
            ((sdData_val vtot).extractLsb' 8 8)).append ((sdData_val vtot).extractLsb' 0 8)
            : BitVec (8 * 8))))
        vsp ((sdData_val vtot).extractLsb' 0 8) ((sdData_val vtot).extractLsb' 8 8)
        ((sdData_val vtot).extractLsb' 16 8) ((sdData_val vtot).extractLsb' 24 8)
        ((sdData_val vtot).extractLsb' 32 8) ((sdData_val vtot).extractLsb' 40 8)
        ((sdData_val vtot).extractLsb' 48 8) ((sdData_val vtot).extractLsb' 56 8)
        hG (rX_bits_x2 _ vsp hx2n1)
        (wX_bits_x14 _ (sign_extend (m := 64)
          (((((((((sdData_val vtot).extractLsb' 56 8).append ((sdData_val vtot).extractLsb' 48 8)).append
            ((sdData_val vtot).extractLsb' 40 8)).append ((sdData_val vtot).extractLsb' 32 8)).append
            ((sdData_val vtot).extractLsb' 24 8)).append ((sdData_val vtot).extractLsb' 16 8)).append
            ((sdData_val vtot).extractLsb' 8 8)).append ((sdData_val vtot).extractLsb' 0 8)
            : BitVec (8 * 8))))
        (by rw [hoff16]; omega) (by rw [hoff16]; omega) (Or.inr (by rw [hoff16]; omega))
        (by rw [hoff16]; omega) hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1s
  have hpc1 : σ1.regs.get? Register.PC = some (0x8000790c#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x80007908#64 : BitVec 64) 4 = (0x8000790c#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hx14_1 : σ1.regs.get? Register.x14 = some vtot := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [ve_sext_reassemble vtot] at this
  have hx2_1 : σ1.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2
  have hx5_1 : σ1.regs.get? Register.x5 = some vt0 :=
    obs_alu_other hobs1 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5
  have hx6_1 : σ1.regs.get? Register.x6 = some vt6 :=
    obs_alu_other hobs1 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6
  have hx8_1 : σ1.regs.get? Register.x8 = some v8 :=
    obs_alu_other hobs1 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8
  have hx12_1 : σ1.regs.get? Register.x12 = some vc2 :=
    obs_alu_other hobs1 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12
  have hx15_1 : σ1.regs.get? Register.x15 = some vsel :=
    obs_alu_other hobs1 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15
  have hx16_1 : σ1.regs.get? Register.x16 = some vlen :=
    obs_alu_other hobs1 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16
  have hx20_1 : σ1.regs.get? Register.x20 = some vsubw :=
    obs_alu_other hobs1 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20
  have hx22_1 : σ1.regs.get? Register.x22 = some vnd6 :=
    obs_alu_other hobs1 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22
  have hx23_1 : σ1.regs.get? Register.x23 = some viov3 :=
    obs_alu_other hobs1 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23
  have hx26_1 : σ1.regs.get? Register.x26 = some vbase :=
    obs_alu_other hobs1 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26
  have hx28_1 : σ1.regs.get? Register.x28 = some vt3 :=
    obs_alu_other hobs1 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28
  have hload1 : SvfprintfSliceLoaded σ1.mem := hmem1 ▸ hload
  have hfp1 : FlushPinsLoaded σ1.mem := hmem1 ▸ hfp
  have hstr1 : SlotHolds vsp 0x008 vstr σ1.mem := hmem1 ▸ hstr
  -- === 790c: addw a5,a5,a4  ⇒  x15 := sext32(lo32 vsel + lo32 vtot) ===
  obtain ⟨hc0, hc1, hc2, hc3⟩ := Vsa.Sim.Code.svfprintfSlice_at_8000790c hload1
  have hx15n2 : (afterNextPC (afterPrelude σ1) (0x8000790c#64)).regs.get? Register.x15 = some vsel := by
    rw [get?_afterNextPC σ1 (0x8000790c#64) _ (by decide) (by decide)]; exact hx15_1
  have hx14n2 : (afterNextPC (afterPrelude σ1) (0x8000790c#64)).regs.get? Register.x14 = some vtot := by
    rw [get?_afterNextPC σ1 (0x8000790c#64) _ (by decide) (by decide)]; exact hx14_1
  obtain ⟨σ2, i2, hs2s, hi2, hG2, hmem2, hobs2⟩ :=
    stepObs_alu σ1 i1 (c.steps + 1) (0x8000790c#64) vmi1 (0x00e787bb#32)
      (instruction.RTYPEW (regidx.Regidx 0x0e#5, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, ropw.ADDW))
      Register.x15 (sign_extend (m := 64)
        (Sail.BitVec.extractLsb vsel 31 0 + Sail.BitVec.extractLsb vtot 31 0))
      (0xbb#8) (0x87#8) (0xe7#8) (0x00#8)
      hG1 hpc1 hmi1 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_00e787bb (afterPrelude σ1)
        (by rw [get?_afterPrelude σ1 _ (by decide)]; exact hG1.misa)
        (by rw [get?_afterPrelude σ1 _ (by decide)]; exact hG1.cur_privilege)
        (by rw [get?_afterPrelude σ1 _ (by decide)]; exact hG1.mseccfg))
      (execute_rtypew_addw_char (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5)
        vsel vtot (afterNextPC (afterPrelude σ1) (0x8000790c#64))
        (sigma3_alu σ1 (0x8000790c#64) Register.x15 (sign_extend (m := 64)
          (Sail.BitVec.extractLsb vsel 31 0 + Sail.BitVec.extractLsb vtot 31 0)))
        (rX_bits_x15 _ vsel hx15n2) (rX_bits_x14 _ vtot hx14n2)
        (wX_bits_x15 _ (sign_extend (m := 64)
          (Sail.BitVec.extractLsb vsel 31 0 + Sail.BitVec.extractLsb vtot 31 0))))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hc0 hc1 hc2 hc3 (by decide) (by decide) (by decide) hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2s
  have hpc2 : σ2.regs.get? Register.PC = some (0x80007910#64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x8000790c#64 : BitVec 64) 4 = (0x80007910#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hx2_2 : σ2.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs2 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_1
  have hx5_2 : σ2.regs.get? Register.x5 = some vt0 :=
    obs_alu_other hobs2 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_1
  have hx6_2 : σ2.regs.get? Register.x6 = some vt6 :=
    obs_alu_other hobs2 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_1
  have hx8_2 : σ2.regs.get? Register.x8 = some v8 :=
    obs_alu_other hobs2 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_1
  have hx12_2 : σ2.regs.get? Register.x12 = some vc2 :=
    obs_alu_other hobs2 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_1
  have hx15_2 : σ2.regs.get? Register.x15 = some (sign_extend (m := 64)
      (Sail.BitVec.extractLsb vsel 31 0 + Sail.BitVec.extractLsb vtot 31 0)) :=
    obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx16_2 : σ2.regs.get? Register.x16 = some vlen :=
    obs_alu_other hobs2 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_1
  have hx20_2 : σ2.regs.get? Register.x20 = some vsubw :=
    obs_alu_other hobs2 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_1
  have hx22_2 : σ2.regs.get? Register.x22 = some vnd6 :=
    obs_alu_other hobs2 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_1
  have hx23_2 : σ2.regs.get? Register.x23 = some viov3 :=
    obs_alu_other hobs2 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_1
  have hx26_2 : σ2.regs.get? Register.x26 = some vbase :=
    obs_alu_other hobs2 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_1
  have hx28_2 : σ2.regs.get? Register.x28 = some vt3 :=
    obs_alu_other hobs2 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_1
  have hload2 : SvfprintfSliceLoaded σ2.mem := hmem2 ▸ hload1
  have hfp2 : FlushPinsLoaded σ2.mem := hmem2 ▸ hfp1
  have hstr2 : SlotHolds vsp 0x008 vstr σ2.mem := hmem2 ▸ hstr1
  -- === 7910: sd a5,16(sp)  ⇒  mem[sp+16] := the new total ===
  obtain ⟨hd0, hd1, hd2, hd3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80007910 hload2
  have hx2n3 : (afterNextPC (afterPrelude σ2) (0x80007910#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ2 (0x80007910#64) _ (by decide) (by decide)]; exact hx2_2
  have hx15n3 : (afterNextPC (afterPrelude σ2) (0x80007910#64)).regs.get? Register.x15
      = some (sign_extend (m := 64)
        (Sail.BitVec.extractLsb vsel 31 0 + Sail.BitVec.extractLsb vtot 31 0)) := by
    rw [get?_afterNextPC σ2 (0x80007910#64) _ (by decide) (by decide)]; exact hx15_2
  obtain ⟨σ3, i3, hs3s, hi3, hG3, hmem3, hobs3⟩ :=
    stepObs_store σ2 i2 (c.steps + 1 + 1) (0x80007910#64) vmi2 (0x00f13823#32)
      (instruction.STORE (0x010#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x02#5, 8))
      (writeMap8 (afterNextPC (afterPrelude σ2) (0x80007910#64)).mem
        (vsp + sign_extend (m := 64) (0x010#12)).toNat (sdData_val (sign_extend (m := 64)
          (Sail.BitVec.extractLsb vsel 31 0 + Sail.BitVec.extractLsb vtot 31 0))))
      (0x23#8) (0x38#8) (0xf1#8) (0x00#8)
      hG2 hpc2 hmi2 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_00f13823 (afterPrelude σ2)
        (by rw [get?_afterPrelude σ2 _ (by decide)]; exact hG2.misa)
        (by rw [get?_afterPrelude σ2 _ (by decide)]; exact hG2.cur_privilege)
        (by rw [get?_afterPrelude σ2 _ (by decide)]; exact hG2.mseccfg))
      (exec_sd_val σ2 (0x80007910#64) (0x010#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x02#5)
        vsp (sign_extend (m := 64)
          (Sail.BitVec.extractLsb vsel 31 0 + Sail.BitVec.extractLsb vtot 31 0))
        hG2 (rX_bits_x2 _ vsp hx2n3) (rX_bits_x15 _ _ hx15n3)
        (by rw [hoff16]; omega) (by rw [hoff16]; omega) (by rw [hoff16]; omega) (by rw [hoff16]; omega))
      hd0 hd1 hd2 hd3 (by decide) (by decide) (by decide) hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3s
  have hpc3 : σ3.regs.get? Register.PC = some (0x80007914#64) := by
    have := obs_store_pc_sn4 hobs3
    rwa [show BitVec.addInt (0x80007910#64 : BitVec 64) 4 = (0x80007914#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi3, hmi3⟩ := obs_store_minstret_sn4 hobs3
  have hx2_3 : σ3.regs.get? Register.x2 = some vsp :=
    obs_store_other_sn4 Register.x2 hobs3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_2
  have hx5_3 : σ3.regs.get? Register.x5 = some vt0 :=
    obs_store_other_sn4 Register.x5 hobs3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_2
  have hx6_3 : σ3.regs.get? Register.x6 = some vt6 :=
    obs_store_other_sn4 Register.x6 hobs3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_2
  have hx8_3 : σ3.regs.get? Register.x8 = some v8 :=
    obs_store_other_sn4 Register.x8 hobs3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_2
  have hx12_3 : σ3.regs.get? Register.x12 = some vc2 :=
    obs_store_other_sn4 Register.x12 hobs3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_2
  have hx16_3 : σ3.regs.get? Register.x16 = some vlen :=
    obs_store_other_sn4 Register.x16 hobs3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_2
  have hx20_3 : σ3.regs.get? Register.x20 = some vsubw :=
    obs_store_other_sn4 Register.x20 hobs3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_2
  have hx22_3 : σ3.regs.get? Register.x22 = some vnd6 :=
    obs_store_other_sn4 Register.x22 hobs3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_2
  have hx23_3 : σ3.regs.get? Register.x23 = some viov3 :=
    obs_store_other_sn4 Register.x23 hobs3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_2
  have hx26_3 : σ3.regs.get? Register.x26 = some vbase :=
    obs_store_other_sn4 Register.x26 hobs3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_2
  have hx28_3 : σ3.regs.get? Register.x28 = some vt3 :=
    obs_store_other_sn4 Register.x28 hobs3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_2
  have hNP3 : (afterNextPC (afterPrelude σ2) (0x80007910#64)).mem = σ2.mem := rfl
  have hmem3' : σ3.mem = writeMap8 σ2.mem
      (vsp + sign_extend (m := 64) (0x010#12)).toNat (sdData_val (sign_extend (m := 64)
        (Sail.BitVec.extractLsb vsel 31 0 + Sail.BitVec.extractLsb vtot 31 0))) := by
    rw [hmem3, hNP3]
  have hload3 : SvfprintfSliceLoaded σ3.mem := by
    rw [hmem3']; exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff16]; omega) hload2
  have hfp3 : FlushPinsLoaded σ3.mem := by
    rw [hmem3']; exact flushPins_writeMap8_fl _ _ _ (by rw [hoff16]; omega) hfp2
  have hstr3 : SlotHolds vsp 0x008 vstr σ3.mem := by
    rw [hmem3']; exact slotHolds_writeMap8 vsp 0x008 vstr _
      ((vsp + sign_extend (m := 64) (0x010#12)).toNat) _
      (Or.inl (by rw [hoff8, hoff16]; omega)) hstr2
  -- === 7914: bnez a2,8678  (taken: cursor ≠ 0) ===
  obtain ⟨he0, he1, he2, he3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80007914 hload3
  have hx12n4 : (rX_bits (regidx.Regidx 0x0c#5)).run (afterNextPC (afterPrelude σ3) (0x80007914#64))
      = .ok vc2 (afterNextPC (afterPrelude σ3) (0x80007914#64)) := by
    apply rX_bits_x12
    rw [get?_afterNextPC σ3 (0x80007914#64) _ (by decide) (by decide)]; exact hx12_3
  obtain ⟨σ4, i4, hs4s, hi4, hG4, hmem4, hobs4⟩ :=
    stepObs_branch_taken σ3 i3 (c.steps + 1 + 1 + 1) (0x80007914#64) vmi3
      (0x0d64#13) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x00#5) bop.BNE (0x560612e3#32)
      (0xe3#8) (0x12#8) (0x06#8) (0x56#8)
      hG3 hpc3 hmi3 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_560612e3 (afterPrelude σ3)
        (by rw [get?_afterPrelude σ3 _ (by decide)]; exact hG3.misa)
        (by rw [get?_afterPrelude σ3 _ (by decide)]; exact hG3.cur_privilege)
        (by rw [get?_afterPrelude σ3 _ (by decide)]; exact hG3.mseccfg))
      (execute_btype_bne_taken (0x0d64#13) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x00#5)
        vc2 (0#64) (0x80007914#64) initMisa (afterNextPC (afterPrelude σ3) (0x80007914#64))
        hx12n4 (rX_bits_zero _)
        (by rw [get?_afterNextPC σ3 (0x80007914#64) _ (by decide) (by decide)]; exact hpc3)
        (by rw [get?_afterNextPC σ3 (0x80007914#64) _ (by decide) (by decide)]; exact hG3.misa)
        (by decide) hvc2)
      he0 he1 he2 he3 (by decide) (by decide) (by decide) hi3
  have hstep4 : Step ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ := hs4s
  have hpc4 : σ4.regs.get? Register.PC = some (0x80008678#64) := by
    have := obs_branch_taken_pc hobs4
    rwa [show ((0x80007914#64 : BitVec 64) + sign_extend (m := 64) (0x0d64#13))
      = (0x80008678#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi4, hmi4⟩ := obs_branch_taken_minstret hobs4
  have hx2_4 : σ4.regs.get? Register.x2 = some vsp :=
    obs_branch_taken_other hobs4 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_3
  have hx5_4 : σ4.regs.get? Register.x5 = some vt0 :=
    obs_branch_taken_other hobs4 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_3
  have hx6_4 : σ4.regs.get? Register.x6 = some vt6 :=
    obs_branch_taken_other hobs4 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_3
  have hx8_4 : σ4.regs.get? Register.x8 = some v8 :=
    obs_branch_taken_other hobs4 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_3
  have hx16_4 : σ4.regs.get? Register.x16 = some vlen :=
    obs_branch_taken_other hobs4 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_3
  have hx20_4 : σ4.regs.get? Register.x20 = some vsubw :=
    obs_branch_taken_other hobs4 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_3
  have hx22_4 : σ4.regs.get? Register.x22 = some vnd6 :=
    obs_branch_taken_other hobs4 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_3
  have hx23_4 : σ4.regs.get? Register.x23 = some viov3 :=
    obs_branch_taken_other hobs4 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_3
  have hx26_4 : σ4.regs.get? Register.x26 = some vbase :=
    obs_branch_taken_other hobs4 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_3
  have hx28_4 : σ4.regs.get? Register.x28 = some vt3 :=
    obs_branch_taken_other hobs4 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_3
  have hmem4eq : σ4.mem = σ3.mem := hmem4
  have hload4 : SvfprintfSliceLoaded σ4.mem := hmem4eq ▸ hload3
  have hfp4 : FlushPinsLoaded σ4.mem := hmem4eq ▸ hfp3
  have hstr4 : SlotHolds vsp 0x008 vstr σ4.mem := hmem4eq ▸ hstr3
  -- === 8678: ld a1,8(sp)  ⇒  x11 := vstr ===
  obtain ⟨hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7⟩ := hstr4
  obtain ⟨hf0, hf1, hf2, hf3⟩ := Vsa.Sim.Code.flushPins_at_80008678 hfp4
  have hx2n5 : (afterNextPC (afterPrelude σ4) (0x80008678#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ4 (0x80008678#64) _ (by decide) (by decide)]; exact hx2_4
  obtain ⟨σ5, i5, hs5s, hi5, hG5, hmem5, hobs5⟩ :=
    stepObs_alu σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x80008678#64) vmi4 (0x00813583#32)
      (instruction.LOAD (0x008#12, regidx.Regidx 0x02#5, regidx.Regidx 0x0b#5, false, 8))
      Register.x11 (sign_extend (m := 64)
        (((((((((sdData_val vstr).extractLsb' 56 8).append ((sdData_val vstr).extractLsb' 48 8)).append
          ((sdData_val vstr).extractLsb' 40 8)).append ((sdData_val vstr).extractLsb' 32 8)).append
          ((sdData_val vstr).extractLsb' 24 8)).append ((sdData_val vstr).extractLsb' 16 8)).append
          ((sdData_val vstr).extractLsb' 8 8)).append ((sdData_val vstr).extractLsb' 0 8)
          : BitVec (8 * 8)))
      (0x83#8) (0x35#8) (0x81#8) (0x00#8)
      hG4 hpc4 hmi4 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_00813583 (afterPrelude σ4)
        (by rw [get?_afterPrelude σ4 _ (by decide)]; exact hG4.misa)
        (by rw [get?_afterPrelude σ4 _ (by decide)]; exact hG4.cur_privilege)
        (by rw [get?_afterPrelude σ4 _ (by decide)]; exact hG4.mseccfg))
      (exec_ld σ4 (0x80008678#64) (0x008#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x0b#5)
        (sigma3_alu σ4 (0x80008678#64) Register.x11 (sign_extend (m := 64)
          (((((((((sdData_val vstr).extractLsb' 56 8).append ((sdData_val vstr).extractLsb' 48 8)).append
            ((sdData_val vstr).extractLsb' 40 8)).append ((sdData_val vstr).extractLsb' 32 8)).append
            ((sdData_val vstr).extractLsb' 24 8)).append ((sdData_val vstr).extractLsb' 16 8)).append
            ((sdData_val vstr).extractLsb' 8 8)).append ((sdData_val vstr).extractLsb' 0 8)
            : BitVec (8 * 8))))
        vsp ((sdData_val vstr).extractLsb' 0 8) ((sdData_val vstr).extractLsb' 8 8)
        ((sdData_val vstr).extractLsb' 16 8) ((sdData_val vstr).extractLsb' 24 8)
        ((sdData_val vstr).extractLsb' 32 8) ((sdData_val vstr).extractLsb' 40 8)
        ((sdData_val vstr).extractLsb' 48 8) ((sdData_val vstr).extractLsb' 56 8)
        hG4 (rX_bits_x2 _ vsp hx2n5)
        (wX_bits_x11 _ (sign_extend (m := 64)
          (((((((((sdData_val vstr).extractLsb' 56 8).append ((sdData_val vstr).extractLsb' 48 8)).append
            ((sdData_val vstr).extractLsb' 40 8)).append ((sdData_val vstr).extractLsb' 32 8)).append
            ((sdData_val vstr).extractLsb' 24 8)).append ((sdData_val vstr).extractLsb' 16 8)).append
            ((sdData_val vstr).extractLsb' 8 8)).append ((sdData_val vstr).extractLsb' 0 8)
            : BitVec (8 * 8))))
        (by rw [hoff8]; omega) (by rw [hoff8]; omega) (Or.inr (by rw [hoff8]; omega))
        (by rw [hoff8]; omega) hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hf0 hf1 hf2 hf3 (by decide) (by decide) (by decide) hi4
  have hstep5 : Step ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ := hs5s
  have hpc5 : σ5.regs.get? Register.PC = some (0x8000867c#64) := by
    have := obs_alu_pc hobs5
    rwa [show BitVec.addInt (0x80008678#64 : BitVec 64) 4 = (0x8000867c#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi5, hmi5⟩ := obs_alu_minstret hobs5
  have hx11_5 : σ5.regs.get? Register.x11 = some vstr := by
    have := obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [ve_sext_reassemble vstr] at this
  have hx2_5 : σ5.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs5 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_4
  have hx5_5 : σ5.regs.get? Register.x5 = some vt0 :=
    obs_alu_other hobs5 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_4
  have hx6_5 : σ5.regs.get? Register.x6 = some vt6 :=
    obs_alu_other hobs5 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_4
  have hx8_5 : σ5.regs.get? Register.x8 = some v8 :=
    obs_alu_other hobs5 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_4
  have hx16_5 : σ5.regs.get? Register.x16 = some vlen :=
    obs_alu_other hobs5 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_4
  have hx20_5 : σ5.regs.get? Register.x20 = some vsubw :=
    obs_alu_other hobs5 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_4
  have hx22_5 : σ5.regs.get? Register.x22 = some vnd6 :=
    obs_alu_other hobs5 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_4
  have hx23_5 : σ5.regs.get? Register.x23 = some viov3 :=
    obs_alu_other hobs5 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_4
  have hx26_5 : σ5.regs.get? Register.x26 = some vbase :=
    obs_alu_other hobs5 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_4
  have hx28_5 : σ5.regs.get? Register.x28 = some vt3 :=
    obs_alu_other hobs5 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_4
  have hfp5 : FlushPinsLoaded σ5.mem := hmem5 ▸ hfp4
  -- === 867c: addi a2,sp,224  ⇒  x12 := vsp + 224 ===
  obtain ⟨hg0, hg1, hg2, hg3⟩ := Vsa.Sim.Code.flushPins_at_8000867c hfp5
  have hx2n6 : (afterNextPC (afterPrelude σ5) (0x8000867c#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ5 (0x8000867c#64) _ (by decide) (by decide)]; exact hx2_5
  obtain ⟨σ6, i6, hs6s, hi6, hG6, hmem6, hobs6⟩ :=
    stepObs_alu σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x8000867c#64) vmi5 (0x0e010613#32)
      (instruction.ITYPE (0x0e0#12, regidx.Regidx 0x02#5, regidx.Regidx 0x0c#5, iop.ADDI))
      Register.x12 (vsp + sign_extend (m := 64) (0x0e0#12))
      (0x13#8) (0x06#8) (0x01#8) (0x0e#8)
      hG5 hpc5 hmi5 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_0e010613 (afterPrelude σ5)
        (by rw [get?_afterPrelude σ5 _ (by decide)]; exact hG5.misa)
        (by rw [get?_afterPrelude σ5 _ (by decide)]; exact hG5.cur_privilege)
        (by rw [get?_afterPrelude σ5 _ (by decide)]; exact hG5.mseccfg))
      (execute_itype_addi_char (0x0e0#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x0c#5) vsp
        (afterNextPC (afterPrelude σ5) (0x8000867c#64))
        (sigma3_alu σ5 (0x8000867c#64) Register.x12 (vsp + sign_extend (m := 64) (0x0e0#12)))
        (rX_bits_x2 _ vsp hx2n6) (wX_bits_x12 _ (vsp + sign_extend (m := 64) (0x0e0#12))))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hg0 hg1 hg2 hg3 (by decide) (by decide) (by decide) hi5
  have hstep6 : Step ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ ⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs6s
  have hpc6 : σ6.regs.get? Register.PC = some (0x80008680#64) := by
    have := obs_alu_pc hobs6
    rwa [show BitVec.addInt (0x8000867c#64 : BitVec 64) 4 = (0x80008680#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi6, hmi6⟩ := obs_alu_minstret hobs6
  have hx12_6 : σ6.regs.get? Register.x12 = some (vsp + sign_extend (m := 64) (0x0e0#12)) :=
    obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx2_6 : σ6.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs6 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_5
  have hx5_6 : σ6.regs.get? Register.x5 = some vt0 :=
    obs_alu_other hobs6 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_5
  have hx6_6 : σ6.regs.get? Register.x6 = some vt6 :=
    obs_alu_other hobs6 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_5
  have hx8_6 : σ6.regs.get? Register.x8 = some v8 :=
    obs_alu_other hobs6 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_5
  have hx11_6 : σ6.regs.get? Register.x11 = some vstr :=
    obs_alu_other hobs6 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_5
  have hx16_6 : σ6.regs.get? Register.x16 = some vlen :=
    obs_alu_other hobs6 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_5
  have hx20_6 : σ6.regs.get? Register.x20 = some vsubw :=
    obs_alu_other hobs6 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_5
  have hx22_6 : σ6.regs.get? Register.x22 = some vnd6 :=
    obs_alu_other hobs6 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_5
  have hx23_6 : σ6.regs.get? Register.x23 = some viov3 :=
    obs_alu_other hobs6 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_5
  have hx26_6 : σ6.regs.get? Register.x26 = some vbase :=
    obs_alu_other hobs6 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_5
  have hx28_6 : σ6.regs.get? Register.x28 = some vt3 :=
    obs_alu_other hobs6 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_5
  have hfp6 : FlushPinsLoaded σ6.mem := hmem6 ▸ hfp5
  -- === 8680: mv a0,s0  ⇒  x10 := v8 ===
  obtain ⟨hh0, hh1, hh2, hh3⟩ := Vsa.Sim.Code.flushPins_at_80008680 hfp6
  have hx8n7 : (afterNextPC (afterPrelude σ6) (0x80008680#64)).regs.get? Register.x8 = some v8 := by
    rw [get?_afterNextPC σ6 (0x80008680#64) _ (by decide) (by decide)]; exact hx8_6
  obtain ⟨σ7, i7, hs7s, hi7, hG7, hmem7, hobs7⟩ :=
    stepObs_alu σ6 i6 (c.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x80008680#64) vmi6 (0x00040513#32)
      (instruction.ITYPE (0x000#12, regidx.Regidx 0x08#5, regidx.Regidx 0x0a#5, iop.ADDI))
      Register.x10 (v8 + sign_extend (m := 64) (0x000#12))
      (0x13#8) (0x05#8) (0x04#8) (0x00#8)
      hG6 hpc6 hmi6 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_00040513 (afterPrelude σ6)
        (by rw [get?_afterPrelude σ6 _ (by decide)]; exact hG6.misa)
        (by rw [get?_afterPrelude σ6 _ (by decide)]; exact hG6.cur_privilege)
        (by rw [get?_afterPrelude σ6 _ (by decide)]; exact hG6.mseccfg))
      (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x08#5) (regidx.Regidx 0x0a#5) v8
        (afterNextPC (afterPrelude σ6) (0x80008680#64))
        (sigma3_alu σ6 (0x80008680#64) Register.x10 (v8 + sign_extend (m := 64) (0x000#12)))
        (rX_bits_x8 _ v8 hx8n7) (wX_bits_x10 _ (v8 + sign_extend (m := 64) (0x000#12))))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hh0 hh1 hh2 hh3 (by decide) (by decide) (by decide) hi6
  have hstep7 : Step ⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ7, i7, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs7s
  have hpc7 : σ7.regs.get? Register.PC = some (0x80008684#64) := by
    have := obs_alu_pc hobs7
    rwa [show BitVec.addInt (0x80008680#64 : BitVec 64) 4 = (0x80008684#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi7, hmi7⟩ := obs_alu_minstret hobs7
  have hx10_7 : σ7.regs.get? Register.x10 = some v8 := by
    have := obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (v8 + sign_extend (m := 64) (0x000#12) : BitVec 64) = v8 from by
      rw [show sign_extend (m := 64) (0x000#12) = (0#64) from by
        apply BitVec.eq_of_toNat_eq; decide, BitVec.add_zero]] at this
  have hx2_7 : σ7.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs7 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_6
  have hx5_7 : σ7.regs.get? Register.x5 = some vt0 :=
    obs_alu_other hobs7 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_6
  have hx6_7 : σ7.regs.get? Register.x6 = some vt6 :=
    obs_alu_other hobs7 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_6
  have hx8_7 : σ7.regs.get? Register.x8 = some v8 :=
    obs_alu_other hobs7 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_6
  have hx11_7 : σ7.regs.get? Register.x11 = some vstr :=
    obs_alu_other hobs7 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_6
  have hx12_7 : σ7.regs.get? Register.x12 = some (vsp + sign_extend (m := 64) (0x0e0#12)) :=
    obs_alu_other hobs7 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_6
  have hx16_7 : σ7.regs.get? Register.x16 = some vlen :=
    obs_alu_other hobs7 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_6
  have hx20_7 : σ7.regs.get? Register.x20 = some vsubw :=
    obs_alu_other hobs7 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_6
  have hx22_7 : σ7.regs.get? Register.x22 = some vnd6 :=
    obs_alu_other hobs7 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_6
  have hx23_7 : σ7.regs.get? Register.x23 = some viov3 :=
    obs_alu_other hobs7 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_6
  have hx26_7 : σ7.regs.get? Register.x26 = some vbase :=
    obs_alu_other hobs7 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_6
  have hx28_7 : σ7.regs.get? Register.x28 = some vt3 :=
    obs_alu_other hobs7 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_6
  have hfp7 : FlushPinsLoaded σ7.mem := hmem7 ▸ hfp6
  -- === 8684: jal 8000e908 <__ssprint_r>  ⇒  x1 := 0x80008688, PC := 0x8000e908 ===
  obtain ⟨hj0, hj1, hj2, hj3⟩ := Vsa.Sim.Code.flushPins_at_80008684 hfp7
  obtain ⟨σ8, i8, hs8s, hi8, hG8, hmem8, hobs8⟩ :=
    stepObs_jal σ7 i7 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80008684#64) vmi7 (0x284060ef#32)
      (0x006284#21) (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x80008684#64) 4)
      (0xef#8) (0x60#8) (0x40#8) (0x28#8)
      hG7 hpc7 hmi7 hj0 hj1 hj2 hj3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_284060ef (afterPrelude σ7)
        (by rw [get?_afterPrelude σ7 _ (by decide)]; exact hG7.misa)
        (by rw [get?_afterPrelude σ7 _ (by decide)]; exact hG7.cur_privilege)
        (by rw [get?_afterPrelude σ7 _ (by decide)]; exact hG7.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x80008684#64) 4))
      hi7
  have hstep8 : Step ⟨σ7, i7, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ8, i8, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs8s
  have hpc8 : σ8.regs.get? Register.PC = some (0x8000e908#64) := by
    have := obs_jal_pc hobs8
    rwa [show ((0x80008684#64 : BitVec 64) + sign_extend (m := 64) (0x006284#21))
      = (0x8000e908#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hx1_8 : σ8.regs.get? Register.x1 = some (0x80008688#64) := by
    have := obs_jal_rd hobs8 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x80008684#64 : BitVec 64) 4 = (0x80008688#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi8, hmi8⟩ := obs_jal_minstret hobs8
  have hx2_8 : σ8.regs.get? Register.x2 = some vsp :=
    obs_jal_other hobs8 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_7
  have hx5_8 : σ8.regs.get? Register.x5 = some vt0 :=
    obs_jal_other hobs8 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_7
  have hx6_8 : σ8.regs.get? Register.x6 = some vt6 :=
    obs_jal_other hobs8 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_7
  have hx8_8 : σ8.regs.get? Register.x8 = some v8 :=
    obs_jal_other hobs8 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_7
  have hx10_8 : σ8.regs.get? Register.x10 = some v8 :=
    obs_jal_other hobs8 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_7
  have hx11_8 : σ8.regs.get? Register.x11 = some vstr :=
    obs_jal_other hobs8 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_7
  have hx12_8 : σ8.regs.get? Register.x12 = some (vsp + sign_extend (m := 64) (0x0e0#12)) :=
    obs_jal_other hobs8 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_7
  have hx16_8 : σ8.regs.get? Register.x16 = some vlen :=
    obs_jal_other hobs8 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_7
  have hx20_8 : σ8.regs.get? Register.x20 = some vsubw :=
    obs_jal_other hobs8 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_7
  have hx22_8 : σ8.regs.get? Register.x22 = some vnd6 :=
    obs_jal_other hobs8 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_7
  have hx23_8 : σ8.regs.get? Register.x23 = some viov3 :=
    obs_jal_other hobs8 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_7
  have hx26_8 : σ8.regs.get? Register.x26 = some vbase :=
    obs_jal_other hobs8 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_7
  have hx28_8 : σ8.regs.get? Register.x28 = some vt3 :=
    obs_jal_other hobs8 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_7
  have hmem8eq : σ8.mem = σ7.mem := hmem8
  have hmemfinal : σ8.mem = writeMap8 c.σ.mem
      (vsp + sign_extend (m := 64) (0x010#12)).toNat (sdData_val (sign_extend (m := 64)
        (Sail.BitVec.extractLsb vsel 31 0 + Sail.BitVec.extractLsb vtot 31 0))) := by
    rw [hmem8eq, hmem7, hmem6, hmem5, hmem4eq, hmem3', hmem2, hmem1]
  have hkeep8 : KeepRegs midRegs5 c.σ σ8 := by
    have k1 := keep_alu hobs1 (by decide) (keep_rfl midRegs5 c.σ)
    have k2 := keep_alu hobs2 (by decide) k1
    have k3 := keep_store hobs3 (by decide) k2
    have k4 := keep_btaken hobs4 (by decide) k3
    have k5 := keep_alu hobs5 (by decide) k4
    have k6 := keep_alu hobs6 (by decide) k5
    have k7 := keep_alu hobs7 (by decide) k6
    exact keep_jal hobs8 (by decide) k7
  refine ⟨⟨σ8, i8, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩, ?_, hG8, hpc8, hx1_8, hx10_8,
    hx11_8, hx12_8, hx2_8, hx5_8, hx6_8, hx8_8, hx16_8, hx20_8, hx22_8, hx23_8, hx26_8,
    hx28_8, hmemfinal, hi8, ⟨vmi8, hmi8⟩, hkeep8⟩
  exact (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans
    ((Steps.single hstep4).trans ((Steps.single hstep5).trans ((Steps.single hstep6).trans
    ((Steps.single hstep7).trans (Steps.single hstep8)))))))

/-! ## The composed segment: `0x800078ac` → the `__ssprint_r` call (`0x8000e908`)

`iov2ToSsprintCall_spec` runs the head (`li/beq/subw/bgtz/andi/bne/lw/add/sd/
addiw/sd/sd/li/sw/blt/addi/andi/beq/mv`) to the `bge t3,a6` at `0x80007900`,
case-splits its outcome, and finishes with `iov2Tail_spec` — both outcomes
covered, the selected `a5` written as an `if`. -/

theorem iov2ToSsprintCall_spec
    (vsp vt0 vt1 v8 vcur vlen vs4 vnd6 viov2 vbase vt3 vstr vtot : BitVec 64)
    (vcnt : BitVec 32)
    (c : Config)
    (hG : GoodState c.σ)
    (hload : SvfprintfSliceLoaded c.σ.mem)
    (hfp : FlushPinsLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x800078ac#64))
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx5 : c.σ.regs.get? Register.x5 = some vt0)
    (hx6 : c.σ.regs.get? Register.x6 = some vt1)
    (hx8 : c.σ.regs.get? Register.x8 = some v8)
    (hx12 : c.σ.regs.get? Register.x12 = some vcur)
    (hx16 : c.σ.regs.get? Register.x16 = some vlen)
    (hx20 : c.σ.regs.get? Register.x20 = some vs4)
    (hx22 : c.σ.regs.get? Register.x22 = some vnd6)
    (hx23 : c.σ.regs.get? Register.x23 = some viov2)
    (hx26 : c.σ.regs.get? Register.x26 = some vbase)
    (hx28 : c.σ.regs.get? Register.x28 = some vt3)
    (hc0 : c.σ.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat]? = some (vcnt.extractLsb' 0 8))
    (hc1 : c.σ.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 1]? = some (vcnt.extractLsb' 8 8))
    (hc2 : c.σ.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 2]? = some (vcnt.extractLsb' 16 8))
    (hc3 : c.σ.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 3]? = some (vcnt.extractLsb' 24 8))
    (htot : SlotHolds vsp 0x010 vtot c.σ.mem)
    (hstr : SlotHolds vsp 0x008 vstr c.σ.mem)
    (ht0ne : (vt0 == (0x080#64)) = false)
    (hsubwle : zopz0zI_s (0#64)
      (sign_extend (m := 64)
        (Sail.BitVec.extractLsb vs4 31 0 - Sail.BitVec.extractLsb vnd6 31 0)) = false)
    (hb256 : ((vt1 &&& sign_extend (m := 64) (0x100#12)) != (0#64)) = false)
    (hcnt2 : zopz0zI_s (0x007#64)
      (sign_extend (m := 64)
        (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64)
          + sign_extend (m := 64) (0x001#12)) 31 0)) = false)
    (hb4 : ((vt1 &&& sign_extend (m := 64) (0x004#12)) == (0#64)) = true)
    (hcurne : ((vcur + vnd6 != (0#64)) = true))
    (hspwin : tohostAddr + 16 + 64 ≤ vsp.toNat)
    (hsphi : vsp.toNat + 356 ≤ 0x100000000)
    (hspalign : vsp.toNat % 8 = 0)
    (hiovlo : 0x8000b000 ≤ viov2.toNat)
    (hiovhi : viov2.toNat + 16 ≤ 0x100000000)
    (hiovwin : tohostAddr + 16 ≤ viov2.toNat)
    (hiovalign : viov2.toNat % 8 = 0)
    (hiovdisj : viov2.toNat + 16 ≤ vsp.toNat ∨ vsp.toNat + 356 ≤ viov2.toNat)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x8000e908#64) ∧
      c'.σ.regs.get? Register.x1 = some (0x80008688#64) ∧
      c'.σ.regs.get? Register.x10 = some v8 ∧
      c'.σ.regs.get? Register.x11 = some vstr ∧
      c'.σ.regs.get? Register.x12 = some (vsp + sign_extend (m := 64) (0x0e0#12)) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.σ.regs.get? Register.x5 = some vt0 ∧
      c'.σ.regs.get? Register.x6 = some (vt1 &&& sign_extend (m := 64) (0x004#12)) ∧
      c'.σ.regs.get? Register.x8 = some v8 ∧
      c'.σ.regs.get? Register.x16 = some vlen ∧
      c'.σ.regs.get? Register.x20 = some (sign_extend (m := 64)
        (Sail.BitVec.extractLsb vs4 31 0 - Sail.BitVec.extractLsb vnd6 31 0)) ∧
      c'.σ.regs.get? Register.x22 = some vnd6 ∧
      c'.σ.regs.get? Register.x23 = some (viov2 + sign_extend (m := 64) (0x010#12)) ∧
      c'.σ.regs.get? Register.x26 = some vbase ∧
      c'.σ.regs.get? Register.x28 = some vt3 ∧
      c'.σ.mem = writeMap8
        (writeMap4
          (writeMap8
            (writeMap8
              (writeMap8 c.σ.mem
                (vsp + sign_extend (m := 64) (0x0f0#12)).toNat (sdData_val (vcur + vnd6)))
              viov2.toNat (sdData_val vbase))
            (viov2 + sign_extend (m := 64) (0x008#12)).toNat (sdData_val vnd6))
          (vsp + sign_extend (m := 64) (0x0e8#12)).toNat
            (swData (sign_extend (m := 64)
              (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64)
                + sign_extend (m := 64) (0x001#12)) 31 0))))
        (vsp + sign_extend (m := 64) (0x010#12)).toNat
          (sdData_val (sign_extend (m := 64)
            (Sail.BitVec.extractLsb (if zopz0zKzJ_s vt3 vlen = true then vt3 else vlen) 31 0
              + Sail.BitVec.extractLsb vtot 31 0))) ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) ∧
      -- post-widening: mid-register preservation (kills Spec26's `hmidregs`)
      KeepRegs midRegs5 c.σ c'.σ := by
  have htohv : tohostAddr = 0x8001ad00 := rfl
  have hsplo : 0x8000b000 ≤ vsp.toNat := by omega
  have hnw : vsp.toNat + 348 < 2 ^ 64 := by omega
  have hiovnw : viov2.toNat + 348 < 2 ^ 64 := by omega
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
  have hoff240 : (vsp + sign_extend (m := 64) (0x0f0#12)).toNat = vsp.toNat + 240 :=
    addoff_toNat_sn5 vsp (0x0f0#12) 240 (by omega) (by decide) hnw
  have hoff232 : (vsp + sign_extend (m := 64) (0x0e8#12)).toNat = vsp.toNat + 232 :=
    addoff_toNat_sn5 vsp (0x0e8#12) 232 (by omega) (by decide) hnw
  have hoff16 : (vsp + sign_extend (m := 64) (0x010#12)).toNat = vsp.toNat + 16 :=
    addoff_toNat_sn5 vsp (0x010#12) 16 (by omega) (by decide) hnw
  have hoff8 : (vsp + sign_extend (m := 64) (0x008#12)).toNat = vsp.toNat + 8 :=
    addoff_toNat_sn5 vsp (0x008#12) 8 (by omega) (by decide) hnw
  have hoffiov0 : (viov2 + sign_extend (m := 64) (0x000#12)).toNat = viov2.toNat :=
    addoff_toNat_sn5 viov2 (0x000#12) 0 (by omega) (by decide) hiovnw
  have hoffiov8 : (viov2 + sign_extend (m := 64) (0x008#12)).toNat = viov2.toNat + 8 :=
    addoff_toNat_sn5 viov2 (0x008#12) 8 (by omega) (by decide) hiovnw
  -- === 78ac: li a4,128  ⇒  x14 := 0x80 ===
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800078ac hload
  obtain ⟨σ1, i1, hs1s, hi1, hG1, hmem1, hobs1⟩ :=
    stepObs_alu c.σ c.tick c.steps (0x800078ac#64) vmi0 (0x08000713#32)
      (instruction.ITYPE (0x080#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0e#5, iop.ADDI))
      Register.x14 ((0#64) + sign_extend (m := 64) (0x080#12))
      (0x13#8) (0x07#8) (0x00#8) (0x08#8)
      hG hpc hmi0 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_08000713 (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (execute_itype_addi_char (0x080#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0e#5) (0#64)
        (afterNextPC (afterPrelude c.σ) (0x800078ac#64))
        (sigma3_alu c.σ (0x800078ac#64) Register.x14 ((0#64) + sign_extend (m := 64) (0x080#12)))
        (rX_bits_zero _) (wX_bits_x14 _ ((0#64) + sign_extend (m := 64) (0x080#12))))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1s
  have hpc1 : σ1.regs.get? Register.PC = some (0x800078b0#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x800078ac#64 : BitVec 64) 4 = (0x800078b0#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hx14_1 : σ1.regs.get? Register.x14 = some (0x080#64) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64) + sign_extend (m := 64) (0x080#12) : BitVec 64) = (0x080#64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx2_1 : σ1.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2
  have hx5_1 : σ1.regs.get? Register.x5 = some vt0 :=
    obs_alu_other hobs1 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5
  have hx6_1 : σ1.regs.get? Register.x6 = some vt1 :=
    obs_alu_other hobs1 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6
  have hx8_1 : σ1.regs.get? Register.x8 = some v8 :=
    obs_alu_other hobs1 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8
  have hx12_1 : σ1.regs.get? Register.x12 = some vcur :=
    obs_alu_other hobs1 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12
  have hx16_1 : σ1.regs.get? Register.x16 = some vlen :=
    obs_alu_other hobs1 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16
  have hx20_1 : σ1.regs.get? Register.x20 = some vs4 :=
    obs_alu_other hobs1 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20
  have hx22_1 : σ1.regs.get? Register.x22 = some vnd6 :=
    obs_alu_other hobs1 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22
  have hx23_1 : σ1.regs.get? Register.x23 = some viov2 :=
    obs_alu_other hobs1 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23
  have hx26_1 : σ1.regs.get? Register.x26 = some vbase :=
    obs_alu_other hobs1 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26
  have hx28_1 : σ1.regs.get? Register.x28 = some vt3 :=
    obs_alu_other hobs1 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28
  have hload1 : SvfprintfSliceLoaded σ1.mem := hmem1 ▸ hload
  have hfp1 : FlushPinsLoaded σ1.mem := hmem1 ▸ hfp
  have htot1 : SlotHolds vsp 0x010 vtot σ1.mem := hmem1 ▸ htot
  have hstr1 : SlotHolds vsp 0x008 vstr σ1.mem := hmem1 ▸ hstr
  have hc0_1 : σ1.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat]? = some (vcnt.extractLsb' 0 8) := hmem1 ▸ hc0
  have hc1_1 : σ1.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 1]? = some (vcnt.extractLsb' 8 8) := hmem1 ▸ hc1
  have hc2_1 : σ1.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 2]? = some (vcnt.extractLsb' 16 8) := hmem1 ▸ hc2
  have hc3_1 : σ1.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 3]? = some (vcnt.extractLsb' 24 8) := hmem1 ▸ hc3
  -- === 78b0: beq t0,a4,8548  (NOT taken: t0 ≠ 0x80) ===
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800078b0 hload1
  have hx5n2 : (rX_bits (regidx.Regidx 0x05#5)).run (afterNextPC (afterPrelude σ1) (0x800078b0#64))
      = .ok vt0 (afterNextPC (afterPrelude σ1) (0x800078b0#64)) := by
    apply rX_bits_x5
    rw [get?_afterNextPC σ1 (0x800078b0#64) _ (by decide) (by decide)]; exact hx5_1
  have hx14n2 : (rX_bits (regidx.Regidx 0x0e#5)).run (afterNextPC (afterPrelude σ1) (0x800078b0#64))
      = .ok (0x080#64) (afterNextPC (afterPrelude σ1) (0x800078b0#64)) := by
    apply rX_bits_x14
    rw [get?_afterNextPC σ1 (0x800078b0#64) _ (by decide) (by decide)]; exact hx14_1
  obtain ⟨σ2, i2, hs2s, hi2, hG2, hmem2, hobs2⟩ :=
    stepObs_branch_nottaken σ1 i1 (c.steps + 1) (0x800078b0#64) vmi1
      (0x0c98#13) (regidx.Regidx 0x05#5) (regidx.Regidx 0x0e#5) bop.BEQ (0x48e28ce3#32)
      (0xe3#8) (0x8c#8) (0xe2#8) (0x48#8)
      hG1 hpc1 hmi1 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_48e28ce3 (afterPrelude σ1)
        (by rw [get?_afterPrelude σ1 _ (by decide)]; exact hG1.misa)
        (by rw [get?_afterPrelude σ1 _ (by decide)]; exact hG1.cur_privilege)
        (by rw [get?_afterPrelude σ1 _ (by decide)]; exact hG1.mseccfg))
      (execute_btype_beq_nottaken (0x0c98#13) (regidx.Regidx 0x05#5) (regidx.Regidx 0x0e#5)
        vt0 (0x080#64) (afterNextPC (afterPrelude σ1) (0x800078b0#64))
        hx5n2 hx14n2 ht0ne)
      hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2s
  have hpc2 : σ2.regs.get? Register.PC = some (0x800078b4#64) := by
    have := obs_branch_nottaken_pc hobs2
    rwa [show BitVec.addInt (0x800078b0#64 : BitVec 64) 4 = (0x800078b4#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi2, hmi2⟩ := obs_branch_nottaken_minstret hobs2
  have hx2_2 : σ2.regs.get? Register.x2 = some vsp :=
    obs_branch_nottaken_other hobs2 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_1
  have hx5_2 : σ2.regs.get? Register.x5 = some vt0 :=
    obs_branch_nottaken_other hobs2 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_1
  have hx6_2 : σ2.regs.get? Register.x6 = some vt1 :=
    obs_branch_nottaken_other hobs2 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_1
  have hx8_2 : σ2.regs.get? Register.x8 = some v8 :=
    obs_branch_nottaken_other hobs2 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_1
  have hx12_2 : σ2.regs.get? Register.x12 = some vcur :=
    obs_branch_nottaken_other hobs2 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_1
  have hx16_2 : σ2.regs.get? Register.x16 = some vlen :=
    obs_branch_nottaken_other hobs2 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_1
  have hx20_2 : σ2.regs.get? Register.x20 = some vs4 :=
    obs_branch_nottaken_other hobs2 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_1
  have hx22_2 : σ2.regs.get? Register.x22 = some vnd6 :=
    obs_branch_nottaken_other hobs2 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_1
  have hx23_2 : σ2.regs.get? Register.x23 = some viov2 :=
    obs_branch_nottaken_other hobs2 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_1
  have hx26_2 : σ2.regs.get? Register.x26 = some vbase :=
    obs_branch_nottaken_other hobs2 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_1
  have hx28_2 : σ2.regs.get? Register.x28 = some vt3 :=
    obs_branch_nottaken_other hobs2 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_1
  have hload2 : SvfprintfSliceLoaded σ2.mem := hmem2 ▸ hload1
  have hfp2 : FlushPinsLoaded σ2.mem := hmem2 ▸ hfp1
  have htot2 : SlotHolds vsp 0x010 vtot σ2.mem := hmem2 ▸ htot1
  have hstr2 : SlotHolds vsp 0x008 vstr σ2.mem := hmem2 ▸ hstr1
  have hc0_2 : σ2.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat]? = some (vcnt.extractLsb' 0 8) := hmem2 ▸ hc0_1
  have hc1_2 : σ2.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 1]? = some (vcnt.extractLsb' 8 8) := hmem2 ▸ hc1_1
  have hc2_2 : σ2.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 2]? = some (vcnt.extractLsb' 16 8) := hmem2 ▸ hc2_1
  have hc3_2 : σ2.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 3]? = some (vcnt.extractLsb' 24 8) := hmem2 ▸ hc3_1
  -- === 78b4: subw s4,s4,s6  ⇒  x20 := sext32(lo32 vs4 − lo32 vnd6) ===
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800078b4 hload2
  have hx20n3 : (afterNextPC (afterPrelude σ2) (0x800078b4#64)).regs.get? Register.x20 = some vs4 := by
    rw [get?_afterNextPC σ2 (0x800078b4#64) _ (by decide) (by decide)]; exact hx20_2
  have hx22n3 : (afterNextPC (afterPrelude σ2) (0x800078b4#64)).regs.get? Register.x22 = some vnd6 := by
    rw [get?_afterNextPC σ2 (0x800078b4#64) _ (by decide) (by decide)]; exact hx22_2
  obtain ⟨σ3, i3, hs3s, hi3, hG3, hmem3, hobs3⟩ :=
    stepObs_alu σ2 i2 (c.steps + 1 + 1) (0x800078b4#64) vmi2 (0x416a0a3b#32)
      (instruction.RTYPEW (regidx.Regidx 0x16#5, regidx.Regidx 0x14#5, regidx.Regidx 0x14#5, ropw.SUBW))
      Register.x20 (sign_extend (m := 64)
        (Sail.BitVec.extractLsb vs4 31 0 - Sail.BitVec.extractLsb vnd6 31 0))
      (0x3b#8) (0x0a#8) (0x6a#8) (0x41#8)
      hG2 hpc2 hmi2 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_416a0a3b (afterPrelude σ2)
        (by rw [get?_afterPrelude σ2 _ (by decide)]; exact hG2.misa)
        (by rw [get?_afterPrelude σ2 _ (by decide)]; exact hG2.cur_privilege)
        (by rw [get?_afterPrelude σ2 _ (by decide)]; exact hG2.mseccfg))
      (execute_rtypew_subw_char (regidx.Regidx 0x16#5) (regidx.Regidx 0x14#5) (regidx.Regidx 0x14#5)
        vs4 vnd6 (afterNextPC (afterPrelude σ2) (0x800078b4#64))
        (sigma3_alu σ2 (0x800078b4#64) Register.x20 (sign_extend (m := 64)
          (Sail.BitVec.extractLsb vs4 31 0 - Sail.BitVec.extractLsb vnd6 31 0)))
        (rX_bits_x20 _ vs4 hx20n3) (rX_bits_x22 _ vnd6 hx22n3)
        (wX_bits_x20 _ (sign_extend (m := 64)
          (Sail.BitVec.extractLsb vs4 31 0 - Sail.BitVec.extractLsb vnd6 31 0))))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3s
  have hpc3 : σ3.regs.get? Register.PC = some (0x800078b8#64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x800078b4#64 : BitVec 64) 4 = (0x800078b8#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hx20_3 : σ3.regs.get? Register.x20 = some (sign_extend (m := 64)
      (Sail.BitVec.extractLsb vs4 31 0 - Sail.BitVec.extractLsb vnd6 31 0)) :=
    obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx2_3 : σ3.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs3 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_2
  have hx5_3 : σ3.regs.get? Register.x5 = some vt0 :=
    obs_alu_other hobs3 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_2
  have hx6_3 : σ3.regs.get? Register.x6 = some vt1 :=
    obs_alu_other hobs3 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_2
  have hx8_3 : σ3.regs.get? Register.x8 = some v8 :=
    obs_alu_other hobs3 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_2
  have hx12_3 : σ3.regs.get? Register.x12 = some vcur :=
    obs_alu_other hobs3 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_2
  have hx16_3 : σ3.regs.get? Register.x16 = some vlen :=
    obs_alu_other hobs3 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_2
  have hx22_3 : σ3.regs.get? Register.x22 = some vnd6 :=
    obs_alu_other hobs3 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_2
  have hx23_3 : σ3.regs.get? Register.x23 = some viov2 :=
    obs_alu_other hobs3 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_2
  have hx26_3 : σ3.regs.get? Register.x26 = some vbase :=
    obs_alu_other hobs3 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_2
  have hx28_3 : σ3.regs.get? Register.x28 = some vt3 :=
    obs_alu_other hobs3 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_2
  have hload3 : SvfprintfSliceLoaded σ3.mem := hmem3 ▸ hload2
  have hfp3 : FlushPinsLoaded σ3.mem := hmem3 ▸ hfp2
  have htot3 : SlotHolds vsp 0x010 vtot σ3.mem := hmem3 ▸ htot2
  have hstr3 : SlotHolds vsp 0x008 vstr σ3.mem := hmem3 ▸ hstr2
  have hc0_3 : σ3.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat]? = some (vcnt.extractLsb' 0 8) := hmem3 ▸ hc0_2
  have hc1_3 : σ3.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 1]? = some (vcnt.extractLsb' 8 8) := hmem3 ▸ hc1_2
  have hc2_3 : σ3.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 2]? = some (vcnt.extractLsb' 16 8) := hmem3 ▸ hc2_2
  have hc3_3 : σ3.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 3]? = some (vcnt.extractLsb' 24 8) := hmem3 ▸ hc3_2
  -- === 78b8: bgtz s4,7cec  (NOT taken: 0 ≮ subw result) ===
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800078b8 hload3
  have hx20n4 : (rX_bits (regidx.Regidx 0x14#5)).run (afterNextPC (afterPrelude σ3) (0x800078b8#64))
      = .ok (sign_extend (m := 64)
        (Sail.BitVec.extractLsb vs4 31 0 - Sail.BitVec.extractLsb vnd6 31 0))
        (afterNextPC (afterPrelude σ3) (0x800078b8#64)) := by
    apply rX_bits_x20
    rw [get?_afterNextPC σ3 (0x800078b8#64) _ (by decide) (by decide)]; exact hx20_3
  obtain ⟨σ4, i4, hs4s, hi4, hG4, hmem4, hobs4⟩ :=
    stepObs_branch_nottaken σ3 i3 (c.steps + 1 + 1 + 1) (0x800078b8#64) vmi3
      (0x0434#13) (regidx.Regidx 0x00#5) (regidx.Regidx 0x14#5) bop.BLT (0x43404a63#32)
      (0x63#8) (0x4a#8) (0x40#8) (0x43#8)
      hG3 hpc3 hmi3 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_43404a63 (afterPrelude σ3)
        (by rw [get?_afterPrelude σ3 _ (by decide)]; exact hG3.misa)
        (by rw [get?_afterPrelude σ3 _ (by decide)]; exact hG3.cur_privilege)
        (by rw [get?_afterPrelude σ3 _ (by decide)]; exact hG3.mseccfg))
      (execute_btype_blt_nottaken (0x0434#13) (regidx.Regidx 0x00#5) (regidx.Regidx 0x14#5)
        (0#64) (sign_extend (m := 64)
          (Sail.BitVec.extractLsb vs4 31 0 - Sail.BitVec.extractLsb vnd6 31 0))
        (afterNextPC (afterPrelude σ3) (0x800078b8#64))
        (rX_bits_zero _) hx20n4 hsubwle)
      hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi3
  have hstep4 : Step ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ := hs4s
  have hpc4 : σ4.regs.get? Register.PC = some (0x800078bc#64) := by
    have := obs_branch_nottaken_pc hobs4
    rwa [show BitVec.addInt (0x800078b8#64 : BitVec 64) 4 = (0x800078bc#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi4, hmi4⟩ := obs_branch_nottaken_minstret hobs4
  have hx2_4 : σ4.regs.get? Register.x2 = some vsp :=
    obs_branch_nottaken_other hobs4 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_3
  have hx5_4 : σ4.regs.get? Register.x5 = some vt0 :=
    obs_branch_nottaken_other hobs4 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_3
  have hx6_4 : σ4.regs.get? Register.x6 = some vt1 :=
    obs_branch_nottaken_other hobs4 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_3
  have hx8_4 : σ4.regs.get? Register.x8 = some v8 :=
    obs_branch_nottaken_other hobs4 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_3
  have hx12_4 : σ4.regs.get? Register.x12 = some vcur :=
    obs_branch_nottaken_other hobs4 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_3
  have hx16_4 : σ4.regs.get? Register.x16 = some vlen :=
    obs_branch_nottaken_other hobs4 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_3
  have hx20_4 : σ4.regs.get? Register.x20 = some (sign_extend (m := 64)
      (Sail.BitVec.extractLsb vs4 31 0 - Sail.BitVec.extractLsb vnd6 31 0)) :=
    obs_branch_nottaken_other hobs4 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_3
  have hx22_4 : σ4.regs.get? Register.x22 = some vnd6 :=
    obs_branch_nottaken_other hobs4 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_3
  have hx23_4 : σ4.regs.get? Register.x23 = some viov2 :=
    obs_branch_nottaken_other hobs4 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_3
  have hx26_4 : σ4.regs.get? Register.x26 = some vbase :=
    obs_branch_nottaken_other hobs4 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_3
  have hx28_4 : σ4.regs.get? Register.x28 = some vt3 :=
    obs_branch_nottaken_other hobs4 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_3
  have hload4 : SvfprintfSliceLoaded σ4.mem := hmem4 ▸ hload3
  have hfp4 : FlushPinsLoaded σ4.mem := hmem4 ▸ hfp3
  have htot4 : SlotHolds vsp 0x010 vtot σ4.mem := hmem4 ▸ htot3
  have hstr4 : SlotHolds vsp 0x008 vstr σ4.mem := hmem4 ▸ hstr3
  have hc0_4 : σ4.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat]? = some (vcnt.extractLsb' 0 8) := hmem4 ▸ hc0_3
  have hc1_4 : σ4.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 1]? = some (vcnt.extractLsb' 8 8) := hmem4 ▸ hc1_3
  have hc2_4 : σ4.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 2]? = some (vcnt.extractLsb' 16 8) := hmem4 ▸ hc2_3
  have hc3_4 : σ4.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 3]? = some (vcnt.extractLsb' 24 8) := hmem4 ▸ hc3_3
  -- === 78bc: andi a4,t1,256  ⇒  x14 := vt1 &&& 0x100 ===
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800078bc hload4
  have hx6n5 : (afterNextPC (afterPrelude σ4) (0x800078bc#64)).regs.get? Register.x6 = some vt1 := by
    rw [get?_afterNextPC σ4 (0x800078bc#64) _ (by decide) (by decide)]; exact hx6_4
  obtain ⟨σ5, i5, hs5s, hi5, hG5, hmem5, hobs5⟩ :=
    stepObs_alu σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x800078bc#64) vmi4 (0x10037713#32)
      (instruction.ITYPE (0x100#12, regidx.Regidx 0x06#5, regidx.Regidx 0x0e#5, iop.ANDI))
      Register.x14 (vt1 &&& sign_extend (m := 64) (0x100#12))
      (0x13#8) (0x77#8) (0x03#8) (0x10#8)
      hG4 hpc4 hmi4 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_10037713 (afterPrelude σ4)
        (by rw [get?_afterPrelude σ4 _ (by decide)]; exact hG4.misa)
        (by rw [get?_afterPrelude σ4 _ (by decide)]; exact hG4.cur_privilege)
        (by rw [get?_afterPrelude σ4 _ (by decide)]; exact hG4.mseccfg))
      (execute_itype_andi_char (0x100#12) (regidx.Regidx 0x06#5) (regidx.Regidx 0x0e#5) vt1
        (afterNextPC (afterPrelude σ4) (0x800078bc#64))
        (sigma3_alu σ4 (0x800078bc#64) Register.x14 (vt1 &&& sign_extend (m := 64) (0x100#12)))
        (rX_bits_x6 _ vt1 hx6n5) (wX_bits_x14 _ (vt1 &&& sign_extend (m := 64) (0x100#12))))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi4
  have hstep5 : Step ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ := hs5s
  have hpc5 : σ5.regs.get? Register.PC = some (0x800078c0#64) := by
    have := obs_alu_pc hobs5
    rwa [show BitVec.addInt (0x800078bc#64 : BitVec 64) 4 = (0x800078c0#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi5, hmi5⟩ := obs_alu_minstret hobs5
  have hx14_5 : σ5.regs.get? Register.x14 = some (vt1 &&& sign_extend (m := 64) (0x100#12)) :=
    obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx2_5 : σ5.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs5 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_4
  have hx5_5 : σ5.regs.get? Register.x5 = some vt0 :=
    obs_alu_other hobs5 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_4
  have hx6_5 : σ5.regs.get? Register.x6 = some vt1 :=
    obs_alu_other hobs5 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_4
  have hx8_5 : σ5.regs.get? Register.x8 = some v8 :=
    obs_alu_other hobs5 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_4
  have hx12_5 : σ5.regs.get? Register.x12 = some vcur :=
    obs_alu_other hobs5 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_4
  have hx16_5 : σ5.regs.get? Register.x16 = some vlen :=
    obs_alu_other hobs5 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_4
  have hx20_5 : σ5.regs.get? Register.x20 = some (sign_extend (m := 64)
      (Sail.BitVec.extractLsb vs4 31 0 - Sail.BitVec.extractLsb vnd6 31 0)) :=
    obs_alu_other hobs5 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_4
  have hx22_5 : σ5.regs.get? Register.x22 = some vnd6 :=
    obs_alu_other hobs5 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_4
  have hx23_5 : σ5.regs.get? Register.x23 = some viov2 :=
    obs_alu_other hobs5 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_4
  have hx26_5 : σ5.regs.get? Register.x26 = some vbase :=
    obs_alu_other hobs5 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_4
  have hx28_5 : σ5.regs.get? Register.x28 = some vt3 :=
    obs_alu_other hobs5 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_4
  have hload5 : SvfprintfSliceLoaded σ5.mem := hmem5 ▸ hload4
  have hfp5 : FlushPinsLoaded σ5.mem := hmem5 ▸ hfp4
  have htot5 : SlotHolds vsp 0x010 vtot σ5.mem := hmem5 ▸ htot4
  have hstr5 : SlotHolds vsp 0x008 vstr σ5.mem := hmem5 ▸ hstr4
  have hc0_5 : σ5.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat]? = some (vcnt.extractLsb' 0 8) := hmem5 ▸ hc0_4
  have hc1_5 : σ5.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 1]? = some (vcnt.extractLsb' 8 8) := hmem5 ▸ hc1_4
  have hc2_5 : σ5.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 2]? = some (vcnt.extractLsb' 16 8) := hmem5 ▸ hc2_4
  have hc3_5 : σ5.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 3]? = some (vcnt.extractLsb' 24 8) := hmem5 ▸ hc3_4
  -- === 78c0: bnez a4,7e00  (NOT taken: flags&0x100 = 0) ===
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800078c0 hload5
  have hx14n6 : (rX_bits (regidx.Regidx 0x0e#5)).run (afterNextPC (afterPrelude σ5) (0x800078c0#64))
      = .ok (vt1 &&& sign_extend (m := 64) (0x100#12))
        (afterNextPC (afterPrelude σ5) (0x800078c0#64)) := by
    apply rX_bits_x14
    rw [get?_afterNextPC σ5 (0x800078c0#64) _ (by decide) (by decide)]; exact hx14_5
  obtain ⟨σ6, i6, hs6s, hi6, hG6, hmem6, hobs6⟩ :=
    stepObs_branch_nottaken σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x800078c0#64) vmi5
      (0x0540#13) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x00#5) bop.BNE (0x54071063#32)
      (0x63#8) (0x10#8) (0x07#8) (0x54#8)
      hG5 hpc5 hmi5 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_54071063 (afterPrelude σ5)
        (by rw [get?_afterPrelude σ5 _ (by decide)]; exact hG5.misa)
        (by rw [get?_afterPrelude σ5 _ (by decide)]; exact hG5.cur_privilege)
        (by rw [get?_afterPrelude σ5 _ (by decide)]; exact hG5.mseccfg))
      (execute_btype_bne_nottaken (0x0540#13) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x00#5)
        (vt1 &&& sign_extend (m := 64) (0x100#12)) (0#64)
        (afterNextPC (afterPrelude σ5) (0x800078c0#64))
        hx14n6 (rX_bits_zero _) hb256)
      hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi5
  have hstep6 : Step ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs6s
  have hpc6 : σ6.regs.get? Register.PC = some (0x800078c4#64) := by
    have := obs_branch_nottaken_pc hobs6
    rwa [show BitVec.addInt (0x800078c0#64 : BitVec 64) 4 = (0x800078c4#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi6, hmi6⟩ := obs_branch_nottaken_minstret hobs6
  have hx2_6 : σ6.regs.get? Register.x2 = some vsp :=
    obs_branch_nottaken_other hobs6 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_5
  have hx5_6 : σ6.regs.get? Register.x5 = some vt0 :=
    obs_branch_nottaken_other hobs6 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_5
  have hx6_6 : σ6.regs.get? Register.x6 = some vt1 :=
    obs_branch_nottaken_other hobs6 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_5
  have hx8_6 : σ6.regs.get? Register.x8 = some v8 :=
    obs_branch_nottaken_other hobs6 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_5
  have hx12_6 : σ6.regs.get? Register.x12 = some vcur :=
    obs_branch_nottaken_other hobs6 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_5
  have hx16_6 : σ6.regs.get? Register.x16 = some vlen :=
    obs_branch_nottaken_other hobs6 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_5
  have hx20_6 : σ6.regs.get? Register.x20 = some (sign_extend (m := 64)
      (Sail.BitVec.extractLsb vs4 31 0 - Sail.BitVec.extractLsb vnd6 31 0)) :=
    obs_branch_nottaken_other hobs6 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_5
  have hx22_6 : σ6.regs.get? Register.x22 = some vnd6 :=
    obs_branch_nottaken_other hobs6 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_5
  have hx23_6 : σ6.regs.get? Register.x23 = some viov2 :=
    obs_branch_nottaken_other hobs6 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_5
  have hx26_6 : σ6.regs.get? Register.x26 = some vbase :=
    obs_branch_nottaken_other hobs6 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_5
  have hx28_6 : σ6.regs.get? Register.x28 = some vt3 :=
    obs_branch_nottaken_other hobs6 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_5
  have hload6 : SvfprintfSliceLoaded σ6.mem := hmem6 ▸ hload5
  have hfp6 : FlushPinsLoaded σ6.mem := hmem6 ▸ hfp5
  have htot6 : SlotHolds vsp 0x010 vtot σ6.mem := hmem6 ▸ htot5
  have hstr6 : SlotHolds vsp 0x008 vstr σ6.mem := hmem6 ▸ hstr5
  have hc0_6 : σ6.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat]? = some (vcnt.extractLsb' 0 8) := hmem6 ▸ hc0_5
  have hc1_6 : σ6.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 1]? = some (vcnt.extractLsb' 8 8) := hmem6 ▸ hc1_5
  have hc2_6 : σ6.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 2]? = some (vcnt.extractLsb' 16 8) := hmem6 ▸ hc2_5
  have hc3_6 : σ6.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 3]? = some (vcnt.extractLsb' 24 8) := hmem6 ▸ hc3_5
  -- === 78c4: lw a5,232(sp)  ⇒  x15 := sext vcnt ===
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800078c4 hload6
  have hx2n7 : (afterNextPC (afterPrelude σ6) (0x800078c4#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ6 (0x800078c4#64) _ (by decide) (by decide)]; exact hx2_6
  obtain ⟨σ7, i7, hs7s, hi7, hG7, hmem7, hobs7⟩ :=
    stepObs_alu σ6 i6 (c.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x800078c4#64) vmi6 (0x0e812783#32)
      (instruction.LOAD (0x0e8#12, regidx.Regidx 0x02#5, regidx.Regidx 0x0f#5, false, 4))
      Register.x15 (sign_extend (m := 64)
        ((((vcnt.extractLsb' 24 8).append (vcnt.extractLsb' 16 8)).append
          (vcnt.extractLsb' 8 8)).append (vcnt.extractLsb' 0 8) : BitVec (8 * 4)))
      (0x83#8) (0x27#8) (0x81#8) (0x0e#8)
      hG6 hpc6 hmi6 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_0e812783 (afterPrelude σ6)
        (by rw [get?_afterPrelude σ6 _ (by decide)]; exact hG6.misa)
        (by rw [get?_afterPrelude σ6 _ (by decide)]; exact hG6.cur_privilege)
        (by rw [get?_afterPrelude σ6 _ (by decide)]; exact hG6.mseccfg))
      (exec_lw σ6 (0x800078c4#64) (0x0e8#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x0f#5)
        (sigma3_alu σ6 (0x800078c4#64) Register.x15 (sign_extend (m := 64)
          ((((vcnt.extractLsb' 24 8).append (vcnt.extractLsb' 16 8)).append
            (vcnt.extractLsb' 8 8)).append (vcnt.extractLsb' 0 8) : BitVec (8 * 4))))
        vsp (vcnt.extractLsb' 0 8) (vcnt.extractLsb' 8 8) (vcnt.extractLsb' 16 8)
        (vcnt.extractLsb' 24 8)
        hG6 (rX_bits_x2 _ vsp hx2n7)
        (wX_bits_x15 _ (sign_extend (m := 64)
          ((((vcnt.extractLsb' 24 8).append (vcnt.extractLsb' 16 8)).append
            (vcnt.extractLsb' 8 8)).append (vcnt.extractLsb' 0 8) : BitVec (8 * 4))))
        (by rw [hoff232]; omega) (by rw [hoff232]; omega) (Or.inr (by rw [hoff232]; omega))
        (by rw [hoff232]; omega) hc0_6 hc1_6 hc2_6 hc3_6)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi6
  have hstep7 : Step ⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ7, i7, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs7s
  have hpc7 : σ7.regs.get? Register.PC = some (0x800078c8#64) := by
    have := obs_alu_pc hobs7
    rwa [show BitVec.addInt (0x800078c4#64 : BitVec 64) 4 = (0x800078c8#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi7, hmi7⟩ := obs_alu_minstret hobs7
  have hlwval : (sign_extend (m := 64)
      ((((vcnt.extractLsb' 24 8).append (vcnt.extractLsb' 16 8)).append
        (vcnt.extractLsb' 8 8)).append (vcnt.extractLsb' 0 8) : BitVec (8 * 4)))
      = (sign_extend (m := 64) vcnt : BitVec 64) := by
    have hreassemble : ((((vcnt.extractLsb' 24 8).append (vcnt.extractLsb' 16 8)).append
        (vcnt.extractLsb' 8 8)).append (vcnt.extractLsb' 0 8) : BitVec (8 * 4)) = vcnt := by
      apply BitVec.eq_of_toNat_eq
      rw [word_toNat_recon]
      simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      have := vcnt.isLt
      omega
    rw [hreassemble]
  have hx15_7 : σ7.regs.get? Register.x15 = some (sign_extend (m := 64) vcnt : BitVec 64) := by
    have := obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hlwval] at this
  have hx2_7 : σ7.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs7 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_6
  have hx5_7 : σ7.regs.get? Register.x5 = some vt0 :=
    obs_alu_other hobs7 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_6
  have hx6_7 : σ7.regs.get? Register.x6 = some vt1 :=
    obs_alu_other hobs7 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_6
  have hx8_7 : σ7.regs.get? Register.x8 = some v8 :=
    obs_alu_other hobs7 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_6
  have hx12_7 : σ7.regs.get? Register.x12 = some vcur :=
    obs_alu_other hobs7 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_6
  have hx16_7 : σ7.regs.get? Register.x16 = some vlen :=
    obs_alu_other hobs7 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_6
  have hx20_7 : σ7.regs.get? Register.x20 = some (sign_extend (m := 64)
      (Sail.BitVec.extractLsb vs4 31 0 - Sail.BitVec.extractLsb vnd6 31 0)) :=
    obs_alu_other hobs7 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_6
  have hx22_7 : σ7.regs.get? Register.x22 = some vnd6 :=
    obs_alu_other hobs7 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_6
  have hx23_7 : σ7.regs.get? Register.x23 = some viov2 :=
    obs_alu_other hobs7 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_6
  have hx26_7 : σ7.regs.get? Register.x26 = some vbase :=
    obs_alu_other hobs7 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_6
  have hx28_7 : σ7.regs.get? Register.x28 = some vt3 :=
    obs_alu_other hobs7 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_6
  have hload7 : SvfprintfSliceLoaded σ7.mem := hmem7 ▸ hload6
  have hfp7 : FlushPinsLoaded σ7.mem := hmem7 ▸ hfp6
  have htot7 : SlotHolds vsp 0x010 vtot σ7.mem := hmem7 ▸ htot6
  have hstr7 : SlotHolds vsp 0x008 vstr σ7.mem := hmem7 ▸ hstr6
  -- === 78c8: add a2,a2,s6  ⇒  x12 := vcur + vnd6 ===
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800078c8 hload7
  have hx12n8 : (afterNextPC (afterPrelude σ7) (0x800078c8#64)).regs.get? Register.x12 = some vcur := by
    rw [get?_afterNextPC σ7 (0x800078c8#64) _ (by decide) (by decide)]; exact hx12_7
  have hx22n8 : (afterNextPC (afterPrelude σ7) (0x800078c8#64)).regs.get? Register.x22 = some vnd6 := by
    rw [get?_afterNextPC σ7 (0x800078c8#64) _ (by decide) (by decide)]; exact hx22_7
  obtain ⟨σ8, i8, hs8s, hi8, hG8, hmem8, hobs8⟩ :=
    stepObs_alu σ7 i7 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800078c8#64) vmi7 (0x01660633#32)
      (instruction.RTYPE (regidx.Regidx 0x16#5, regidx.Regidx 0x0c#5, regidx.Regidx 0x0c#5, rop.ADD))
      Register.x12 (vcur + vnd6)
      (0x33#8) (0x06#8) (0x66#8) (0x01#8)
      hG7 hpc7 hmi7 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_01660633 (afterPrelude σ7)
        (by rw [get?_afterPrelude σ7 _ (by decide)]; exact hG7.misa)
        (by rw [get?_afterPrelude σ7 _ (by decide)]; exact hG7.cur_privilege)
        (by rw [get?_afterPrelude σ7 _ (by decide)]; exact hG7.mseccfg))
      (execute_rtype_add_char (regidx.Regidx 0x16#5) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0c#5)
        vcur vnd6 (afterNextPC (afterPrelude σ7) (0x800078c8#64))
        (sigma3_alu σ7 (0x800078c8#64) Register.x12 (vcur + vnd6))
        (rX_bits_x12 _ vcur hx12n8) (rX_bits_x22 _ vnd6 hx22n8)
        (wX_bits_x12 _ (vcur + vnd6)))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi7
  have hstep8 : Step ⟨σ7, i7, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ8, i8, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs8s
  have hpc8 : σ8.regs.get? Register.PC = some (0x800078cc#64) := by
    have := obs_alu_pc hobs8
    rwa [show BitVec.addInt (0x800078c8#64 : BitVec 64) 4 = (0x800078cc#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi8, hmi8⟩ := obs_alu_minstret hobs8
  have hx12_8 : σ8.regs.get? Register.x12 = some (vcur + vnd6) :=
    obs_alu_rd hobs8 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx2_8 : σ8.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs8 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_7
  have hx5_8 : σ8.regs.get? Register.x5 = some vt0 :=
    obs_alu_other hobs8 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_7
  have hx6_8 : σ8.regs.get? Register.x6 = some vt1 :=
    obs_alu_other hobs8 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_7
  have hx8_8 : σ8.regs.get? Register.x8 = some v8 :=
    obs_alu_other hobs8 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_7
  have hx15_8 : σ8.regs.get? Register.x15 = some (sign_extend (m := 64) vcnt : BitVec 64) :=
    obs_alu_other hobs8 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_7
  have hx16_8 : σ8.regs.get? Register.x16 = some vlen :=
    obs_alu_other hobs8 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_7
  have hx20_8 : σ8.regs.get? Register.x20 = some (sign_extend (m := 64)
      (Sail.BitVec.extractLsb vs4 31 0 - Sail.BitVec.extractLsb vnd6 31 0)) :=
    obs_alu_other hobs8 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_7
  have hx22_8 : σ8.regs.get? Register.x22 = some vnd6 :=
    obs_alu_other hobs8 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_7
  have hx23_8 : σ8.regs.get? Register.x23 = some viov2 :=
    obs_alu_other hobs8 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_7
  have hx26_8 : σ8.regs.get? Register.x26 = some vbase :=
    obs_alu_other hobs8 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_7
  have hx28_8 : σ8.regs.get? Register.x28 = some vt3 :=
    obs_alu_other hobs8 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_7
  have hload8 : SvfprintfSliceLoaded σ8.mem := hmem8 ▸ hload7
  have hfp8 : FlushPinsLoaded σ8.mem := hmem8 ▸ hfp7
  have htot8 : SlotHolds vsp 0x010 vtot σ8.mem := hmem8 ▸ htot7
  have hstr8 : SlotHolds vsp 0x008 vstr σ8.mem := hmem8 ▸ hstr7
  -- === 78cc: sd a2,240(sp)  ⇒  mem[sp+240] := cursor ===
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800078cc hload8
  have hx2n9 : (afterNextPC (afterPrelude σ8) (0x800078cc#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ8 (0x800078cc#64) _ (by decide) (by decide)]; exact hx2_8
  have hx12n9 : (afterNextPC (afterPrelude σ8) (0x800078cc#64)).regs.get? Register.x12 = some (vcur + vnd6) := by
    rw [get?_afterNextPC σ8 (0x800078cc#64) _ (by decide) (by decide)]; exact hx12_8
  obtain ⟨σ9, i9, hs9s, hi9, hG9, hmem9, hobs9⟩ :=
    stepObs_store σ8 i8 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800078cc#64) vmi8 (0x0ec13823#32)
      (instruction.STORE (0x0f0#12, regidx.Regidx 0x0c#5, regidx.Regidx 0x02#5, 8))
      (writeMap8 (afterNextPC (afterPrelude σ8) (0x800078cc#64)).mem
        (vsp + sign_extend (m := 64) (0x0f0#12)).toNat (sdData_val (vcur + vnd6)))
      (0x23#8) (0x38#8) (0xc1#8) (0x0e#8)
      hG8 hpc8 hmi8 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_0ec13823 (afterPrelude σ8)
        (by rw [get?_afterPrelude σ8 _ (by decide)]; exact hG8.misa)
        (by rw [get?_afterPrelude σ8 _ (by decide)]; exact hG8.cur_privilege)
        (by rw [get?_afterPrelude σ8 _ (by decide)]; exact hG8.mseccfg))
      (exec_sd_val σ8 (0x800078cc#64) (0x0f0#12) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x02#5)
        vsp (vcur + vnd6) hG8 (rX_bits_x2 _ vsp hx2n9) (rX_bits_x12 _ (vcur + vnd6) hx12n9)
        (by rw [hoff240]; omega) (by rw [hoff240]; omega) (by rw [hoff240]; omega) (by rw [hoff240]; omega))
      hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi8
  have hstep9 : Step ⟨σ8, i8, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ9, i9, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs9s
  have hpc9 : σ9.regs.get? Register.PC = some (0x800078d0#64) := by
    have := obs_store_pc_sn4 hobs9
    rwa [show BitVec.addInt (0x800078cc#64 : BitVec 64) 4 = (0x800078d0#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi9, hmi9⟩ := obs_store_minstret_sn4 hobs9
  have hx2_9 : σ9.regs.get? Register.x2 = some vsp :=
    obs_store_other_sn4 Register.x2 hobs9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_8
  have hx5_9 : σ9.regs.get? Register.x5 = some vt0 :=
    obs_store_other_sn4 Register.x5 hobs9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_8
  have hx6_9 : σ9.regs.get? Register.x6 = some vt1 :=
    obs_store_other_sn4 Register.x6 hobs9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_8
  have hx8_9 : σ9.regs.get? Register.x8 = some v8 :=
    obs_store_other_sn4 Register.x8 hobs9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_8
  have hx12_9 : σ9.regs.get? Register.x12 = some (vcur + vnd6) :=
    obs_store_other_sn4 Register.x12 hobs9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_8
  have hx15_9 : σ9.regs.get? Register.x15 = some (sign_extend (m := 64) vcnt : BitVec 64) :=
    obs_store_other_sn4 Register.x15 hobs9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_8
  have hx16_9 : σ9.regs.get? Register.x16 = some vlen :=
    obs_store_other_sn4 Register.x16 hobs9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_8
  have hx20_9 : σ9.regs.get? Register.x20 = some (sign_extend (m := 64)
      (Sail.BitVec.extractLsb vs4 31 0 - Sail.BitVec.extractLsb vnd6 31 0)) :=
    obs_store_other_sn4 Register.x20 hobs9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_8
  have hx22_9 : σ9.regs.get? Register.x22 = some vnd6 :=
    obs_store_other_sn4 Register.x22 hobs9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_8
  have hx23_9 : σ9.regs.get? Register.x23 = some viov2 :=
    obs_store_other_sn4 Register.x23 hobs9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_8
  have hx26_9 : σ9.regs.get? Register.x26 = some vbase :=
    obs_store_other_sn4 Register.x26 hobs9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_8
  have hx28_9 : σ9.regs.get? Register.x28 = some vt3 :=
    obs_store_other_sn4 Register.x28 hobs9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_8
  have hNP9 : (afterNextPC (afterPrelude σ8) (0x800078cc#64)).mem = σ8.mem := rfl
  have hmem9' : σ9.mem = writeMap8 σ8.mem
      (vsp + sign_extend (m := 64) (0x0f0#12)).toNat (sdData_val (vcur + vnd6)) := by
    rw [hmem9, hNP9]
  have hload9 : SvfprintfSliceLoaded σ9.mem := by
    rw [hmem9']; exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff240]; omega) hload8
  have hfp9 : FlushPinsLoaded σ9.mem := by
    rw [hmem9']; exact flushPins_writeMap8_fl _ _ _ (by rw [hoff240]; omega) hfp8
  have htot9 : SlotHolds vsp 0x010 vtot σ9.mem := by
    rw [hmem9']; exact slotHolds_writeMap8 vsp 0x010 vtot _
      ((vsp + sign_extend (m := 64) (0x0f0#12)).toNat) _
      (Or.inl (by rw [hoff16, hoff240]; omega)) htot8
  have hstr9 : SlotHolds vsp 0x008 vstr σ9.mem := by
    rw [hmem9']; exact slotHolds_writeMap8 vsp 0x008 vstr _
      ((vsp + sign_extend (m := 64) (0x0f0#12)).toNat) _
      (Or.inl (by rw [hoff8, hoff240]; omega)) hstr8
  -- === 78d0: addiw a5,a5,1  ⇒  x15 := count+1 ===
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800078d0 hload9
  have hx15n10 : (afterNextPC (afterPrelude σ9) (0x800078d0#64)).regs.get? Register.x15
      = some (sign_extend (m := 64) vcnt : BitVec 64) := by
    rw [get?_afterNextPC σ9 (0x800078d0#64) _ (by decide) (by decide)]; exact hx15_9
  obtain ⟨σ10, i10, hs10s, hi10, hG10, hmem10, hobs10⟩ :=
    stepObs_alu σ9 i9 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800078d0#64) vmi9 (0x0017879b#32)
      (instruction.ADDIW (0x001#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5))
      Register.x15 (sign_extend (m := 64)
        (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64)
          + sign_extend (m := 64) (0x001#12)) 31 0))
      (0x9b#8) (0x87#8) (0x17#8) (0x00#8)
      hG9 hpc9 hmi9 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_0017879b (afterPrelude σ9)
        (by rw [get?_afterPrelude σ9 _ (by decide)]; exact hG9.misa)
        (by rw [get?_afterPrelude σ9 _ (by decide)]; exact hG9.cur_privilege)
        (by rw [get?_afterPrelude σ9 _ (by decide)]; exact hG9.mseccfg))
      (execute_addiw_char (0x001#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5)
        (sign_extend (m := 64) vcnt : BitVec 64)
        (afterNextPC (afterPrelude σ9) (0x800078d0#64))
        (sigma3_alu σ9 (0x800078d0#64) Register.x15 (sign_extend (m := 64)
          (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64)
            + sign_extend (m := 64) (0x001#12)) 31 0)))
        (rX_bits_x15 _ (sign_extend (m := 64) vcnt : BitVec 64) hx15n10)
        (wX_bits_x15 _ (sign_extend (m := 64)
          (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64)
            + sign_extend (m := 64) (0x001#12)) 31 0))))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi9
  have hstep10 : Step ⟨σ9, i9, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ10, i10, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs10s
  have hpc10 : σ10.regs.get? Register.PC = some (0x800078d4#64) := by
    have := obs_alu_pc hobs10
    rwa [show BitVec.addInt (0x800078d0#64 : BitVec 64) 4 = (0x800078d4#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi10, hmi10⟩ := obs_alu_minstret hobs10
  have hx15_10 : σ10.regs.get? Register.x15 = some (sign_extend (m := 64)
      (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64)
        + sign_extend (m := 64) (0x001#12)) 31 0)) :=
    obs_alu_rd hobs10 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx2_10 : σ10.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs10 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_9
  have hx5_10 : σ10.regs.get? Register.x5 = some vt0 :=
    obs_alu_other hobs10 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_9
  have hx6_10 : σ10.regs.get? Register.x6 = some vt1 :=
    obs_alu_other hobs10 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_9
  have hx8_10 : σ10.regs.get? Register.x8 = some v8 :=
    obs_alu_other hobs10 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_9
  have hx12_10 : σ10.regs.get? Register.x12 = some (vcur + vnd6) :=
    obs_alu_other hobs10 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_9
  have hx16_10 : σ10.regs.get? Register.x16 = some vlen :=
    obs_alu_other hobs10 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_9
  have hx20_10 : σ10.regs.get? Register.x20 = some (sign_extend (m := 64)
      (Sail.BitVec.extractLsb vs4 31 0 - Sail.BitVec.extractLsb vnd6 31 0)) :=
    obs_alu_other hobs10 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_9
  have hx22_10 : σ10.regs.get? Register.x22 = some vnd6 :=
    obs_alu_other hobs10 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_9
  have hx23_10 : σ10.regs.get? Register.x23 = some viov2 :=
    obs_alu_other hobs10 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_9
  have hx26_10 : σ10.regs.get? Register.x26 = some vbase :=
    obs_alu_other hobs10 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_9
  have hx28_10 : σ10.regs.get? Register.x28 = some vt3 :=
    obs_alu_other hobs10 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_9
  have hload10 : SvfprintfSliceLoaded σ10.mem := hmem10 ▸ hload9
  have hfp10 : FlushPinsLoaded σ10.mem := hmem10 ▸ hfp9
  have htot10 : SlotHolds vsp 0x010 vtot σ10.mem := hmem10 ▸ htot9
  have hstr10 : SlotHolds vsp 0x008 vstr σ10.mem := hmem10 ▸ hstr9
  -- === 78d4: sd s10,0(s7)  ⇒  mem[viov2] := digit buffer base ===
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800078d4 hload10
  have hx23n11 : (afterNextPC (afterPrelude σ10) (0x800078d4#64)).regs.get? Register.x23 = some viov2 := by
    rw [get?_afterNextPC σ10 (0x800078d4#64) _ (by decide) (by decide)]; exact hx23_10
  have hx26n11 : (afterNextPC (afterPrelude σ10) (0x800078d4#64)).regs.get? Register.x26 = some vbase := by
    rw [get?_afterNextPC σ10 (0x800078d4#64) _ (by decide) (by decide)]; exact hx26_10
  obtain ⟨σ11, i11, hs11s, hi11, hG11, hmem11, hobs11⟩ :=
    stepObs_store σ10 i10 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800078d4#64) vmi10 (0x01abb023#32)
      (instruction.STORE (0x000#12, regidx.Regidx 0x1a#5, regidx.Regidx 0x17#5, 8))
      (writeMap8 (afterNextPC (afterPrelude σ10) (0x800078d4#64)).mem
        (viov2 + sign_extend (m := 64) (0x000#12)).toNat (sdData_val vbase))
      (0x23#8) (0xb0#8) (0xab#8) (0x01#8)
      hG10 hpc10 hmi10 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_01abb023 (afterPrelude σ10)
        (by rw [get?_afterPrelude σ10 _ (by decide)]; exact hG10.misa)
        (by rw [get?_afterPrelude σ10 _ (by decide)]; exact hG10.cur_privilege)
        (by rw [get?_afterPrelude σ10 _ (by decide)]; exact hG10.mseccfg))
      (exec_sd_val σ10 (0x800078d4#64) (0x000#12) (regidx.Regidx 0x1a#5) (regidx.Regidx 0x17#5)
        viov2 vbase hG10 (rX_bits_x23 _ viov2 hx23n11) (rX_bits_x26 _ vbase hx26n11)
        (by rw [hoffiov0]; omega) (by rw [hoffiov0]; omega) (by rw [hoffiov0]; omega)
        (by rw [hoffiov0]; omega))
      hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi10
  have hstep11 : Step ⟨σ10, i10, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ11, i11, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs11s
  have hpc11 : σ11.regs.get? Register.PC = some (0x800078d8#64) := by
    have := obs_store_pc_sn4 hobs11
    rwa [show BitVec.addInt (0x800078d4#64 : BitVec 64) 4 = (0x800078d8#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi11, hmi11⟩ := obs_store_minstret_sn4 hobs11
  have hx2_11 : σ11.regs.get? Register.x2 = some vsp :=
    obs_store_other_sn4 Register.x2 hobs11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_10
  have hx5_11 : σ11.regs.get? Register.x5 = some vt0 :=
    obs_store_other_sn4 Register.x5 hobs11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_10
  have hx6_11 : σ11.regs.get? Register.x6 = some vt1 :=
    obs_store_other_sn4 Register.x6 hobs11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_10
  have hx8_11 : σ11.regs.get? Register.x8 = some v8 :=
    obs_store_other_sn4 Register.x8 hobs11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_10
  have hx12_11 : σ11.regs.get? Register.x12 = some (vcur + vnd6) :=
    obs_store_other_sn4 Register.x12 hobs11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_10
  have hx15_11 : σ11.regs.get? Register.x15 = some (sign_extend (m := 64)
      (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64)
        + sign_extend (m := 64) (0x001#12)) 31 0)) :=
    obs_store_other_sn4 Register.x15 hobs11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_10
  have hx16_11 : σ11.regs.get? Register.x16 = some vlen :=
    obs_store_other_sn4 Register.x16 hobs11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_10
  have hx20_11 : σ11.regs.get? Register.x20 = some (sign_extend (m := 64)
      (Sail.BitVec.extractLsb vs4 31 0 - Sail.BitVec.extractLsb vnd6 31 0)) :=
    obs_store_other_sn4 Register.x20 hobs11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_10
  have hx22_11 : σ11.regs.get? Register.x22 = some vnd6 :=
    obs_store_other_sn4 Register.x22 hobs11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_10
  have hx23_11 : σ11.regs.get? Register.x23 = some viov2 :=
    obs_store_other_sn4 Register.x23 hobs11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_10
  have hx26_11 : σ11.regs.get? Register.x26 = some vbase :=
    obs_store_other_sn4 Register.x26 hobs11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_10
  have hx28_11 : σ11.regs.get? Register.x28 = some vt3 :=
    obs_store_other_sn4 Register.x28 hobs11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_10
  have hNP11 : (afterNextPC (afterPrelude σ10) (0x800078d4#64)).mem = σ10.mem := rfl
  have hmem11' : σ11.mem = writeMap8 σ10.mem
      (viov2 + sign_extend (m := 64) (0x000#12)).toNat (sdData_val vbase) := by
    rw [hmem11, hNP11]
  have hload11 : SvfprintfSliceLoaded σ11.mem := by
    rw [hmem11']; exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoffiov0]; omega) hload10
  have hfp11 : FlushPinsLoaded σ11.mem := by
    rw [hmem11']; exact flushPins_writeMap8_fl _ _ _ (by rw [hoffiov0]; omega) hfp10
  have htot11 : SlotHolds vsp 0x010 vtot σ11.mem := by
    rw [hmem11']; exact slotHolds_writeMap8 vsp 0x010 vtot _
      ((viov2 + sign_extend (m := 64) (0x000#12)).toNat) _
      (hiovdisj.elim (fun h => Or.inr (by rw [hoff16, hoffiov0]; omega))
        (fun h => Or.inl (by rw [hoff16, hoffiov0]; omega))) htot10
  have hstr11 : SlotHolds vsp 0x008 vstr σ11.mem := by
    rw [hmem11']; exact slotHolds_writeMap8 vsp 0x008 vstr _
      ((viov2 + sign_extend (m := 64) (0x000#12)).toNat) _
      (hiovdisj.elim (fun h => Or.inr (by rw [hoff8, hoffiov0]; omega))
        (fun h => Or.inl (by rw [hoff8, hoffiov0]; omega))) hstr10
  -- === 78d8: sd s6,8(s7)  ⇒  mem[viov2+8] := digit count ===
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800078d8 hload11
  have hx23n12 : (afterNextPC (afterPrelude σ11) (0x800078d8#64)).regs.get? Register.x23 = some viov2 := by
    rw [get?_afterNextPC σ11 (0x800078d8#64) _ (by decide) (by decide)]; exact hx23_11
  have hx22n12 : (afterNextPC (afterPrelude σ11) (0x800078d8#64)).regs.get? Register.x22 = some vnd6 := by
    rw [get?_afterNextPC σ11 (0x800078d8#64) _ (by decide) (by decide)]; exact hx22_11
  obtain ⟨σ12, i12, hs12s, hi12, hG12, hmem12, hobs12⟩ :=
    stepObs_store σ11 i11 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800078d8#64) vmi11 (0x016bb423#32)
      (instruction.STORE (0x008#12, regidx.Regidx 0x16#5, regidx.Regidx 0x17#5, 8))
      (writeMap8 (afterNextPC (afterPrelude σ11) (0x800078d8#64)).mem
        (viov2 + sign_extend (m := 64) (0x008#12)).toNat (sdData_val vnd6))
      (0x23#8) (0xb4#8) (0x6b#8) (0x01#8)
      hG11 hpc11 hmi11 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_016bb423 (afterPrelude σ11)
        (by rw [get?_afterPrelude σ11 _ (by decide)]; exact hG11.misa)
        (by rw [get?_afterPrelude σ11 _ (by decide)]; exact hG11.cur_privilege)
        (by rw [get?_afterPrelude σ11 _ (by decide)]; exact hG11.mseccfg))
      (exec_sd_val σ11 (0x800078d8#64) (0x008#12) (regidx.Regidx 0x16#5) (regidx.Regidx 0x17#5)
        viov2 vnd6 hG11 (rX_bits_x23 _ viov2 hx23n12) (rX_bits_x22 _ vnd6 hx22n12)
        (by rw [hoffiov8]; omega) (by rw [hoffiov8]; omega) (by rw [hoffiov8]; omega)
        (by rw [hoffiov8]; omega))
      hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi11
  have hstep12 : Step ⟨σ11, i11, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ12, i12, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs12s
  have hpc12 : σ12.regs.get? Register.PC = some (0x800078dc#64) := by
    have := obs_store_pc_sn4 hobs12
    rwa [show BitVec.addInt (0x800078d8#64 : BitVec 64) 4 = (0x800078dc#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi12, hmi12⟩ := obs_store_minstret_sn4 hobs12
  have hx2_12 : σ12.regs.get? Register.x2 = some vsp :=
    obs_store_other_sn4 Register.x2 hobs12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_11
  have hx5_12 : σ12.regs.get? Register.x5 = some vt0 :=
    obs_store_other_sn4 Register.x5 hobs12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_11
  have hx6_12 : σ12.regs.get? Register.x6 = some vt1 :=
    obs_store_other_sn4 Register.x6 hobs12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_11
  have hx8_12 : σ12.regs.get? Register.x8 = some v8 :=
    obs_store_other_sn4 Register.x8 hobs12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_11
  have hx12_12 : σ12.regs.get? Register.x12 = some (vcur + vnd6) :=
    obs_store_other_sn4 Register.x12 hobs12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_11
  have hx15_12 : σ12.regs.get? Register.x15 = some (sign_extend (m := 64)
      (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64)
        + sign_extend (m := 64) (0x001#12)) 31 0)) :=
    obs_store_other_sn4 Register.x15 hobs12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_11
  have hx16_12 : σ12.regs.get? Register.x16 = some vlen :=
    obs_store_other_sn4 Register.x16 hobs12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_11
  have hx20_12 : σ12.regs.get? Register.x20 = some (sign_extend (m := 64)
      (Sail.BitVec.extractLsb vs4 31 0 - Sail.BitVec.extractLsb vnd6 31 0)) :=
    obs_store_other_sn4 Register.x20 hobs12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_11
  have hx22_12 : σ12.regs.get? Register.x22 = some vnd6 :=
    obs_store_other_sn4 Register.x22 hobs12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_11
  have hx23_12 : σ12.regs.get? Register.x23 = some viov2 :=
    obs_store_other_sn4 Register.x23 hobs12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_11
  have hx26_12 : σ12.regs.get? Register.x26 = some vbase :=
    obs_store_other_sn4 Register.x26 hobs12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_11
  have hx28_12 : σ12.regs.get? Register.x28 = some vt3 :=
    obs_store_other_sn4 Register.x28 hobs12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_11
  have hNP12 : (afterNextPC (afterPrelude σ11) (0x800078d8#64)).mem = σ11.mem := rfl
  have hmem12' : σ12.mem = writeMap8 σ11.mem
      (viov2 + sign_extend (m := 64) (0x008#12)).toNat (sdData_val vnd6) := by
    rw [hmem12, hNP12]
  have hload12 : SvfprintfSliceLoaded σ12.mem := by
    rw [hmem12']; exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoffiov8]; omega) hload11
  have hfp12 : FlushPinsLoaded σ12.mem := by
    rw [hmem12']; exact flushPins_writeMap8_fl _ _ _ (by rw [hoffiov8]; omega) hfp11
  have htot12 : SlotHolds vsp 0x010 vtot σ12.mem := by
    rw [hmem12']; exact slotHolds_writeMap8 vsp 0x010 vtot _
      ((viov2 + sign_extend (m := 64) (0x008#12)).toNat) _
      (hiovdisj.elim (fun h => Or.inr (by rw [hoff16, hoffiov8]; omega))
        (fun h => Or.inl (by rw [hoff16, hoffiov8]; omega))) htot11
  have hstr12 : SlotHolds vsp 0x008 vstr σ12.mem := by
    rw [hmem12']; exact slotHolds_writeMap8 vsp 0x008 vstr _
      ((viov2 + sign_extend (m := 64) (0x008#12)).toNat) _
      (hiovdisj.elim (fun h => Or.inr (by rw [hoff8, hoffiov8]; omega))
        (fun h => Or.inl (by rw [hoff8, hoffiov8]; omega))) hstr11
  -- === 78dc: li a4,7  ⇒  x14 := 7 ===
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800078dc hload12
  obtain ⟨σ13, i13, hs13s, hi13, hG13, hmem13, hobs13⟩ :=
    stepObs_alu σ12 i12 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800078dc#64) vmi12 (0x00700713#32)
      (instruction.ITYPE (0x007#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0e#5, iop.ADDI))
      Register.x14 ((0#64) + sign_extend (m := 64) (0x007#12))
      (0x13#8) (0x07#8) (0x70#8) (0x00#8)
      hG12 hpc12 hmi12 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_00700713 (afterPrelude σ12)
        (by rw [get?_afterPrelude σ12 _ (by decide)]; exact hG12.misa)
        (by rw [get?_afterPrelude σ12 _ (by decide)]; exact hG12.cur_privilege)
        (by rw [get?_afterPrelude σ12 _ (by decide)]; exact hG12.mseccfg))
      (execute_itype_addi_char (0x007#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0e#5) (0#64)
        (afterNextPC (afterPrelude σ12) (0x800078dc#64))
        (sigma3_alu σ12 (0x800078dc#64) Register.x14 ((0#64) + sign_extend (m := 64) (0x007#12)))
        (rX_bits_zero _) (wX_bits_x14 _ ((0#64) + sign_extend (m := 64) (0x007#12))))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi12
  have hstep13 : Step ⟨σ12, i12, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ13, i13, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs13s
  have hpc13 : σ13.regs.get? Register.PC = some (0x800078e0#64) := by
    have := obs_alu_pc hobs13
    rwa [show BitVec.addInt (0x800078dc#64 : BitVec 64) 4 = (0x800078e0#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi13, hmi13⟩ := obs_alu_minstret hobs13
  have hx14_13 : σ13.regs.get? Register.x14 = some (0x007#64) := by
    have := obs_alu_rd hobs13 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64) + sign_extend (m := 64) (0x007#12) : BitVec 64) = (0x007#64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx2_13 : σ13.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs13 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_12
  have hx5_13 : σ13.regs.get? Register.x5 = some vt0 :=
    obs_alu_other hobs13 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_12
  have hx6_13 : σ13.regs.get? Register.x6 = some vt1 :=
    obs_alu_other hobs13 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_12
  have hx8_13 : σ13.regs.get? Register.x8 = some v8 :=
    obs_alu_other hobs13 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_12
  have hx12_13 : σ13.regs.get? Register.x12 = some (vcur + vnd6) :=
    obs_alu_other hobs13 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_12
  have hx15_13 : σ13.regs.get? Register.x15 = some (sign_extend (m := 64)
      (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64)
        + sign_extend (m := 64) (0x001#12)) 31 0)) :=
    obs_alu_other hobs13 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_12
  have hx16_13 : σ13.regs.get? Register.x16 = some vlen :=
    obs_alu_other hobs13 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_12
  have hx20_13 : σ13.regs.get? Register.x20 = some (sign_extend (m := 64)
      (Sail.BitVec.extractLsb vs4 31 0 - Sail.BitVec.extractLsb vnd6 31 0)) :=
    obs_alu_other hobs13 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_12
  have hx22_13 : σ13.regs.get? Register.x22 = some vnd6 :=
    obs_alu_other hobs13 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_12
  have hx23_13 : σ13.regs.get? Register.x23 = some viov2 :=
    obs_alu_other hobs13 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_12
  have hx26_13 : σ13.regs.get? Register.x26 = some vbase :=
    obs_alu_other hobs13 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_12
  have hx28_13 : σ13.regs.get? Register.x28 = some vt3 :=
    obs_alu_other hobs13 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_12
  have hload13 : SvfprintfSliceLoaded σ13.mem := hmem13 ▸ hload12
  have hfp13 : FlushPinsLoaded σ13.mem := hmem13 ▸ hfp12
  have htot13 : SlotHolds vsp 0x010 vtot σ13.mem := hmem13 ▸ htot12
  have hstr13 : SlotHolds vsp 0x008 vstr σ13.mem := hmem13 ▸ hstr12
  -- === 78e0: sw a5,232(sp)  ⇒  mem[sp+232] := count+1 ===
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800078e0 hload13
  have hx2n14 : (afterNextPC (afterPrelude σ13) (0x800078e0#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ13 (0x800078e0#64) _ (by decide) (by decide)]; exact hx2_13
  have hx15n14 : (afterNextPC (afterPrelude σ13) (0x800078e0#64)).regs.get? Register.x15
      = some (sign_extend (m := 64)
        (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64)
          + sign_extend (m := 64) (0x001#12)) 31 0)) := by
    rw [get?_afterNextPC σ13 (0x800078e0#64) _ (by decide) (by decide)]; exact hx15_13
  obtain ⟨σ14, i14, hs14s, hi14, hG14, hmem14, hobs14⟩ :=
    stepObs_store σ13 i13 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800078e0#64) vmi13 (0x0ef12423#32)
      (instruction.STORE (0x0e8#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x02#5, 4))
      (writeMap4 (afterNextPC (afterPrelude σ13) (0x800078e0#64)).mem
        (vsp + sign_extend (m := 64) (0x0e8#12)).toNat (swData (sign_extend (m := 64)
          (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64)
            + sign_extend (m := 64) (0x001#12)) 31 0))))
      (0x23#8) (0x24#8) (0xf1#8) (0x0e#8)
      hG13 hpc13 hmi13 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_0ef12423 (afterPrelude σ13)
        (by rw [get?_afterPrelude σ13 _ (by decide)]; exact hG13.misa)
        (by rw [get?_afterPrelude σ13 _ (by decide)]; exact hG13.cur_privilege)
        (by rw [get?_afterPrelude σ13 _ (by decide)]; exact hG13.mseccfg))
      (exec_sw σ13 (0x800078e0#64) (0x0e8#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x02#5)
        vsp (sign_extend (m := 64)
          (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64)
            + sign_extend (m := 64) (0x001#12)) 31 0))
        hG13 (rX_bits_x2 _ vsp hx2n14) (rX_bits_x15 _ _ hx15n14)
        (by rw [hoff232]; omega) (by rw [hoff232]; omega) (by rw [hoff232]; omega) (by rw [hoff232]; omega))
      hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi13
  have hstep14 : Step ⟨σ13, i13, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ14, i14, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs14s
  have hpc14 : σ14.regs.get? Register.PC = some (0x800078e4#64) := by
    have := obs_store_pc_sn4 hobs14
    rwa [show BitVec.addInt (0x800078e0#64 : BitVec 64) 4 = (0x800078e4#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi14, hmi14⟩ := obs_store_minstret_sn4 hobs14
  have hx2_14 : σ14.regs.get? Register.x2 = some vsp :=
    obs_store_other_sn4 Register.x2 hobs14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_13
  have hx5_14 : σ14.regs.get? Register.x5 = some vt0 :=
    obs_store_other_sn4 Register.x5 hobs14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_13
  have hx6_14 : σ14.regs.get? Register.x6 = some vt1 :=
    obs_store_other_sn4 Register.x6 hobs14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_13
  have hx8_14 : σ14.regs.get? Register.x8 = some v8 :=
    obs_store_other_sn4 Register.x8 hobs14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_13
  have hx12_14 : σ14.regs.get? Register.x12 = some (vcur + vnd6) :=
    obs_store_other_sn4 Register.x12 hobs14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_13
  have hx14_14 : σ14.regs.get? Register.x14 = some (0x007#64) :=
    obs_store_other_sn4 Register.x14 hobs14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_13
  have hx15_14 : σ14.regs.get? Register.x15 = some (sign_extend (m := 64)
      (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64)
        + sign_extend (m := 64) (0x001#12)) 31 0)) :=
    obs_store_other_sn4 Register.x15 hobs14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_13
  have hx16_14 : σ14.regs.get? Register.x16 = some vlen :=
    obs_store_other_sn4 Register.x16 hobs14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_13
  have hx20_14 : σ14.regs.get? Register.x20 = some (sign_extend (m := 64)
      (Sail.BitVec.extractLsb vs4 31 0 - Sail.BitVec.extractLsb vnd6 31 0)) :=
    obs_store_other_sn4 Register.x20 hobs14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_13
  have hx22_14 : σ14.regs.get? Register.x22 = some vnd6 :=
    obs_store_other_sn4 Register.x22 hobs14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_13
  have hx23_14 : σ14.regs.get? Register.x23 = some viov2 :=
    obs_store_other_sn4 Register.x23 hobs14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_13
  have hx26_14 : σ14.regs.get? Register.x26 = some vbase :=
    obs_store_other_sn4 Register.x26 hobs14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_13
  have hx28_14 : σ14.regs.get? Register.x28 = some vt3 :=
    obs_store_other_sn4 Register.x28 hobs14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_13
  have hNP14 : (afterNextPC (afterPrelude σ13) (0x800078e0#64)).mem = σ13.mem := rfl
  have hmem14' : σ14.mem = writeMap4 σ13.mem
      (vsp + sign_extend (m := 64) (0x0e8#12)).toNat (swData (sign_extend (m := 64)
        (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64)
          + sign_extend (m := 64) (0x001#12)) 31 0))) := by
    rw [hmem14, hNP14]
  have hload14 : SvfprintfSliceLoaded σ14.mem := by
    rw [hmem14']; exact svfprintfSlice_writeMap4_pe _ _ _ (by rw [hoff232]; omega) hload13
  have hfp14 : FlushPinsLoaded σ14.mem := by
    rw [hmem14']; exact flushPins_writeMap4_pe _ _ _ (by rw [hoff232]; omega) hfp13
  have htot14 : SlotHolds vsp 0x010 vtot σ14.mem := by
    rw [hmem14']; exact slotHolds_writeMap4_i2 vsp 0x010 vtot _
      ((vsp + sign_extend (m := 64) (0x0e8#12)).toNat) _
      (by rw [hoff16, hoff232]; omega) htot13
  have hstr14 : SlotHolds vsp 0x008 vstr σ14.mem := by
    rw [hmem14']; exact slotHolds_writeMap4_i2 vsp 0x008 vstr _
      ((vsp + sign_extend (m := 64) (0x0e8#12)).toNat) _
      (by rw [hoff8, hoff232]; omega) hstr13
  -- === 78e4: blt a4,a5,7bf4  (NOT taken: count+1 ≤ 7) ===
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800078e4 hload14
  have hx14n15 : (rX_bits (regidx.Regidx 0x0e#5)).run (afterNextPC (afterPrelude σ14) (0x800078e4#64))
      = .ok (0x007#64) (afterNextPC (afterPrelude σ14) (0x800078e4#64)) := by
    apply rX_bits_x14
    rw [get?_afterNextPC σ14 (0x800078e4#64) _ (by decide) (by decide)]; exact hx14_14
  have hx15n15 : (rX_bits (regidx.Regidx 0x0f#5)).run (afterNextPC (afterPrelude σ14) (0x800078e4#64))
      = .ok (sign_extend (m := 64)
        (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64)
          + sign_extend (m := 64) (0x001#12)) 31 0))
        (afterNextPC (afterPrelude σ14) (0x800078e4#64)) := by
    apply rX_bits_x15
    rw [get?_afterNextPC σ14 (0x800078e4#64) _ (by decide) (by decide)]; exact hx15_14
  obtain ⟨σ15, i15, hs15s, hi15, hG15, hmem15, hobs15⟩ :=
    stepObs_branch_nottaken σ14 i14 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800078e4#64) vmi14
      (0x0310#13) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0f#5) bop.BLT (0x30f74863#32)
      (0x63#8) (0x48#8) (0xf7#8) (0x30#8)
      hG14 hpc14 hmi14 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_30f74863 (afterPrelude σ14)
        (by rw [get?_afterPrelude σ14 _ (by decide)]; exact hG14.misa)
        (by rw [get?_afterPrelude σ14 _ (by decide)]; exact hG14.cur_privilege)
        (by rw [get?_afterPrelude σ14 _ (by decide)]; exact hG14.mseccfg))
      (execute_btype_blt_nottaken (0x0310#13) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0f#5)
        (0x007#64) (sign_extend (m := 64)
          (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64)
            + sign_extend (m := 64) (0x001#12)) 31 0))
        (afterNextPC (afterPrelude σ14) (0x800078e4#64))
        hx14n15 hx15n15 hcnt2)
      hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi14
  have hstep15 : Step ⟨σ14, i14, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ15, i15, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs15s
  have hpc15 : σ15.regs.get? Register.PC = some (0x800078e8#64) := by
    have := obs_branch_nottaken_pc hobs15
    rwa [show BitVec.addInt (0x800078e4#64 : BitVec 64) 4 = (0x800078e8#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi15, hmi15⟩ := obs_branch_nottaken_minstret hobs15
  have hx2_15 : σ15.regs.get? Register.x2 = some vsp :=
    obs_branch_nottaken_other hobs15 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_14
  have hx5_15 : σ15.regs.get? Register.x5 = some vt0 :=
    obs_branch_nottaken_other hobs15 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_14
  have hx6_15 : σ15.regs.get? Register.x6 = some vt1 :=
    obs_branch_nottaken_other hobs15 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_14
  have hx8_15 : σ15.regs.get? Register.x8 = some v8 :=
    obs_branch_nottaken_other hobs15 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_14
  have hx12_15 : σ15.regs.get? Register.x12 = some (vcur + vnd6) :=
    obs_branch_nottaken_other hobs15 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_14
  have hx16_15 : σ15.regs.get? Register.x16 = some vlen :=
    obs_branch_nottaken_other hobs15 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_14
  have hx20_15 : σ15.regs.get? Register.x20 = some (sign_extend (m := 64)
      (Sail.BitVec.extractLsb vs4 31 0 - Sail.BitVec.extractLsb vnd6 31 0)) :=
    obs_branch_nottaken_other hobs15 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_14
  have hx22_15 : σ15.regs.get? Register.x22 = some vnd6 :=
    obs_branch_nottaken_other hobs15 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_14
  have hx23_15 : σ15.regs.get? Register.x23 = some viov2 :=
    obs_branch_nottaken_other hobs15 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_14
  have hx26_15 : σ15.regs.get? Register.x26 = some vbase :=
    obs_branch_nottaken_other hobs15 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_14
  have hx28_15 : σ15.regs.get? Register.x28 = some vt3 :=
    obs_branch_nottaken_other hobs15 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_14
  have hload15 : SvfprintfSliceLoaded σ15.mem := hmem15 ▸ hload14
  have hfp15 : FlushPinsLoaded σ15.mem := hmem15 ▸ hfp14
  have htot15 : SlotHolds vsp 0x010 vtot σ15.mem := hmem15 ▸ htot14
  have hstr15 : SlotHolds vsp 0x008 vstr σ15.mem := hmem15 ▸ hstr14
  -- === 78e8: addi s7,s7,16  ⇒  x23 := viov2 + 16 ===
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800078e8 hload15
  have hx23n16 : (afterNextPC (afterPrelude σ15) (0x800078e8#64)).regs.get? Register.x23 = some viov2 := by
    rw [get?_afterNextPC σ15 (0x800078e8#64) _ (by decide) (by decide)]; exact hx23_15
  obtain ⟨σ16, i16, hs16s, hi16, hG16, hmem16, hobs16⟩ :=
    stepObs_alu σ15 i15 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800078e8#64) vmi15 (0x010b8b93#32)
      (instruction.ITYPE (0x010#12, regidx.Regidx 0x17#5, regidx.Regidx 0x17#5, iop.ADDI))
      Register.x23 (viov2 + sign_extend (m := 64) (0x010#12))
      (0x93#8) (0x8b#8) (0x0b#8) (0x01#8)
      hG15 hpc15 hmi15 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_010b8b93 (afterPrelude σ15)
        (by rw [get?_afterPrelude σ15 _ (by decide)]; exact hG15.misa)
        (by rw [get?_afterPrelude σ15 _ (by decide)]; exact hG15.cur_privilege)
        (by rw [get?_afterPrelude σ15 _ (by decide)]; exact hG15.mseccfg))
      (execute_itype_addi_char (0x010#12) (regidx.Regidx 0x17#5) (regidx.Regidx 0x17#5) viov2
        (afterNextPC (afterPrelude σ15) (0x800078e8#64))
        (sigma3_alu σ15 (0x800078e8#64) Register.x23 (viov2 + sign_extend (m := 64) (0x010#12)))
        (rX_bits_x23 _ viov2 hx23n16) (wX_bits_x23 _ (viov2 + sign_extend (m := 64) (0x010#12))))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi15
  have hstep16 : Step ⟨σ15, i15, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ16, i16, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs16s
  have hpc16 : σ16.regs.get? Register.PC = some (0x800078ec#64) := by
    have := obs_alu_pc hobs16
    rwa [show BitVec.addInt (0x800078e8#64 : BitVec 64) 4 = (0x800078ec#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi16, hmi16⟩ := obs_alu_minstret hobs16
  have hx23_16 : σ16.regs.get? Register.x23 = some (viov2 + sign_extend (m := 64) (0x010#12)) :=
    obs_alu_rd hobs16 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx2_16 : σ16.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs16 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_15
  have hx5_16 : σ16.regs.get? Register.x5 = some vt0 :=
    obs_alu_other hobs16 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_15
  have hx6_16 : σ16.regs.get? Register.x6 = some vt1 :=
    obs_alu_other hobs16 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_15
  have hx8_16 : σ16.regs.get? Register.x8 = some v8 :=
    obs_alu_other hobs16 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_15
  have hx12_16 : σ16.regs.get? Register.x12 = some (vcur + vnd6) :=
    obs_alu_other hobs16 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_15
  have hx16_16 : σ16.regs.get? Register.x16 = some vlen :=
    obs_alu_other hobs16 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_15
  have hx20_16 : σ16.regs.get? Register.x20 = some (sign_extend (m := 64)
      (Sail.BitVec.extractLsb vs4 31 0 - Sail.BitVec.extractLsb vnd6 31 0)) :=
    obs_alu_other hobs16 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_15
  have hx22_16 : σ16.regs.get? Register.x22 = some vnd6 :=
    obs_alu_other hobs16 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_15
  have hx26_16 : σ16.regs.get? Register.x26 = some vbase :=
    obs_alu_other hobs16 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_15
  have hx28_16 : σ16.regs.get? Register.x28 = some vt3 :=
    obs_alu_other hobs16 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_15
  have hload16 : SvfprintfSliceLoaded σ16.mem := hmem16 ▸ hload15
  have hfp16 : FlushPinsLoaded σ16.mem := hmem16 ▸ hfp15
  have htot16 : SlotHolds vsp 0x010 vtot σ16.mem := hmem16 ▸ htot15
  have hstr16 : SlotHolds vsp 0x008 vstr σ16.mem := hmem16 ▸ hstr15
  -- === 78ec: andi t1,t1,4  ⇒  x6 := vt1 &&& 4 ===
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800078ec hload16
  have hx6n17 : (afterNextPC (afterPrelude σ16) (0x800078ec#64)).regs.get? Register.x6 = some vt1 := by
    rw [get?_afterNextPC σ16 (0x800078ec#64) _ (by decide) (by decide)]; exact hx6_16
  obtain ⟨σ17, i17, hs17s, hi17, hG17, hmem17, hobs17⟩ :=
    stepObs_alu σ16 i16 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800078ec#64) vmi16 (0x00437313#32)
      (instruction.ITYPE (0x004#12, regidx.Regidx 0x06#5, regidx.Regidx 0x06#5, iop.ANDI))
      Register.x6 (vt1 &&& sign_extend (m := 64) (0x004#12))
      (0x13#8) (0x73#8) (0x43#8) (0x00#8)
      hG16 hpc16 hmi16 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_00437313 (afterPrelude σ16)
        (by rw [get?_afterPrelude σ16 _ (by decide)]; exact hG16.misa)
        (by rw [get?_afterPrelude σ16 _ (by decide)]; exact hG16.cur_privilege)
        (by rw [get?_afterPrelude σ16 _ (by decide)]; exact hG16.mseccfg))
      (execute_itype_andi_char (0x004#12) (regidx.Regidx 0x06#5) (regidx.Regidx 0x06#5) vt1
        (afterNextPC (afterPrelude σ16) (0x800078ec#64))
        (sigma3_alu σ16 (0x800078ec#64) Register.x6 (vt1 &&& sign_extend (m := 64) (0x004#12)))
        (rX_bits_x6 _ vt1 hx6n17) (wX_bits_x6 _ (vt1 &&& sign_extend (m := 64) (0x004#12))))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi16
  have hstep17 : Step ⟨σ16, i16, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ17, i17, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs17s
  have hpc17 : σ17.regs.get? Register.PC = some (0x800078f0#64) := by
    have := obs_alu_pc hobs17
    rwa [show BitVec.addInt (0x800078ec#64 : BitVec 64) 4 = (0x800078f0#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi17, hmi17⟩ := obs_alu_minstret hobs17
  have hx6_17 : σ17.regs.get? Register.x6 = some (vt1 &&& sign_extend (m := 64) (0x004#12)) :=
    obs_alu_rd hobs17 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx2_17 : σ17.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs17 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_16
  have hx5_17 : σ17.regs.get? Register.x5 = some vt0 :=
    obs_alu_other hobs17 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_16
  have hx8_17 : σ17.regs.get? Register.x8 = some v8 :=
    obs_alu_other hobs17 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_16
  have hx12_17 : σ17.regs.get? Register.x12 = some (vcur + vnd6) :=
    obs_alu_other hobs17 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_16
  have hx16_17 : σ17.regs.get? Register.x16 = some vlen :=
    obs_alu_other hobs17 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_16
  have hx20_17 : σ17.regs.get? Register.x20 = some (sign_extend (m := 64)
      (Sail.BitVec.extractLsb vs4 31 0 - Sail.BitVec.extractLsb vnd6 31 0)) :=
    obs_alu_other hobs17 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_16
  have hx22_17 : σ17.regs.get? Register.x22 = some vnd6 :=
    obs_alu_other hobs17 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_16
  have hx23_17 : σ17.regs.get? Register.x23 = some (viov2 + sign_extend (m := 64) (0x010#12)) :=
    obs_alu_other hobs17 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_16
  have hx26_17 : σ17.regs.get? Register.x26 = some vbase :=
    obs_alu_other hobs17 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_16
  have hx28_17 : σ17.regs.get? Register.x28 = some vt3 :=
    obs_alu_other hobs17 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_16
  have hload17 : SvfprintfSliceLoaded σ17.mem := hmem17 ▸ hload16
  have hfp17 : FlushPinsLoaded σ17.mem := hmem17 ▸ hfp16
  have htot17 : SlotHolds vsp 0x010 vtot σ17.mem := hmem17 ▸ htot16
  have hstr17 : SlotHolds vsp 0x008 vstr σ17.mem := hmem17 ▸ hstr16
  -- === 78f0: beqz t1,78fc  (TAKEN: flags&4 = 0) → 0x800078fc ===
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800078f0 hload17
  have hx6n18 : (rX_bits (regidx.Regidx 0x06#5)).run (afterNextPC (afterPrelude σ17) (0x800078f0#64))
      = .ok (vt1 &&& sign_extend (m := 64) (0x004#12))
        (afterNextPC (afterPrelude σ17) (0x800078f0#64)) := by
    apply rX_bits_x6
    rw [get?_afterNextPC σ17 (0x800078f0#64) _ (by decide) (by decide)]; exact hx6_17
  obtain ⟨σ18, i18, hs18s, hi18, hG18, hmem18, hobs18⟩ :=
    stepObs_branch_taken σ17 i17 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800078f0#64) vmi17
      (0x000c#13) (regidx.Regidx 0x06#5) (regidx.Regidx 0x00#5) bop.BEQ (0x00030663#32)
      (0x63#8) (0x06#8) (0x03#8) (0x00#8)
      hG17 hpc17 hmi17 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_00030663 (afterPrelude σ17)
        (by rw [get?_afterPrelude σ17 _ (by decide)]; exact hG17.misa)
        (by rw [get?_afterPrelude σ17 _ (by decide)]; exact hG17.cur_privilege)
        (by rw [get?_afterPrelude σ17 _ (by decide)]; exact hG17.mseccfg))
      (execute_btype_beq_taken (0x000c#13) (regidx.Regidx 0x06#5) (regidx.Regidx 0x00#5)
        (vt1 &&& sign_extend (m := 64) (0x004#12)) (0#64) (0x800078f0#64) initMisa
        (afterNextPC (afterPrelude σ17) (0x800078f0#64))
        hx6n18 (rX_bits_zero _)
        (by rw [get?_afterNextPC σ17 (0x800078f0#64) _ (by decide) (by decide)]; exact hpc17)
        (by rw [get?_afterNextPC σ17 (0x800078f0#64) _ (by decide) (by decide)]; exact hG17.misa)
        (by decide) hb4)
      hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi17
  have hstep18 : Step ⟨σ17, i17, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ18, i18, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs18s
  have hpc18 : σ18.regs.get? Register.PC = some (0x800078fc#64) := by
    have := obs_branch_taken_pc hobs18
    rwa [show ((0x800078f0#64 : BitVec 64) + sign_extend (m := 64) (0x000c#13))
      = (0x800078fc#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi18, hmi18⟩ := obs_branch_taken_minstret hobs18
  have hx2_18 : σ18.regs.get? Register.x2 = some vsp :=
    obs_branch_taken_other hobs18 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_17
  have hx5_18 : σ18.regs.get? Register.x5 = some vt0 :=
    obs_branch_taken_other hobs18 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_17
  have hx6_18 : σ18.regs.get? Register.x6 = some (vt1 &&& sign_extend (m := 64) (0x004#12)) :=
    obs_branch_taken_other hobs18 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_17
  have hx8_18 : σ18.regs.get? Register.x8 = some v8 :=
    obs_branch_taken_other hobs18 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_17
  have hx12_18 : σ18.regs.get? Register.x12 = some (vcur + vnd6) :=
    obs_branch_taken_other hobs18 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_17
  have hx16_18 : σ18.regs.get? Register.x16 = some vlen :=
    obs_branch_taken_other hobs18 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_17
  have hx20_18 : σ18.regs.get? Register.x20 = some (sign_extend (m := 64)
      (Sail.BitVec.extractLsb vs4 31 0 - Sail.BitVec.extractLsb vnd6 31 0)) :=
    obs_branch_taken_other hobs18 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_17
  have hx22_18 : σ18.regs.get? Register.x22 = some vnd6 :=
    obs_branch_taken_other hobs18 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_17
  have hx23_18 : σ18.regs.get? Register.x23 = some (viov2 + sign_extend (m := 64) (0x010#12)) :=
    obs_branch_taken_other hobs18 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_17
  have hx26_18 : σ18.regs.get? Register.x26 = some vbase :=
    obs_branch_taken_other hobs18 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_17
  have hx28_18 : σ18.regs.get? Register.x28 = some vt3 :=
    obs_branch_taken_other hobs18 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_17
  have hload18 : SvfprintfSliceLoaded σ18.mem := hmem18 ▸ hload17
  have hfp18 : FlushPinsLoaded σ18.mem := hmem18 ▸ hfp17
  have htot18 : SlotHolds vsp 0x010 vtot σ18.mem := hmem18 ▸ htot17
  have hstr18 : SlotHolds vsp 0x008 vstr σ18.mem := hmem18 ▸ hstr17
  -- === 78fc: mv a5,t3  ⇒  x15 := vt3 ===
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800078fc hload18
  have hx28n19 : (afterNextPC (afterPrelude σ18) (0x800078fc#64)).regs.get? Register.x28 = some vt3 := by
    rw [get?_afterNextPC σ18 (0x800078fc#64) _ (by decide) (by decide)]; exact hx28_18
  obtain ⟨σ19, i19, hs19s, hi19, hG19, hmem19, hobs19⟩ :=
    stepObs_alu σ18 i18 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800078fc#64) vmi18 (0x000e0793#32)
      (instruction.ITYPE (0x000#12, regidx.Regidx 0x1c#5, regidx.Regidx 0x0f#5, iop.ADDI))
      Register.x15 (vt3 + sign_extend (m := 64) (0x000#12))
      (0x93#8) (0x07#8) (0x0e#8) (0x00#8)
      hG18 hpc18 hmi18 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_000e0793 (afterPrelude σ18)
        (by rw [get?_afterPrelude σ18 _ (by decide)]; exact hG18.misa)
        (by rw [get?_afterPrelude σ18 _ (by decide)]; exact hG18.cur_privilege)
        (by rw [get?_afterPrelude σ18 _ (by decide)]; exact hG18.mseccfg))
      (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x1c#5) (regidx.Regidx 0x0f#5) vt3
        (afterNextPC (afterPrelude σ18) (0x800078fc#64))
        (sigma3_alu σ18 (0x800078fc#64) Register.x15 (vt3 + sign_extend (m := 64) (0x000#12)))
        (rX_bits_x28 _ vt3 hx28n19) (wX_bits_x15 _ (vt3 + sign_extend (m := 64) (0x000#12))))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi18
  have hstep19 : Step ⟨σ18, i18, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ19, i19, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs19s
  have hpc19 : σ19.regs.get? Register.PC = some (0x80007900#64) := by
    have := obs_alu_pc hobs19
    rwa [show BitVec.addInt (0x800078fc#64 : BitVec 64) 4 = (0x80007900#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi19, hmi19⟩ := obs_alu_minstret hobs19
  have hx15_19 : σ19.regs.get? Register.x15 = some vt3 := by
    have := obs_alu_rd hobs19 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (vt3 + sign_extend (m := 64) (0x000#12) : BitVec 64) = vt3 from by
      rw [show sign_extend (m := 64) (0x000#12) = (0#64) from by
        apply BitVec.eq_of_toNat_eq; decide, BitVec.add_zero]] at this
  have hx2_19 : σ19.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs19 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_18
  have hx5_19 : σ19.regs.get? Register.x5 = some vt0 :=
    obs_alu_other hobs19 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_18
  have hx6_19 : σ19.regs.get? Register.x6 = some (vt1 &&& sign_extend (m := 64) (0x004#12)) :=
    obs_alu_other hobs19 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_18
  have hx8_19 : σ19.regs.get? Register.x8 = some v8 :=
    obs_alu_other hobs19 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_18
  have hx12_19 : σ19.regs.get? Register.x12 = some (vcur + vnd6) :=
    obs_alu_other hobs19 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_18
  have hx16_19 : σ19.regs.get? Register.x16 = some vlen :=
    obs_alu_other hobs19 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_18
  have hx20_19 : σ19.regs.get? Register.x20 = some (sign_extend (m := 64)
      (Sail.BitVec.extractLsb vs4 31 0 - Sail.BitVec.extractLsb vnd6 31 0)) :=
    obs_alu_other hobs19 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_18
  have hx22_19 : σ19.regs.get? Register.x22 = some vnd6 :=
    obs_alu_other hobs19 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_18
  have hx23_19 : σ19.regs.get? Register.x23 = some (viov2 + sign_extend (m := 64) (0x010#12)) :=
    obs_alu_other hobs19 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_18
  have hx26_19 : σ19.regs.get? Register.x26 = some vbase :=
    obs_alu_other hobs19 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_18
  have hx28_19 : σ19.regs.get? Register.x28 = some vt3 :=
    obs_alu_other hobs19 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_18
  have hload19 : SvfprintfSliceLoaded σ19.mem := hmem19 ▸ hload18
  have hfp19 : FlushPinsLoaded σ19.mem := hmem19 ▸ hfp18
  have htot19 : SlotHolds vsp 0x010 vtot σ19.mem := hmem19 ▸ htot18
  have hstr19 : SlotHolds vsp 0x008 vstr σ19.mem := hmem19 ▸ hstr18
  -- === the head Steps chain and the shared register facts ===
  have hheadsteps : Steps c ⟨σ19, i19, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ :=
    ((Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans ((Steps.single hstep4).trans ((Steps.single hstep5).trans ((Steps.single hstep6).trans ((Steps.single hstep7).trans ((Steps.single hstep8).trans ((Steps.single hstep9).trans ((Steps.single hstep10).trans ((Steps.single hstep11).trans ((Steps.single hstep12).trans ((Steps.single hstep13).trans ((Steps.single hstep14).trans ((Steps.single hstep15).trans ((Steps.single hstep16).trans ((Steps.single hstep17).trans ((Steps.single hstep18).trans (Steps.single hstep19)))))))))))))))))))
  have hmem19base : σ19.mem = writeMap4
      (writeMap8
        (writeMap8
          (writeMap8 c.σ.mem
            (vsp + sign_extend (m := 64) (0x0f0#12)).toNat (sdData_val (vcur + vnd6)))
          viov2.toNat (sdData_val vbase))
        (viov2 + sign_extend (m := 64) (0x008#12)).toNat (sdData_val vnd6))
      (vsp + sign_extend (m := 64) (0x0e8#12)).toNat (swData (sign_extend (m := 64)
        (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64)
          + sign_extend (m := 64) (0x001#12)) 31 0))) := by
    rw [hmem19, hmem18, hmem17, hmem16, hmem15, hmem14', hmem13, hmem12', hmem11', hoffiov0,
      hmem10, hmem9', hmem8, hmem7, hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]
  -- === 7900: bge t3,a6,7908  (case split; both outcomes covered) ===
  have hkeepHead : KeepRegs midRegs5 c.σ σ19 := by
    have k1 := keep_alu hobs1 (by decide) (keep_rfl midRegs5 c.σ)
    have k2 := keep_bnottaken hobs2 (by decide) k1
    have k3 := keep_alu hobs3 (by decide) k2
    have k4 := keep_bnottaken hobs4 (by decide) k3
    have k5 := keep_alu hobs5 (by decide) k4
    have k6 := keep_bnottaken hobs6 (by decide) k5
    have k7 := keep_alu hobs7 (by decide) k6
    have k8 := keep_alu hobs8 (by decide) k7
    have k9 := keep_store hobs9 (by decide) k8
    have k10 := keep_alu hobs10 (by decide) k9
    have k11 := keep_store hobs11 (by decide) k10
    have k12 := keep_store hobs12 (by decide) k11
    have k13 := keep_alu hobs13 (by decide) k12
    have k14 := keep_store hobs14 (by decide) k13
    have k15 := keep_bnottaken hobs15 (by decide) k14
    have k16 := keep_alu hobs16 (by decide) k15
    have k17 := keep_alu hobs17 (by decide) k16
    have k18 := keep_btaken hobs18 (by decide) k17
    exact keep_alu hobs19 (by decide) k18
  cases hbge : zopz0zKzJ_s vt3 vlen with
  | true =>
    obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80007900 hload19
    have hx28n20 : (rX_bits (regidx.Regidx 0x1c#5)).run (afterNextPC (afterPrelude σ19) (0x80007900#64))
        = .ok vt3 (afterNextPC (afterPrelude σ19) (0x80007900#64)) := by
      apply rX_bits_x28
      rw [get?_afterNextPC σ19 (0x80007900#64) _ (by decide) (by decide)]; exact hx28_19
    have hx16n20 : (rX_bits (regidx.Regidx 0x10#5)).run (afterNextPC (afterPrelude σ19) (0x80007900#64))
        = .ok vlen (afterNextPC (afterPrelude σ19) (0x80007900#64)) := by
      apply rX_bits_x16
      rw [get?_afterNextPC σ19 (0x80007900#64) _ (by decide) (by decide)]; exact hx16_19
    obtain ⟨σ20, i20, hs20s, hi20, hG20, hmem20, hobs20⟩ :=
      stepObs_branch_taken σ19 i19 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80007900#64) vmi19
        (0x0008#13) (regidx.Regidx 0x1c#5) (regidx.Regidx 0x10#5) bop.BGE (0x010e5463#32)
        (0x63#8) (0x54#8) (0x0e#8) (0x01#8)
        hG19 hpc19 hmi19 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
        (Vsa.Sim.DecodeTable.decode_010e5463 (afterPrelude σ19)
          (by rw [get?_afterPrelude σ19 _ (by decide)]; exact hG19.misa)
          (by rw [get?_afterPrelude σ19 _ (by decide)]; exact hG19.cur_privilege)
          (by rw [get?_afterPrelude σ19 _ (by decide)]; exact hG19.mseccfg))
        (execute_btype_bge_taken (0x0008#13) (regidx.Regidx 0x1c#5) (regidx.Regidx 0x10#5)
          vt3 vlen (0x80007900#64) initMisa (afterNextPC (afterPrelude σ19) (0x80007900#64))
          hx28n20 hx16n20
          (by rw [get?_afterNextPC σ19 (0x80007900#64) _ (by decide) (by decide)]; exact hpc19)
          (by rw [get?_afterNextPC σ19 (0x80007900#64) _ (by decide) (by decide)]; exact hG19.misa)
          (by decide) hbge)
        hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi19
    have hstep20 : Step ⟨σ19, i19, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
        ⟨σ20, i20, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs20s
    have hpc20 : σ20.regs.get? Register.PC = some (0x80007908#64) := by
      have := obs_branch_taken_pc hobs20
      rwa [show ((0x80007900#64 : BitVec 64) + sign_extend (m := 64) (0x0008#13))
        = (0x80007908#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
    have hx2_20t : σ20.regs.get? Register.x2 = some vsp :=
      obs_branch_taken_other hobs20 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_19
    have hx5_20t : σ20.regs.get? Register.x5 = some vt0 :=
      obs_branch_taken_other hobs20 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_19
    have hx6_20t : σ20.regs.get? Register.x6 = some (vt1 &&& sign_extend (m := 64) (0x004#12)) :=
      obs_branch_taken_other hobs20 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_19
    have hx8_20t : σ20.regs.get? Register.x8 = some v8 :=
      obs_branch_taken_other hobs20 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_19
    have hx12_20t : σ20.regs.get? Register.x12 = some (vcur + vnd6) :=
      obs_branch_taken_other hobs20 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_19
    have hx16_20t : σ20.regs.get? Register.x16 = some vlen :=
      obs_branch_taken_other hobs20 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_19
    have hx20_20t : σ20.regs.get? Register.x20 = some (sign_extend (m := 64)
        (Sail.BitVec.extractLsb vs4 31 0 - Sail.BitVec.extractLsb vnd6 31 0)) :=
      obs_branch_taken_other hobs20 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_19
    have hx22_20t : σ20.regs.get? Register.x22 = some vnd6 :=
      obs_branch_taken_other hobs20 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_19
    have hx23_20t : σ20.regs.get? Register.x23 = some (viov2 + sign_extend (m := 64) (0x010#12)) :=
      obs_branch_taken_other hobs20 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_19
    have hx26_20t : σ20.regs.get? Register.x26 = some vbase :=
      obs_branch_taken_other hobs20 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_19
    have hx28_20t : σ20.regs.get? Register.x28 = some vt3 :=
      obs_branch_taken_other hobs20 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_19
    have hload20t : SvfprintfSliceLoaded σ20.mem := hmem20 ▸ hload19
    have hfp20t : FlushPinsLoaded σ20.mem := hmem20 ▸ hfp19
    have htot20t : SlotHolds vsp 0x010 vtot σ20.mem := hmem20 ▸ htot19
    have hstr20t : SlotHolds vsp 0x008 vstr σ20.mem := hmem20 ▸ hstr19
    have hx15_20t : σ20.regs.get? Register.x15 = some vt3 :=
      obs_branch_taken_other hobs20 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_19
    obtain ⟨c', hstepsT, hG', hpc', hx1', hx10', hx11', hx12', hx2', hx5', hx6', hx8', hx16',
        hx20', hx22', hx23', hx26', hx28', hmem', htick', hmi', hkeepT⟩ :=
      iov2Tail_spec vsp vt0 (vt1 &&& sign_extend (m := 64) (0x004#12)) v8 (vcur + vnd6) vlen
        (sign_extend (m := 64)
          (Sail.BitVec.extractLsb vs4 31 0 - Sail.BitVec.extractLsb vnd6 31 0))
        vnd6 (viov2 + sign_extend (m := 64) (0x010#12)) vbase vt3 vt3 vstr vtot
        ⟨σ20, i20, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
        hG20 hpc20 hx2_20t hx5_20t hx6_20t hx8_20t hx12_20t hx15_20t hx16_20t hx20_20t hx22_20t
        hx23_20t hx26_20t hx28_20t hload20t hfp20t htot20t hstr20t hcurne hspwin hsphi hspalign hi20
    refine ⟨c', hheadsteps.trans ((Steps.single hstep20).trans hstepsT), hG', hpc', hx1', hx10',
      hx11', hx12', hx2', hx5', hx6', hx8', hx16', hx20', hx22', hx23', hx26', hx28', ?_,
      htick', hmi', keep_trans (keep_btaken hobs20 (by decide) hkeepHead) hkeepT⟩
    rw [hmem', hmem20, hmem19base, if_pos (by decide)]
  | false =>
    have hne : ¬(zopz0zKzJ_s vt3 vlen = true) := by
      intro h; rw [h] at hbge; exact Bool.noConfusion hbge
    obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80007900 hload19
    have hx28n20 : (rX_bits (regidx.Regidx 0x1c#5)).run (afterNextPC (afterPrelude σ19) (0x80007900#64))
        = .ok vt3 (afterNextPC (afterPrelude σ19) (0x80007900#64)) := by
      apply rX_bits_x28
      rw [get?_afterNextPC σ19 (0x80007900#64) _ (by decide) (by decide)]; exact hx28_19
    have hx16n20 : (rX_bits (regidx.Regidx 0x10#5)).run (afterNextPC (afterPrelude σ19) (0x80007900#64))
        = .ok vlen (afterNextPC (afterPrelude σ19) (0x80007900#64)) := by
      apply rX_bits_x16
      rw [get?_afterNextPC σ19 (0x80007900#64) _ (by decide) (by decide)]; exact hx16_19
    obtain ⟨σ20, i20, hs20s, hi20, hG20, hmem20, hobs20⟩ :=
      stepObs_branch_nottaken σ19 i19 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80007900#64) vmi19
        (0x0008#13) (regidx.Regidx 0x1c#5) (regidx.Regidx 0x10#5) bop.BGE (0x010e5463#32)
        (0x63#8) (0x54#8) (0x0e#8) (0x01#8)
        hG19 hpc19 hmi19 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
        (Vsa.Sim.DecodeTable.decode_010e5463 (afterPrelude σ19)
          (by rw [get?_afterPrelude σ19 _ (by decide)]; exact hG19.misa)
          (by rw [get?_afterPrelude σ19 _ (by decide)]; exact hG19.cur_privilege)
          (by rw [get?_afterPrelude σ19 _ (by decide)]; exact hG19.mseccfg))
        (execute_btype_bge_nottaken (0x0008#13) (regidx.Regidx 0x1c#5) (regidx.Regidx 0x10#5)
          vt3 vlen (afterNextPC (afterPrelude σ19) (0x80007900#64))
          hx28n20 hx16n20 hbge)
        hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi19
    have hstep20 : Step ⟨σ19, i19, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
        ⟨σ20, i20, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs20s
    have hpc20 : σ20.regs.get? Register.PC = some (0x80007904#64) := by
      have := obs_branch_nottaken_pc hobs20
      rwa [show BitVec.addInt (0x80007900#64 : BitVec 64) 4 = (0x80007904#64 : BitVec 64) from by
        apply BitVec.eq_of_toNat_eq; decide] at this
    obtain ⟨vmi20, hmi20⟩ := obs_branch_nottaken_minstret hobs20
    have hx2_20 : σ20.regs.get? Register.x2 = some vsp :=
      obs_branch_nottaken_other hobs20 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_19
    have hx5_20 : σ20.regs.get? Register.x5 = some vt0 :=
      obs_branch_nottaken_other hobs20 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_19
    have hx6_20 : σ20.regs.get? Register.x6 = some (vt1 &&& sign_extend (m := 64) (0x004#12)) :=
      obs_branch_nottaken_other hobs20 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_19
    have hx8_20 : σ20.regs.get? Register.x8 = some v8 :=
      obs_branch_nottaken_other hobs20 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_19
    have hx12_20 : σ20.regs.get? Register.x12 = some (vcur + vnd6) :=
      obs_branch_nottaken_other hobs20 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_19
    have hx16_20 : σ20.regs.get? Register.x16 = some vlen :=
      obs_branch_nottaken_other hobs20 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_19
    have hx20_20 : σ20.regs.get? Register.x20 = some (sign_extend (m := 64)
        (Sail.BitVec.extractLsb vs4 31 0 - Sail.BitVec.extractLsb vnd6 31 0)) :=
      obs_branch_nottaken_other hobs20 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_19
    have hx22_20 : σ20.regs.get? Register.x22 = some vnd6 :=
      obs_branch_nottaken_other hobs20 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_19
    have hx23_20 : σ20.regs.get? Register.x23 = some (viov2 + sign_extend (m := 64) (0x010#12)) :=
      obs_branch_nottaken_other hobs20 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_19
    have hx26_20 : σ20.regs.get? Register.x26 = some vbase :=
      obs_branch_nottaken_other hobs20 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_19
    have hx28_20 : σ20.regs.get? Register.x28 = some vt3 :=
      obs_branch_nottaken_other hobs20 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_19
    have hload20 : SvfprintfSliceLoaded σ20.mem := hmem20 ▸ hload19
    have hfp20 : FlushPinsLoaded σ20.mem := hmem20 ▸ hfp19
    have htot20 : SlotHolds vsp 0x010 vtot σ20.mem := hmem20 ▸ htot19
    have hstr20 : SlotHolds vsp 0x008 vstr σ20.mem := hmem20 ▸ hstr19
    -- === 7904: mv a5,a6  ⇒  x15 := vlen ===
    obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80007904 hload20
    have hx16n21 : (afterNextPC (afterPrelude σ20) (0x80007904#64)).regs.get? Register.x16 = some vlen := by
      rw [get?_afterNextPC σ20 (0x80007904#64) _ (by decide) (by decide)]; exact hx16_20
    obtain ⟨σ21, i21, hs21s, hi21, hG21, hmem21, hobs21⟩ :=
      stepObs_alu σ20 i20 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80007904#64) vmi20 (0x00080793#32)
        (instruction.ITYPE (0x000#12, regidx.Regidx 0x10#5, regidx.Regidx 0x0f#5, iop.ADDI))
        Register.x15 (vlen + sign_extend (m := 64) (0x000#12))
        (0x93#8) (0x07#8) (0x08#8) (0x00#8)
        hG20 hpc20 hmi20 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
        (Vsa.Sim.DecodeTable.decode_00080793 (afterPrelude σ20)
          (by rw [get?_afterPrelude σ20 _ (by decide)]; exact hG20.misa)
          (by rw [get?_afterPrelude σ20 _ (by decide)]; exact hG20.cur_privilege)
          (by rw [get?_afterPrelude σ20 _ (by decide)]; exact hG20.mseccfg))
        (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x10#5) (regidx.Regidx 0x0f#5) vlen
          (afterNextPC (afterPrelude σ20) (0x80007904#64))
          (sigma3_alu σ20 (0x80007904#64) Register.x15 (vlen + sign_extend (m := 64) (0x000#12)))
          (rX_bits_x16 _ vlen hx16n21) (wX_bits_x15 _ (vlen + sign_extend (m := 64) (0x000#12))))
        (by decide) (by decide) (by decide) (by decide) (by decide)
        hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi20
    have hstep21 : Step ⟨σ20, i20, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
        ⟨σ21, i21, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs21s
    have hpc21 : σ21.regs.get? Register.PC = some (0x80007908#64) := by
      have := obs_alu_pc hobs21
      rwa [show BitVec.addInt (0x80007904#64 : BitVec 64) 4 = (0x80007908#64 : BitVec 64) from by
        apply BitVec.eq_of_toNat_eq; decide] at this
    have hx15_21 : σ21.regs.get? Register.x15 = some vlen := by
      have := obs_alu_rd hobs21 (by decide) (by decide) (by decide) (by decide) (by decide)
      rwa [show (vlen + sign_extend (m := 64) (0x000#12) : BitVec 64) = vlen from by
        rw [show sign_extend (m := 64) (0x000#12) = (0#64) from by
          apply BitVec.eq_of_toNat_eq; decide, BitVec.add_zero]] at this
    have hx2_21 : σ21.regs.get? Register.x2 = some vsp :=
      obs_alu_other hobs21 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_20
    have hx5_21 : σ21.regs.get? Register.x5 = some vt0 :=
      obs_alu_other hobs21 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_20
    have hx6_21 : σ21.regs.get? Register.x6 = some (vt1 &&& sign_extend (m := 64) (0x004#12)) :=
      obs_alu_other hobs21 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_20
    have hx8_21 : σ21.regs.get? Register.x8 = some v8 :=
      obs_alu_other hobs21 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_20
    have hx12_21 : σ21.regs.get? Register.x12 = some (vcur + vnd6) :=
      obs_alu_other hobs21 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_20
    have hx16_21 : σ21.regs.get? Register.x16 = some vlen :=
      obs_alu_other hobs21 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_20
    have hx20_21 : σ21.regs.get? Register.x20 = some (sign_extend (m := 64)
        (Sail.BitVec.extractLsb vs4 31 0 - Sail.BitVec.extractLsb vnd6 31 0)) :=
      obs_alu_other hobs21 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_20
    have hx22_21 : σ21.regs.get? Register.x22 = some vnd6 :=
      obs_alu_other hobs21 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_20
    have hx23_21 : σ21.regs.get? Register.x23 = some (viov2 + sign_extend (m := 64) (0x010#12)) :=
      obs_alu_other hobs21 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_20
    have hx26_21 : σ21.regs.get? Register.x26 = some vbase :=
      obs_alu_other hobs21 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_20
    have hx28_21 : σ21.regs.get? Register.x28 = some vt3 :=
      obs_alu_other hobs21 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_20
    have hload21 : SvfprintfSliceLoaded σ21.mem := hmem21 ▸ hload20
    have hfp21 : FlushPinsLoaded σ21.mem := hmem21 ▸ hfp20
    have htot21 : SlotHolds vsp 0x010 vtot σ21.mem := hmem21 ▸ htot20
    have hstr21 : SlotHolds vsp 0x008 vstr σ21.mem := hmem21 ▸ hstr20
    obtain ⟨c', hstepsT, hG', hpc', hx1', hx10', hx11', hx12', hx2', hx5', hx6', hx8', hx16',
        hx20', hx22', hx23', hx26', hx28', hmem', htick', hmi', hkeepT⟩ :=
      iov2Tail_spec vsp vt0 (vt1 &&& sign_extend (m := 64) (0x004#12)) v8 (vcur + vnd6) vlen
        (sign_extend (m := 64)
          (Sail.BitVec.extractLsb vs4 31 0 - Sail.BitVec.extractLsb vnd6 31 0))
        vnd6 (viov2 + sign_extend (m := 64) (0x010#12)) vbase vt3 vlen vstr vtot
        ⟨σ21, i21, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
        hG21 hpc21 hx2_21 hx5_21 hx6_21 hx8_21 hx12_21 hx15_21 hx16_21 hx20_21 hx22_21 hx23_21
        hx26_21 hx28_21 hload21 hfp21 htot21 hstr21 hcurne hspwin hsphi hspalign hi21
    refine ⟨c', hheadsteps.trans ((Steps.single hstep20).trans ((Steps.single hstep21).trans hstepsT)),
      hG', hpc', hx1', hx10', hx11', hx12', hx2', hx5', hx6', hx8', hx16', hx20', hx22', hx23',
      hx26', hx28', ?_, htick', hmi',
      keep_trans (keep_alu hobs21 (by decide)
        (keep_bnottaken hobs20 (by decide) hkeepHead)) hkeepT⟩
    rw [hmem', hmem21, hmem20, hmem19base, if_neg (by decide)]

end Vsa.Sim
