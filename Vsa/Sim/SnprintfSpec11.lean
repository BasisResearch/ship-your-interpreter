import Vsa.Sim.SnprintfSpec7
import Vsa.Sim.DecodeTable.Batch14Part05
import Vsa.Sim.DecodeTable.Batch13Part02
import Vsa.Sim.DecodeTable.Batch12Part07
import Vsa.Sim.DecodeTable.Batch11Part27
import Vsa.Sim.DecodeTable.Batch10Part30
import Vsa.Sim.DecodeTable.Batch09Part28
import Vsa.Sim.DecodeTable.Batch09Part26
import Vsa.Sim.DecodeTable.Batch09Part25
import Vsa.Sim.DecodeTable.Batch09Part24
import Vsa.Sim.DecodeTable.Batch09Part10
import Vsa.Sim.DecodeTable.Batch08Part31
import Vsa.Sim.DecodeTable.Batch06Part28
import Vsa.Sim.DecodeTable.Batch05Part21
import Vsa.Sim.DecodeTable.Batch05Part07
import Vsa.Sim.DecodeTable.Batch04Part07
import Vsa.Sim.DecodeTable.Batch03Part15
import Vsa.Sim.DecodeTable.Batch03Part01
import Vsa.Sim.DecodeTable.Batch02Part24
import Vsa.Sim.DecodeTable.Batch02Part20
import Vsa.Sim.DecodeTable.Batch01Part21
import Vsa.Sim.DecodeTable.Batch01Part02

/-!
# M3 Layer-3 — `SnprintfSpec11` : PRINT-macro entry → first (sign) iovec entry (`_pe`)

The `svfprintf` PRINT/iov segment head that `snprintf("%lld", negative)` runs
straight after digit formatting.  From the PRINT-macro entry `0x8000782c` (where
`entryToPrint_neg_spec`, `SnprintfSpec8`, lands) this covers the executed path

```
  782c: ld   a2,240(sp)     a2 := cursor  (running dest-buffer pointer)
  7830: andi t0,t1,132      t0 := flags & 0x84   (left-justify / zero-pad bits)
  7834: mv   a0,a2
  7838: beq  t0,zero,7cd4   taken (no adjust-justify flags for %lld)
  7cd4: subw a4,t3,a6       a4 := (payload_end - len)  (pad count)
  7cd8: blt  zero,a4,8c38   NOT taken (no left padding)
  7cdc: lbu  a4,167(sp)     a4 := the sign byte  ('-')
  7ce0: bne  a4,zero,7844   taken (there IS a sign)
  7844: lw   t4,232(sp)     t4 := iovcnt
  7848: li   s11,0
  784c: addi a1,sp,167      a1 := &sign_byte
  7850: addi a2,a2,1        a2 := cursor+1
  7854: addiw t4,t4,1       t4 := iovcnt+1
  7858: li   a5,1
  785c: sd   a1,0(s7)       iov[k].iov_base := &sign_byte
  7860: sd   a5,8(s7)       iov[k].iov_len  := 1
  7864: sd   a2,240(sp)     store cursor+1
  7868: sw   t4,232(sp)     store iovcnt+1
  786c: li   a1,7
  7870: addi s7,s7,16       iov pointer += 16
  7874: blt  a1,t4,7b00     NOT taken (iovcnt+1 ≤ 7, no flush)
  7878: beq  s11,zero,78ac  taken → 0x800078ac
```

`printEntryToSignIov_spec` is one `Steps` chain over exactly these 21
instructions.  The **postcondition** is the first `iovec` entry of the FILE
sink's gather buffer — the sign byte `'-'`:

* `iov[k].iov_base := sp+167` (the address of the `'-'` byte the digit path left
  at `sp+167`) and `iov[k].iov_len := 1`, written at the iov cursor `s7 = viov`;
* the iov cursor `s7` advanced by 16 (one `struct iovec`);
* the cursor field `mem[sp+240]` bumped by 1 and the iov count `mem[sp+232]`
  bumped by 1.

This is the field-level postcondition a later agent feeds into the
`__ssputs_r`/memcpy composition.

The three branch guards are discharged from explicit hypotheses about the parsed
flag word (`hflag84`), the (non-positive) pad count (`hpad`), and the
sign-present marker byte at `sp+167` (`hsignbyte`).  See the report for how they
compose onto `entryToPrint_neg_spec`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (SvfprintfSliceLoaded FlushPinsLoaded)

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- `SvfprintfSliceLoaded` survives a disjoint 4-byte `writeMap4` (four inserts
above `0x80009000`). -/
theorem svfprintfSlice_writeMap4_pe (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat)
    (d : BitVec (8 * 4)) (ha : 0x80009000 ≤ a) (h : SvfprintfSliceLoaded mem) :
    SvfprintfSliceLoaded (writeMap4 mem a d) :=
  svfprintfSlice_insert_sn4 _ _ _ (by omega) (svfprintfSlice_insert_sn4 _ _ _ (by omega)
    (svfprintfSlice_insert_sn4 _ _ _ (by omega) (svfprintfSlice_insert_sn4 _ _ _ (by omega) h)))

/-- `FlushPinsLoaded` survives a disjoint 4-byte `writeMap4` (four inserts above
`0x8000b000`). -/
theorem flushPins_writeMap4_pe (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat)
    (d : BitVec (8 * 4)) (ha : 0x8000b000 ≤ a) (h : FlushPinsLoaded mem) :
    FlushPinsLoaded (writeMap4 mem a d) :=
  flushPins_insert_fl _ _ _ (by omega) (flushPins_insert_fl _ _ _ (by omega)
    (flushPins_insert_fl _ _ _ (by omega) (flushPins_insert_fl _ _ _ (by omega) h)))

/-- **PRINT-macro entry → first (sign-byte) iovec entry.**

From `0x8000782c` (the PRINT-macro entry that `entryToPrint_neg_spec` reaches) to
`0x800078ac`, one `Steps` chain over the 21 executed instructions that build the
first `struct iovec` of the FILE sink's gather buffer — the sign byte `'-'`.

Register naming at entry: `x2 = vsp`, `x6 = vt1` (parsed flag word), `x28 = vt3`
(payload end), `x16 = vlen` (`= a6`, the sign-inclusive length), `x23 = viov`
(the current iov cursor).  Memory: `mem[sp+240]` holds the running cursor
(8 bytes = `vcur`), `mem[sp+232]` the iov count (4 bytes = `vcnt32`), and
`sp+167` the sign byte `signB` (`≠ 0`, the digit path's `'-'`).

Postcondition (the iovec entry): `mem[viov, viov+8) := sp+167`,
`mem[viov+8, viov+16) := 1`, `x23 = viov + 16`, and the two FILE fields bumped
by one. -/
theorem printEntryToSignIov_spec
    (vsp vt1 vt3 vlen viov vcur : BitVec 64) (vcnt : BitVec 32) (signB : BitVec 8)
    (c : Config)
    (hG : GoodState c.σ)
    (hload : SvfprintfSliceLoaded c.σ.mem)
    (hfp : FlushPinsLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x8000782c#64))
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx6 : c.σ.regs.get? Register.x6 = some vt1)
    (hx28 : c.σ.regs.get? Register.x28 = some vt3)
    (hx16 : c.σ.regs.get? Register.x16 = some vlen)
    (hx23 : c.σ.regs.get? Register.x23 = some viov)
    -- the running cursor at sp+240 (8-byte)
    (hcur : SlotHolds vsp 0x0f0 vcur c.σ.mem)
    -- the iov count at sp+232 (4-byte, low half `vcnt`)
    (hcnt0 : c.σ.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat]? = some (vcnt.extractLsb' 0 8))
    (hcnt1 : c.σ.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 1]? = some (vcnt.extractLsb' 8 8))
    (hcnt2 : c.σ.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 2]? = some (vcnt.extractLsb' 16 8))
    (hcnt3 : c.σ.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 3]? = some (vcnt.extractLsb' 24 8))
    -- the sign byte at sp+167
    (hsign : c.σ.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some signB)
    -- branch guards (all from the negative-%lld path, upstream)
    (hflag84 : vt1 &&& sign_extend (m := 64) (0x084#12) = 0#64)
    (hpad : zopz0zI_s (0#64) (sign_extend (m := 64)
      (Sail.BitVec.extractLsb vt3 31 0 - Sail.BitVec.extractLsb vlen 31 0)) = false)
    (hsignne : ((zero_extend (m := 64) signB : BitVec 64) != (0#64)) = true)
    (hcntlt : zopz0zI_s (0x7#64)
      (sign_extend (m := 64) (Sail.BitVec.extractLsb
        ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0)) = false)
    -- stack frame: RAM above the svfprintf code region, above HTIF, 8-aligned;
    -- room for sp+240 and the sp+232 word (the stores must not clobber the code slice)
    (hsplo : 0x80009000 ≤ vsp.toNat)
    (hsphi : vsp.toNat + 356 ≤ 0x100000000)
    (hspwin : tohostAddr + 16 + 64 ≤ vsp.toNat)
    (hspalign : vsp.toNat % 8 = 0)
    -- the iov gather buffer: RAM above the svfprintf code region, above HTIF, 8-aligned
    (hiovlo : 0x80009000 ≤ viov.toNat)
    (hiovhi : viov.toNat + 16 ≤ 0x100000000)
    (hiovwin : tohostAddr + 16 ≤ viov.toNat)
    (hiovalign : viov.toNat % 8 = 0)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x800078ac#64) ∧
      -- iov cursor advanced by one struct iovec
      c'.σ.regs.get? Register.x23 = some (viov + sign_extend (m := 64) (0x010#12)) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      -- the sign-byte iovec entry: base = &sign_byte (sp+167), len = 1
      c'.σ.mem = writeMap4
        (writeMap8
          (writeMap8
            (writeMap8 c.σ.mem
              viov.toNat (sdData_val (vsp + sign_extend (m := 64) (0x0a7#12))))
            (viov + sign_extend (m := 64) (0x008#12)).toNat (sdData_val (0x1#64)))
          (vsp + sign_extend (m := 64) (0x0f0#12)).toNat
            (sdData_val (vcur + sign_extend (m := 64) (0x001#12))))
        (vsp + sign_extend (m := 64) (0x0e8#12)).toNat
          (swData (sign_extend (m := 64)
            (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64)
              + sign_extend (m := 64) (0x001#12)) 31 0))) ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) := by
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
  have hnw : vsp.toNat + 348 < 2 ^ 64 := by omega
  -- effective-address rewrites for the two FILE fields
  have hoff240 : (vsp + sign_extend (m := 64) (0x0f0#12)).toNat = vsp.toNat + 240 :=
    addoff_toNat_sn5 vsp (0x0f0#12) 240 (by omega) (by decide) hnw
  have hoff232 : (vsp + sign_extend (m := 64) (0x0e8#12)).toNat = vsp.toNat + 232 :=
    addoff_toNat_sn5 vsp (0x0e8#12) 232 (by omega) (by decide) hnw
  have hoff167 : (vsp + sign_extend (m := 64) (0x0a7#12)).toNat = vsp.toNat + 167 :=
    addoff_toNat_sn5 vsp (0x0a7#12) 167 (by omega) (by decide) hnw
  have hoffiov0 : (viov + sign_extend (m := 64) (0x000#12)).toNat = viov.toNat :=
    addoff_toNat_sn5 viov (0x000#12) 0 (by omega) (by decide) (by omega)
  have hoffiov8 : (viov + sign_extend (m := 64) (0x008#12)).toNat = viov.toNat + 8 :=
    addoff_toNat_sn5 viov (0x008#12) 8 (by omega) (by decide) (by omega)
  -- === 782c: ld a2,240(sp)  ⇒  x12 := vcur ===
  obtain ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7⟩ := hcur
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_8000782c hload
  have hx2n1 : (afterNextPC (afterPrelude c.σ) (0x8000782c#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC c.σ (0x8000782c#64) _ (by decide) (by decide)]; exact hx2
  obtain ⟨σ1, i1, hs1s, hi1, hG1, hmem1, hobs1⟩ :=
    stepObs_alu c.σ c.tick c.steps (0x8000782c#64) vmi0 (0x0f013603#32)
      (instruction.LOAD (0x0f0#12, regidx.Regidx 0x02#5, regidx.Regidx 0x0c#5, false, 8))
      Register.x12 (sign_extend (m := 64)
        (((((((((sdData_val vcur).extractLsb' 56 8).append ((sdData_val vcur).extractLsb' 48 8)).append
          ((sdData_val vcur).extractLsb' 40 8)).append ((sdData_val vcur).extractLsb' 32 8)).append
          ((sdData_val vcur).extractLsb' 24 8)).append ((sdData_val vcur).extractLsb' 16 8)).append
          ((sdData_val vcur).extractLsb' 8 8)).append ((sdData_val vcur).extractLsb' 0 8)
          : BitVec (8 * 8)))
      (0x03#8) (0x36#8) (0x01#8) (0x0f#8)
      hG hpc hmi0 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_0f013603 (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (exec_ld c.σ (0x8000782c#64) (0x0f0#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x0c#5)
        (sigma3_alu c.σ (0x8000782c#64) Register.x12 (sign_extend (m := 64)
          (((((((((sdData_val vcur).extractLsb' 56 8).append ((sdData_val vcur).extractLsb' 48 8)).append
            ((sdData_val vcur).extractLsb' 40 8)).append ((sdData_val vcur).extractLsb' 32 8)).append
            ((sdData_val vcur).extractLsb' 24 8)).append ((sdData_val vcur).extractLsb' 16 8)).append
            ((sdData_val vcur).extractLsb' 8 8)).append ((sdData_val vcur).extractLsb' 0 8)
            : BitVec (8 * 8))))
        vsp _ _ _ _ _ _ _ _ hG (rX_bits_x2 _ vsp hx2n1)
        (wX_bits_x12 _ _)
        (by rw [hoff240]; omega) (by rw [hoff240]; omega) (Or.inr (by rw [hoff240]; omega))
        (by rw [hoff240]; omega)
        hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1s
  have hpc1 : σ1.regs.get? Register.PC = some (0x80007830#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x8000782c#64 : BitVec 64) 4 = (0x80007830#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx12_1 : σ1.regs.get? Register.x12 = some vcur := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [ve_sext_reassemble vcur] at this
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hx2_1 : σ1.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2
  have hx6_1 : σ1.regs.get? Register.x6 = some vt1 :=
    obs_alu_other hobs1 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6
  have hx28_1 : σ1.regs.get? Register.x28 = some vt3 :=
    obs_alu_other hobs1 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28
  have hx16_1 : σ1.regs.get? Register.x16 = some vlen :=
    obs_alu_other hobs1 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16
  have hx23_1 : σ1.regs.get? Register.x23 = some viov :=
    obs_alu_other hobs1 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23
  have hload1 : SvfprintfSliceLoaded σ1.mem := hmem1 ▸ hload
  have hfp1 : FlushPinsLoaded σ1.mem := hmem1 ▸ hfp
  have hsign1 : σ1.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some signB := hmem1 ▸ hsign
  have hcnt0_1 : σ1.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat]? = some (vcnt.extractLsb' 0 8) := hmem1 ▸ hcnt0
  have hcnt1_1 : σ1.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 1]? = some (vcnt.extractLsb' 8 8) := hmem1 ▸ hcnt1
  have hcnt2_1 : σ1.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 2]? = some (vcnt.extractLsb' 16 8) := hmem1 ▸ hcnt2
  have hcnt3_1 : σ1.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 3]? = some (vcnt.extractLsb' 24 8) := hmem1 ▸ hcnt3
  -- === 7830: andi t0,t1,132  ⇒  x5 := vt1 &&& sext 0x084 = 0 ===
  obtain ⟨hc0, hc1, hc2, hc3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80007830 hload1
  have hx6n2 : (afterNextPC (afterPrelude σ1) (0x80007830#64)).regs.get? Register.x6 = some vt1 := by
    rw [get?_afterNextPC σ1 (0x80007830#64) _ (by decide) (by decide)]; exact hx6_1
  obtain ⟨σ2, i2, hs2s, hi2, hG2, hmem2, hobs2⟩ :=
    stepObs_alu σ1 i1 (c.steps + 1) (0x80007830#64) vmi1 (0x08437293#32)
      (instruction.ITYPE (0x084#12, regidx.Regidx 0x06#5, regidx.Regidx 0x05#5, iop.ANDI))
      Register.x5 (vt1 &&& sign_extend (m := 64) (0x084#12))
      (0x93#8) (0x72#8) (0x43#8) (0x08#8)
      hG1 hpc1 hmi1 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_08437293 (afterPrelude σ1)
        (by rw [get?_afterPrelude σ1 _ (by decide)]; exact hG1.misa)
        (by rw [get?_afterPrelude σ1 _ (by decide)]; exact hG1.cur_privilege)
        (by rw [get?_afterPrelude σ1 _ (by decide)]; exact hG1.mseccfg))
      (execute_itype_andi_char (0x084#12) (regidx.Regidx 0x06#5) (regidx.Regidx 0x05#5) vt1
        (afterNextPC (afterPrelude σ1) (0x80007830#64))
        (sigma3_alu σ1 (0x80007830#64) Register.x5 (vt1 &&& sign_extend (m := 64) (0x084#12)))
        (rX_bits_x6 _ vt1 hx6n2) (wX_bits_x5 _ (vt1 &&& sign_extend (m := 64) (0x084#12))))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hc0 hc1 hc2 hc3 (by decide) (by decide) (by decide) hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2s
  have hpc2 : σ2.regs.get? Register.PC = some (0x80007834#64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x80007830#64 : BitVec 64) 4 = (0x80007834#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx5_2 : σ2.regs.get? Register.x5 = some (0#64) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hflag84] at this
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hx2_2 : σ2.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs2 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_1
  have hx12_2 : σ2.regs.get? Register.x12 = some vcur :=
    obs_alu_other hobs2 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_1
  have hx28_2 : σ2.regs.get? Register.x28 = some vt3 :=
    obs_alu_other hobs2 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_1
  have hx16_2 : σ2.regs.get? Register.x16 = some vlen :=
    obs_alu_other hobs2 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_1
  have hx23_2 : σ2.regs.get? Register.x23 = some viov :=
    obs_alu_other hobs2 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_1
  have hload2 : SvfprintfSliceLoaded σ2.mem := hmem2 ▸ hload1
  have hfp2 : FlushPinsLoaded σ2.mem := hmem2 ▸ hfp1
  have hsign2 : σ2.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some signB := hmem2 ▸ hsign1
  have hcnt0_2 : σ2.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat]? = some (vcnt.extractLsb' 0 8) := hmem2 ▸ hcnt0_1
  have hcnt1_2 : σ2.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 1]? = some (vcnt.extractLsb' 8 8) := hmem2 ▸ hcnt1_1
  have hcnt2_2 : σ2.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 2]? = some (vcnt.extractLsb' 16 8) := hmem2 ▸ hcnt2_1
  have hcnt3_2 : σ2.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 3]? = some (vcnt.extractLsb' 24 8) := hmem2 ▸ hcnt3_1
  -- === 7834: mv a0,a2  (addi a0,a2,0)  ⇒  x10 := vcur ===
  obtain ⟨hd0, hd1, hd2, hd3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80007834 hload2
  have hx12n3 : (afterNextPC (afterPrelude σ2) (0x80007834#64)).regs.get? Register.x12 = some vcur := by
    rw [get?_afterNextPC σ2 (0x80007834#64) _ (by decide) (by decide)]; exact hx12_2
  obtain ⟨σ3, i3, hs3s, hi3, hG3, hmem3, hobs3⟩ :=
    stepObs_alu σ2 i2 (c.steps + 1 + 1) (0x80007834#64) vmi2 (0x00060513#32)
      (instruction.ITYPE (0x000#12, regidx.Regidx 0x0c#5, regidx.Regidx 0x0a#5, iop.ADDI))
      Register.x10 (vcur + sign_extend (m := 64) (0x000#12))
      (0x13#8) (0x05#8) (0x06#8) (0x00#8)
      hG2 hpc2 hmi2 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_00060513 (afterPrelude σ2)
        (by rw [get?_afterPrelude σ2 _ (by decide)]; exact hG2.misa)
        (by rw [get?_afterPrelude σ2 _ (by decide)]; exact hG2.cur_privilege)
        (by rw [get?_afterPrelude σ2 _ (by decide)]; exact hG2.mseccfg))
      (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0a#5) vcur
        (afterNextPC (afterPrelude σ2) (0x80007834#64))
        (sigma3_alu σ2 (0x80007834#64) Register.x10 (vcur + sign_extend (m := 64) (0x000#12)))
        (rX_bits_x12 _ vcur hx12n3) (wX_bits_x10 _ (vcur + sign_extend (m := 64) (0x000#12))))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hd0 hd1 hd2 hd3 (by decide) (by decide) (by decide) hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3s
  have hpc3 : σ3.regs.get? Register.PC = some (0x80007838#64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x80007834#64 : BitVec 64) 4 = (0x80007838#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hx5_3 : σ3.regs.get? Register.x5 = some (0#64) :=
    obs_alu_other hobs3 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_2
  have hx2_3 : σ3.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs3 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_2
  have hx12_3 : σ3.regs.get? Register.x12 = some vcur :=
    obs_alu_other hobs3 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_2
  have hx28_3 : σ3.regs.get? Register.x28 = some vt3 :=
    obs_alu_other hobs3 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_2
  have hx16_3 : σ3.regs.get? Register.x16 = some vlen :=
    obs_alu_other hobs3 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_2
  have hx23_3 : σ3.regs.get? Register.x23 = some viov :=
    obs_alu_other hobs3 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_2
  have hload3 : SvfprintfSliceLoaded σ3.mem := hmem3 ▸ hload2
  have hfp3 : FlushPinsLoaded σ3.mem := hmem3 ▸ hfp2
  have hsign3 : σ3.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some signB := hmem3 ▸ hsign2
  -- === 7838: beq t0,zero,7cd4  (taken since t0 = 0) ===
  obtain ⟨he0, he1, he2, he3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80007838 hload3
  have hx5n4 : (rX_bits (regidx.Regidx 0x05#5)).run (afterNextPC (afterPrelude σ3) (0x80007838#64))
      = .ok (0#64) (afterNextPC (afterPrelude σ3) (0x80007838#64)) := by
    apply rX_bits_x5
    rw [get?_afterNextPC σ3 (0x80007838#64) _ (by decide) (by decide)]; exact hx5_3
  obtain ⟨σ4, i4, hs4s, hi4, hG4, hmem4, hobs4⟩ :=
    stepObs_branch_taken σ3 i3 (c.steps + 1 + 1 + 1) (0x80007838#64) vmi3
      (0x049c#13) (regidx.Regidx 0x05#5) (regidx.Regidx 0x00#5) bop.BEQ (0x48028e63#32)
      (0x63#8) (0x8e#8) (0x02#8) (0x48#8)
      hG3 hpc3 hmi3 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_48028e63 (afterPrelude σ3)
        (by rw [get?_afterPrelude σ3 _ (by decide)]; exact hG3.misa)
        (by rw [get?_afterPrelude σ3 _ (by decide)]; exact hG3.cur_privilege)
        (by rw [get?_afterPrelude σ3 _ (by decide)]; exact hG3.mseccfg))
      (execute_btype_beq_taken (0x049c#13) (regidx.Regidx 0x05#5) (regidx.Regidx 0x00#5)
        (0#64) (0#64) (0x80007838#64) initMisa (afterNextPC (afterPrelude σ3) (0x80007838#64))
        hx5n4 (rX_bits_zero _)
        (by rw [get?_afterNextPC σ3 (0x80007838#64) _ (by decide) (by decide)]; exact hpc3)
        (by rw [get?_afterNextPC σ3 (0x80007838#64) _ (by decide) (by decide)]; exact hG3.misa)
        (by decide) (by decide))
      he0 he1 he2 he3 (by decide) (by decide) (by decide) hi3
  have hstep4 : Step ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ := hs4s
  have hpc4 : σ4.regs.get? Register.PC = some (0x80007cd4#64) := by
    have := obs_branch_taken_pc hobs4
    rwa [show ((0x80007838#64 : BitVec 64) + sign_extend (m := 64) (0x049c#13))
      = (0x80007cd4#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi4, hmi4⟩ := obs_branch_taken_minstret hobs4
  have hx2_4 : σ4.regs.get? Register.x2 = some vsp :=
    obs_branch_taken_other hobs4 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_3
  have hx12_4 : σ4.regs.get? Register.x12 = some vcur :=
    obs_branch_taken_other hobs4 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_3
  have hx28_4 : σ4.regs.get? Register.x28 = some vt3 :=
    obs_branch_taken_other hobs4 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_3
  have hx16_4 : σ4.regs.get? Register.x16 = some vlen :=
    obs_branch_taken_other hobs4 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_3
  have hx23_4 : σ4.regs.get? Register.x23 = some viov :=
    obs_branch_taken_other hobs4 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_3
  have hload4 : SvfprintfSliceLoaded σ4.mem := hmem4 ▸ hload3
  have hfp4 : FlushPinsLoaded σ4.mem := hmem4 ▸ hfp3
  have hsign4 : σ4.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some signB := hmem4 ▸ hsign3
  -- === 7cd4: subw a4,t3,a6  ⇒  x14 := sext (extractLsb vt3 - extractLsb vlen) === (FlushPins)
  obtain ⟨hf0, hf1, hf2, hf3⟩ := Vsa.Sim.Code.flushPins_at_80007cd4 hfp4
  have hx28n5 : (afterNextPC (afterPrelude σ4) (0x80007cd4#64)).regs.get? Register.x28 = some vt3 := by
    rw [get?_afterNextPC σ4 (0x80007cd4#64) _ (by decide) (by decide)]; exact hx28_4
  have hx16n5 : (afterNextPC (afterPrelude σ4) (0x80007cd4#64)).regs.get? Register.x16 = some vlen := by
    rw [get?_afterNextPC σ4 (0x80007cd4#64) _ (by decide) (by decide)]; exact hx16_4
  obtain ⟨σ5, i5, hs5s, hi5, hG5, hmem5, hobs5⟩ :=
    stepObs_alu σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x80007cd4#64) vmi4 (0x410e073b#32)
      (instruction.RTYPEW (regidx.Regidx 0x10#5, regidx.Regidx 0x1c#5, regidx.Regidx 0x0e#5, ropw.SUBW))
      Register.x14 (sign_extend (m := 64)
        ((Sail.BitVec.extractLsb vt3 31 0) - (Sail.BitVec.extractLsb vlen 31 0)))
      (0x3b#8) (0x07#8) (0x0e#8) (0x41#8)
      hG4 hpc4 hmi4 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_410e073b (afterPrelude σ4)
        (by rw [get?_afterPrelude σ4 _ (by decide)]; exact hG4.misa)
        (by rw [get?_afterPrelude σ4 _ (by decide)]; exact hG4.cur_privilege)
        (by rw [get?_afterPrelude σ4 _ (by decide)]; exact hG4.mseccfg))
      (execute_rtypew_subw_char (regidx.Regidx 0x10#5) (regidx.Regidx 0x1c#5) (regidx.Regidx 0x0e#5)
        vt3 vlen (afterNextPC (afterPrelude σ4) (0x80007cd4#64))
        (sigma3_alu σ4 (0x80007cd4#64) Register.x14
          (sign_extend (m := 64) ((Sail.BitVec.extractLsb vt3 31 0) - (Sail.BitVec.extractLsb vlen 31 0))))
        (rX_bits_x28 _ vt3 hx28n5) (rX_bits_x16 _ vlen hx16n5)
        (wX_bits_x14 _ (sign_extend (m := 64)
          ((Sail.BitVec.extractLsb vt3 31 0) - (Sail.BitVec.extractLsb vlen 31 0)))))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hf0 hf1 hf2 hf3 (by decide) (by decide) (by decide) hi4
  have hstep5 : Step ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ := hs5s
  have hpc5 : σ5.regs.get? Register.PC = some (0x80007cd8#64) := by
    have := obs_alu_pc hobs5
    rwa [show BitVec.addInt (0x80007cd4#64 : BitVec 64) 4 = (0x80007cd8#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx14_5 : σ5.regs.get? Register.x14 = some (sign_extend (m := 64)
      ((Sail.BitVec.extractLsb vt3 31 0) - (Sail.BitVec.extractLsb vlen 31 0))) :=
    obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi5, hmi5⟩ := obs_alu_minstret hobs5
  have hx2_5 : σ5.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs5 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_4
  have hx12_5 : σ5.regs.get? Register.x12 = some vcur :=
    obs_alu_other hobs5 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_4
  have hx23_5 : σ5.regs.get? Register.x23 = some viov :=
    obs_alu_other hobs5 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_4
  have hload5 : SvfprintfSliceLoaded σ5.mem := hmem5 ▸ hload4
  have hfp5 : FlushPinsLoaded σ5.mem := hmem5 ▸ hfp4
  have hsign5 : σ5.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some signB := hmem5 ▸ hsign4
  -- === 7cd8: blt zero,a4,8c38  (NOT taken: hpad) === (FlushPins)
  obtain ⟨hg0, hg1, hg2, hg3⟩ := Vsa.Sim.Code.flushPins_at_80007cd8 hfp5
  have hz6 : (rX_bits (regidx.Regidx 0x00#5)).run (afterNextPC (afterPrelude σ5) (0x80007cd8#64))
      = .ok (0#64) (afterNextPC (afterPrelude σ5) (0x80007cd8#64)) := rX_bits_zero _
  have hv6 : (rX_bits (regidx.Regidx 0x0e#5)).run (afterNextPC (afterPrelude σ5) (0x80007cd8#64))
      = .ok (sign_extend (m := 64) ((Sail.BitVec.extractLsb vt3 31 0) - (Sail.BitVec.extractLsb vlen 31 0)))
        (afterNextPC (afterPrelude σ5) (0x80007cd8#64)) := by
    apply rX_bits_x14
    rw [get?_afterNextPC σ5 (0x80007cd8#64) _ (by decide) (by decide)]; exact hx14_5
  obtain ⟨σ6, i6, hs6s, hi6, hG6, hmem6, hobs6⟩ :=
    stepObs_branch_nottaken σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x80007cd8#64) vmi5
      (0x0f60#13) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0e#5) bop.BLT (0x76e040e3#32)
      (0xe3#8) (0x40#8) (0xe0#8) (0x76#8)
      hG5 hpc5 hmi5 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_76e040e3 (afterPrelude σ5)
        (by rw [get?_afterPrelude σ5 _ (by decide)]; exact hG5.misa)
        (by rw [get?_afterPrelude σ5 _ (by decide)]; exact hG5.cur_privilege)
        (by rw [get?_afterPrelude σ5 _ (by decide)]; exact hG5.mseccfg))
      (execute_btype_blt_nottaken (0x0f60#13) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0e#5)
        (0#64) (sign_extend (m := 64) ((Sail.BitVec.extractLsb vt3 31 0) - (Sail.BitVec.extractLsb vlen 31 0)))
        (afterNextPC (afterPrelude σ5) (0x80007cd8#64)) hz6 hv6 hpad)
      hg0 hg1 hg2 hg3 (by decide) (by decide) (by decide) hi5
  have hstep6 : Step ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ ⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs6s
  have hpc6 : σ6.regs.get? Register.PC = some (0x80007cdc#64) := by
    have := obs_branch_nottaken_pc hobs6
    rwa [show BitVec.addInt (0x80007cd8#64 : BitVec 64) 4 = (0x80007cdc#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi6, hmi6⟩ := obs_branch_nottaken_minstret hobs6
  have hx2_6 : σ6.regs.get? Register.x2 = some vsp :=
    obs_branch_nottaken_other hobs6 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_5
  have hx12_6 : σ6.regs.get? Register.x12 = some vcur :=
    obs_branch_nottaken_other hobs6 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_5
  have hx23_6 : σ6.regs.get? Register.x23 = some viov :=
    obs_branch_nottaken_other hobs6 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_5
  have hload6 : SvfprintfSliceLoaded σ6.mem := hmem6 ▸ hload5
  have hfp6 : FlushPinsLoaded σ6.mem := hmem6 ▸ hfp5
  have hsign6 : σ6.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some signB := hmem6 ▸ hsign5
  -- === 7cdc: lbu a4,167(sp)  ⇒  x14 := zext signB === (FlushPins)
  obtain ⟨hh0, hh1, hh2, hh3⟩ := Vsa.Sim.Code.flushPins_at_80007cdc hfp6
  have hx2n7 : (afterNextPC (afterPrelude σ6) (0x80007cdc#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ6 (0x80007cdc#64) _ (by decide) (by decide)]; exact hx2_6
  obtain ⟨σ7, i7, hs7s, hi7, hG7, hmem7, hobs7⟩ :=
    stepObs_alu σ6 i6 (c.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x80007cdc#64) vmi6 (0x0a714703#32)
      (instruction.LOAD (0x0a7#12, regidx.Regidx 0x02#5, regidx.Regidx 0x0e#5, true, 1))
      Register.x14 (zero_extend (m := 64) signB)
      (0x03#8) (0x47#8) (0x71#8) (0x0a#8)
      hG6 hpc6 hmi6 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_0a714703 (afterPrelude σ6)
        (by rw [get?_afterPrelude σ6 _ (by decide)]; exact hG6.misa)
        (by rw [get?_afterPrelude σ6 _ (by decide)]; exact hG6.cur_privilege)
        (by rw [get?_afterPrelude σ6 _ (by decide)]; exact hG6.mseccfg))
      (exec_lbu_gen σ6 (0x80007cdc#64) (0x0a7#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x0e#5)
        vsp signB _ hG6 (rX_bits_x2 _ vsp hx2n7)
        (wX_bits_x14 _ (zero_extend (m := 64) signB))
        (by rw [hoff167]; omega) (by rw [hoff167]; omega) (Or.inr (by rw [hoff167]; omega))
        hsign6)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hh0 hh1 hh2 hh3 (by decide) (by decide) (by decide) hi6
  have hstep7 : Step ⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ7, i7, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs7s
  have hpc7 : σ7.regs.get? Register.PC = some (0x80007ce0#64) := by
    have := obs_alu_pc hobs7
    rwa [show BitVec.addInt (0x80007cdc#64 : BitVec 64) 4 = (0x80007ce0#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx14_7 : σ7.regs.get? Register.x14 = some (zero_extend (m := 64) signB) :=
    obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi7, hmi7⟩ := obs_alu_minstret hobs7
  have hx2_7 : σ7.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs7 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_6
  have hx12_7 : σ7.regs.get? Register.x12 = some vcur :=
    obs_alu_other hobs7 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_6
  have hx23_7 : σ7.regs.get? Register.x23 = some viov :=
    obs_alu_other hobs7 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_6
  have hload7 : SvfprintfSliceLoaded σ7.mem := hmem7 ▸ hload6
  have hcnt0_7 : σ7.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat]? = some (vcnt.extractLsb' 0 8) := by
    rw [hmem7, hmem6, hmem5, hmem4, hmem3]; exact hcnt0_2
  have hcnt1_7 : σ7.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 1]? = some (vcnt.extractLsb' 8 8) := by
    rw [hmem7, hmem6, hmem5, hmem4, hmem3]; exact hcnt1_2
  have hcnt2_7 : σ7.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 2]? = some (vcnt.extractLsb' 16 8) := by
    rw [hmem7, hmem6, hmem5, hmem4, hmem3]; exact hcnt2_2
  have hcnt3_7 : σ7.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 3]? = some (vcnt.extractLsb' 24 8) := by
    rw [hmem7, hmem6, hmem5, hmem4, hmem3]; exact hcnt3_2
  -- === 7ce0: bne a4,zero,7844  (taken: signB ≠ 0) === (FlushPins)
  have hfp7 : FlushPinsLoaded σ7.mem := hmem7 ▸ hfp6
  obtain ⟨hk0, hk1, hk2, hk3⟩ := Vsa.Sim.Code.flushPins_at_80007ce0 hfp7
  have hx14n8 : (rX_bits (regidx.Regidx 0x0e#5)).run (afterNextPC (afterPrelude σ7) (0x80007ce0#64))
      = .ok (zero_extend (m := 64) signB) (afterNextPC (afterPrelude σ7) (0x80007ce0#64)) := by
    apply rX_bits_x14
    rw [get?_afterNextPC σ7 (0x80007ce0#64) _ (by decide) (by decide)]; exact hx14_7
  obtain ⟨σ8, i8, hs8s, hi8, hG8, hmem8, hobs8⟩ :=
    stepObs_branch_taken σ7 i7 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80007ce0#64) vmi7
      (0x1b64#13) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x00#5) bop.BNE (0xb60712e3#32)
      (0xe3#8) (0x12#8) (0x07#8) (0xb6#8)
      hG7 hpc7 hmi7 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_b60712e3 (afterPrelude σ7)
        (by rw [get?_afterPrelude σ7 _ (by decide)]; exact hG7.misa)
        (by rw [get?_afterPrelude σ7 _ (by decide)]; exact hG7.cur_privilege)
        (by rw [get?_afterPrelude σ7 _ (by decide)]; exact hG7.mseccfg))
      (execute_btype_bne_taken (0x1b64#13) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x00#5)
        (zero_extend (m := 64) signB) (0#64) (0x80007ce0#64) initMisa
        (afterNextPC (afterPrelude σ7) (0x80007ce0#64))
        hx14n8 (rX_bits_zero _)
        (by rw [get?_afterNextPC σ7 (0x80007ce0#64) _ (by decide) (by decide)]; exact hpc7)
        (by rw [get?_afterNextPC σ7 (0x80007ce0#64) _ (by decide) (by decide)]; exact hG7.misa)
        (by decide) hsignne)
      hk0 hk1 hk2 hk3 (by decide) (by decide) (by decide) hi7
  have hstep8 : Step ⟨σ7, i7, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ8, i8, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs8s
  have hpc8 : σ8.regs.get? Register.PC = some (0x80007844#64) := by
    have := obs_branch_taken_pc hobs8
    rwa [show ((0x80007ce0#64 : BitVec 64) + sign_extend (m := 64) (0x1b64#13))
      = (0x80007844#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi8, hmi8⟩ := obs_branch_taken_minstret hobs8
  have hx2_8 : σ8.regs.get? Register.x2 = some vsp :=
    obs_branch_taken_other hobs8 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_7
  have hx12_8 : σ8.regs.get? Register.x12 = some vcur :=
    obs_branch_taken_other hobs8 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_7
  have hx23_8 : σ8.regs.get? Register.x23 = some viov :=
    obs_branch_taken_other hobs8 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_7
  have hload8 : SvfprintfSliceLoaded σ8.mem := hmem8 ▸ hload7
  have hcnt0_8 : σ8.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat]? = some (vcnt.extractLsb' 0 8) := hmem8 ▸ hcnt0_7
  have hcnt1_8 : σ8.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 1]? = some (vcnt.extractLsb' 8 8) := hmem8 ▸ hcnt1_7
  have hcnt2_8 : σ8.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 2]? = some (vcnt.extractLsb' 16 8) := hmem8 ▸ hcnt2_7
  have hcnt3_8 : σ8.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 3]? = some (vcnt.extractLsb' 24 8) := hmem8 ▸ hcnt3_7
  -- === 7844: lw t4,232(sp)  ⇒  x29 := sext vcnt ===
  obtain ⟨hl0, hl1, hl2, hl3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80007844 hload8
  have hx2n9 : (afterNextPC (afterPrelude σ8) (0x80007844#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ8 (0x80007844#64) _ (by decide) (by decide)]; exact hx2_8
  obtain ⟨σ9, i9, hs9s, hi9, hG9, hmem9, hobs9⟩ :=
    stepObs_alu σ8 i8 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80007844#64) vmi8 (0x0e812e83#32)
      (instruction.LOAD (0x0e8#12, regidx.Regidx 0x02#5, regidx.Regidx 0x1d#5, false, 4))
      Register.x29 (sign_extend (m := 64)
        ((((vcnt.extractLsb' 24 8).append (vcnt.extractLsb' 16 8)).append
          (vcnt.extractLsb' 8 8)).append (vcnt.extractLsb' 0 8) : BitVec (8 * 4)))
      (0x83#8) (0x2e#8) (0x81#8) (0x0e#8)
      hG8 hpc8 hmi8 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_0e812e83 (afterPrelude σ8)
        (by rw [get?_afterPrelude σ8 _ (by decide)]; exact hG8.misa)
        (by rw [get?_afterPrelude σ8 _ (by decide)]; exact hG8.cur_privilege)
        (by rw [get?_afterPrelude σ8 _ (by decide)]; exact hG8.mseccfg))
      (exec_lw σ8 (0x80007844#64) (0x0e8#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x1d#5)
        (sigma3_alu σ8 (0x80007844#64) Register.x29 (sign_extend (m := 64)
          ((((vcnt.extractLsb' 24 8).append (vcnt.extractLsb' 16 8)).append
            (vcnt.extractLsb' 8 8)).append (vcnt.extractLsb' 0 8) : BitVec (8 * 4))))
        vsp _ _ _ _ hG8 (rX_bits_x2 _ vsp hx2n9)
        (wX_bits_x29 _ _)
        (by rw [hoff232]; omega) (by rw [hoff232]; omega) (Or.inr (by rw [hoff232]; omega))
        (by rw [hoff232]; omega)
        hcnt0_8 hcnt1_8 hcnt2_8 hcnt3_8)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hl0 hl1 hl2 hl3 (by decide) (by decide) (by decide) hi8
  have hstep9 : Step ⟨σ8, i8, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ9, i9, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs9s
  have hpc9 : σ9.regs.get? Register.PC = some (0x80007848#64) := by
    have := obs_alu_pc hobs9
    rwa [show BitVec.addInt (0x80007844#64 : BitVec 64) 4 = (0x80007848#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  -- the loaded value equals `sext vcnt`
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
  have hx29_9 : σ9.regs.get? Register.x29 = some (sign_extend (m := 64) vcnt : BitVec 64) := by
    have := obs_alu_rd hobs9 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hlwval] at this
  obtain ⟨vmi9, hmi9⟩ := obs_alu_minstret hobs9
  have hx2_9 : σ9.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs9 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_8
  have hx12_9 : σ9.regs.get? Register.x12 = some vcur :=
    obs_alu_other hobs9 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_8
  have hx23_9 : σ9.regs.get? Register.x23 = some viov :=
    obs_alu_other hobs9 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_8
  have hload9 : SvfprintfSliceLoaded σ9.mem := hmem9 ▸ hload8
  have hfp9 : FlushPinsLoaded σ9.mem := by
    have : σ9.mem = σ8.mem := hmem9
    rw [this]; exact hmem8 ▸ hfp7
  -- === 7848: li s11,0  ⇒  x27 := 0 ===
  obtain ⟨hm0, hm1, hm2, hm3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80007848 hload9
  obtain ⟨σ10, i10, hs10s, hi10, hG10, hmem10, hobs10⟩ :=
    stepObs_alu σ9 i9 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80007848#64) vmi9 (0x00000d93#32)
      (instruction.ITYPE (0x000#12, regidx.Regidx 0x00#5, regidx.Regidx 0x1b#5, iop.ADDI))
      Register.x27 ((0#64) + sign_extend (m := 64) (0x000#12))
      (0x93#8) (0x0d#8) (0x00#8) (0x00#8)
      hG9 hpc9 hmi9 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_00000d93 (afterPrelude σ9)
        (by rw [get?_afterPrelude σ9 _ (by decide)]; exact hG9.misa)
        (by rw [get?_afterPrelude σ9 _ (by decide)]; exact hG9.cur_privilege)
        (by rw [get?_afterPrelude σ9 _ (by decide)]; exact hG9.mseccfg))
      (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x1b#5) (0#64)
        (afterNextPC (afterPrelude σ9) (0x80007848#64))
        (sigma3_alu σ9 (0x80007848#64) Register.x27 ((0#64) + sign_extend (m := 64) (0x000#12)))
        (rX_bits_zero _) (wX_bits_x27 _ ((0#64) + sign_extend (m := 64) (0x000#12))))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hm0 hm1 hm2 hm3 (by decide) (by decide) (by decide) hi9
  have hstep10 : Step ⟨σ9, i9, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ10, i10, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs10s
  have hpc10 : σ10.regs.get? Register.PC = some (0x8000784c#64) := by
    have := obs_alu_pc hobs10
    rwa [show BitVec.addInt (0x80007848#64 : BitVec 64) 4 = (0x8000784c#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx27_10 : σ10.regs.get? Register.x27 = some (0#64) := by
    have := obs_alu_rd hobs10 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64) + sign_extend (m := 64) (0x000#12) : BitVec 64) = (0#64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi10, hmi10⟩ := obs_alu_minstret hobs10
  have hx2_10 : σ10.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs10 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_9
  have hx12_10 : σ10.regs.get? Register.x12 = some vcur :=
    obs_alu_other hobs10 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_9
  have hx23_10 : σ10.regs.get? Register.x23 = some viov :=
    obs_alu_other hobs10 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_9
  have hx29_10 : σ10.regs.get? Register.x29 = some (sign_extend (m := 64) vcnt : BitVec 64) :=
    obs_alu_other hobs10 Register.x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx29_9
  have hload10 : SvfprintfSliceLoaded σ10.mem := hmem10 ▸ hload9
  have hfp10 : FlushPinsLoaded σ10.mem := hmem10 ▸ hfp9
  -- === 784c: addi a1,sp,167  ⇒  x11 := vsp + sext 0xa7 ===
  obtain ⟨hn0, hn1, hn2, hn3⟩ := Vsa.Sim.Code.svfprintfSlice_at_8000784c hload10
  have hx2n11 : (afterNextPC (afterPrelude σ10) (0x8000784c#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ10 (0x8000784c#64) _ (by decide) (by decide)]; exact hx2_10
  obtain ⟨σ11, i11, hs11s, hi11, hG11, hmem11, hobs11⟩ :=
    stepObs_alu σ10 i10 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x8000784c#64) vmi10 (0x0a710593#32)
      (instruction.ITYPE (0x0a7#12, regidx.Regidx 0x02#5, regidx.Regidx 0x0b#5, iop.ADDI))
      Register.x11 (vsp + sign_extend (m := 64) (0x0a7#12))
      (0x93#8) (0x05#8) (0x71#8) (0x0a#8)
      hG10 hpc10 hmi10 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_0a710593 (afterPrelude σ10)
        (by rw [get?_afterPrelude σ10 _ (by decide)]; exact hG10.misa)
        (by rw [get?_afterPrelude σ10 _ (by decide)]; exact hG10.cur_privilege)
        (by rw [get?_afterPrelude σ10 _ (by decide)]; exact hG10.mseccfg))
      (execute_itype_addi_char (0x0a7#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x0b#5) vsp
        (afterNextPC (afterPrelude σ10) (0x8000784c#64))
        (sigma3_alu σ10 (0x8000784c#64) Register.x11 (vsp + sign_extend (m := 64) (0x0a7#12)))
        (rX_bits_x2 _ vsp hx2n11) (wX_bits_x11 _ (vsp + sign_extend (m := 64) (0x0a7#12))))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hn0 hn1 hn2 hn3 (by decide) (by decide) (by decide) hi10
  have hstep11 : Step ⟨σ10, i10, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ11, i11, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs11s
  have hpc11 : σ11.regs.get? Register.PC = some (0x80007850#64) := by
    have := obs_alu_pc hobs11
    rwa [show BitVec.addInt (0x8000784c#64 : BitVec 64) 4 = (0x80007850#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx11_11 : σ11.regs.get? Register.x11 = some (vsp + sign_extend (m := 64) (0x0a7#12)) :=
    obs_alu_rd hobs11 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi11, hmi11⟩ := obs_alu_minstret hobs11
  have hx2_11 : σ11.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs11 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_10
  have hx12_11 : σ11.regs.get? Register.x12 = some vcur :=
    obs_alu_other hobs11 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_10
  have hx23_11 : σ11.regs.get? Register.x23 = some viov :=
    obs_alu_other hobs11 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_10
  have hx27_11 : σ11.regs.get? Register.x27 = some (0#64) :=
    obs_alu_other hobs11 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27_10
  have hx29_11 : σ11.regs.get? Register.x29 = some (sign_extend (m := 64) vcnt : BitVec 64) :=
    obs_alu_other hobs11 Register.x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx29_10
  have hload11 : SvfprintfSliceLoaded σ11.mem := hmem11 ▸ hload10
  have hfp11 : FlushPinsLoaded σ11.mem := hmem11 ▸ hfp10
  -- === 7850: addi a2,a2,1  ⇒  x12 := vcur + sext 1 ===
  obtain ⟨ho0, ho1, ho2, ho3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80007850 hload11
  have hx12n12 : (afterNextPC (afterPrelude σ11) (0x80007850#64)).regs.get? Register.x12 = some vcur := by
    rw [get?_afterNextPC σ11 (0x80007850#64) _ (by decide) (by decide)]; exact hx12_11
  obtain ⟨σ12, i12, hs12s, hi12, hG12, hmem12, hobs12⟩ :=
    stepObs_alu σ11 i11 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80007850#64) vmi11 (0x00160613#32)
      (instruction.ITYPE (0x001#12, regidx.Regidx 0x0c#5, regidx.Regidx 0x0c#5, iop.ADDI))
      Register.x12 (vcur + sign_extend (m := 64) (0x001#12))
      (0x13#8) (0x06#8) (0x16#8) (0x00#8)
      hG11 hpc11 hmi11 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_00160613 (afterPrelude σ11)
        (by rw [get?_afterPrelude σ11 _ (by decide)]; exact hG11.misa)
        (by rw [get?_afterPrelude σ11 _ (by decide)]; exact hG11.cur_privilege)
        (by rw [get?_afterPrelude σ11 _ (by decide)]; exact hG11.mseccfg))
      (execute_itype_addi_char (0x001#12) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0c#5) vcur
        (afterNextPC (afterPrelude σ11) (0x80007850#64))
        (sigma3_alu σ11 (0x80007850#64) Register.x12 (vcur + sign_extend (m := 64) (0x001#12)))
        (rX_bits_x12 _ vcur hx12n12) (wX_bits_x12 _ (vcur + sign_extend (m := 64) (0x001#12))))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      ho0 ho1 ho2 ho3 (by decide) (by decide) (by decide) hi11
  have hstep12 : Step ⟨σ11, i11, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ12, i12, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs12s
  have hpc12 : σ12.regs.get? Register.PC = some (0x80007854#64) := by
    have := obs_alu_pc hobs12
    rwa [show BitVec.addInt (0x80007850#64 : BitVec 64) 4 = (0x80007854#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx12_12 : σ12.regs.get? Register.x12 = some (vcur + sign_extend (m := 64) (0x001#12)) :=
    obs_alu_rd hobs12 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi12, hmi12⟩ := obs_alu_minstret hobs12
  have hx2_12 : σ12.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs12 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_11
  have hx11_12 : σ12.regs.get? Register.x11 = some (vsp + sign_extend (m := 64) (0x0a7#12)) :=
    obs_alu_other hobs12 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_11
  have hx23_12 : σ12.regs.get? Register.x23 = some viov :=
    obs_alu_other hobs12 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_11
  have hx27_12 : σ12.regs.get? Register.x27 = some (0#64) :=
    obs_alu_other hobs12 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27_11
  have hx29_12 : σ12.regs.get? Register.x29 = some (sign_extend (m := 64) vcnt : BitVec 64) :=
    obs_alu_other hobs12 Register.x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx29_11
  have hload12 : SvfprintfSliceLoaded σ12.mem := hmem12 ▸ hload11
  have hfp12 : FlushPinsLoaded σ12.mem := hmem12 ▸ hfp11
  -- === 7854: addiw t4,t4,1  ⇒  x29 := sext(extractLsb (sext vcnt + sext 1) 31 0) ===
  obtain ⟨hp0, hp1, hp2, hp3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80007854 hload12
  have hx29n13 : (afterNextPC (afterPrelude σ12) (0x80007854#64)).regs.get? Register.x29
      = some (sign_extend (m := 64) vcnt : BitVec 64) := by
    rw [get?_afterNextPC σ12 (0x80007854#64) _ (by decide) (by decide)]; exact hx29_12
  obtain ⟨σ13, i13, hs13s, hi13, hG13, hmem13, hobs13⟩ :=
    stepObs_alu σ12 i12 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80007854#64) vmi12 (0x001e8e9b#32)
      (instruction.ADDIW (0x001#12, regidx.Regidx 0x1d#5, regidx.Regidx 0x1d#5))
      Register.x29 (sign_extend (m := 64)
        (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0))
      (0x9b#8) (0x8e#8) (0x1e#8) (0x00#8)
      hG12 hpc12 hmi12 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_001e8e9b (afterPrelude σ12)
        (by rw [get?_afterPrelude σ12 _ (by decide)]; exact hG12.misa)
        (by rw [get?_afterPrelude σ12 _ (by decide)]; exact hG12.cur_privilege)
        (by rw [get?_afterPrelude σ12 _ (by decide)]; exact hG12.mseccfg))
      (execute_addiw_char (0x001#12) (regidx.Regidx 0x1d#5) (regidx.Regidx 0x1d#5)
        (sign_extend (m := 64) vcnt : BitVec 64)
        (afterNextPC (afterPrelude σ12) (0x80007854#64))
        (sigma3_alu σ12 (0x80007854#64) Register.x29 (sign_extend (m := 64)
          (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0)))
        (rX_bits_x29 _ (sign_extend (m := 64) vcnt : BitVec 64) hx29n13)
        (wX_bits_x29 _ (sign_extend (m := 64)
          (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0))))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hp0 hp1 hp2 hp3 (by decide) (by decide) (by decide) hi12
  have hstep13 : Step ⟨σ12, i12, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ13, i13, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs13s
  have hpc13 : σ13.regs.get? Register.PC = some (0x80007858#64) := by
    have := obs_alu_pc hobs13
    rwa [show BitVec.addInt (0x80007854#64 : BitVec 64) 4 = (0x80007858#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx29_13 : σ13.regs.get? Register.x29 = some (sign_extend (m := 64)
      (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0)) :=
    obs_alu_rd hobs13 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi13, hmi13⟩ := obs_alu_minstret hobs13
  have hx2_13 : σ13.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs13 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_12
  have hx11_13 : σ13.regs.get? Register.x11 = some (vsp + sign_extend (m := 64) (0x0a7#12)) :=
    obs_alu_other hobs13 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_12
  have hx12_13 : σ13.regs.get? Register.x12 = some (vcur + sign_extend (m := 64) (0x001#12)) :=
    obs_alu_other hobs13 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_12
  have hx23_13 : σ13.regs.get? Register.x23 = some viov :=
    obs_alu_other hobs13 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_12
  have hx27_13 : σ13.regs.get? Register.x27 = some (0#64) :=
    obs_alu_other hobs13 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27_12
  have hload13 : SvfprintfSliceLoaded σ13.mem := hmem13 ▸ hload12
  have hfp13 : FlushPinsLoaded σ13.mem := hmem13 ▸ hfp12
  -- === 7858: li a5,1  ⇒  x15 := 1 ===
  obtain ⟨hq0, hq1, hq2, hq3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80007858 hload13
  obtain ⟨σ14, i14, hs14s, hi14, hG14, hmem14, hobs14⟩ :=
    stepObs_alu σ13 i13 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80007858#64) vmi13 (0x00100793#32)
      (instruction.ITYPE (0x001#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0f#5, iop.ADDI))
      Register.x15 ((0#64) + sign_extend (m := 64) (0x001#12))
      (0x93#8) (0x07#8) (0x10#8) (0x00#8)
      hG13 hpc13 hmi13 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_00100793 (afterPrelude σ13)
        (by rw [get?_afterPrelude σ13 _ (by decide)]; exact hG13.misa)
        (by rw [get?_afterPrelude σ13 _ (by decide)]; exact hG13.cur_privilege)
        (by rw [get?_afterPrelude σ13 _ (by decide)]; exact hG13.mseccfg))
      (execute_itype_addi_char (0x001#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0f#5) (0#64)
        (afterNextPC (afterPrelude σ13) (0x80007858#64))
        (sigma3_alu σ13 (0x80007858#64) Register.x15 ((0#64) + sign_extend (m := 64) (0x001#12)))
        (rX_bits_zero _) (wX_bits_x15 _ ((0#64) + sign_extend (m := 64) (0x001#12))))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hq0 hq1 hq2 hq3 (by decide) (by decide) (by decide) hi13
  have hstep14 : Step ⟨σ13, i13, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ14, i14, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs14s
  have hpc14 : σ14.regs.get? Register.PC = some (0x8000785c#64) := by
    have := obs_alu_pc hobs14
    rwa [show BitVec.addInt (0x80007858#64 : BitVec 64) 4 = (0x8000785c#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx15_14 : σ14.regs.get? Register.x15 = some (0x1#64) := by
    have := obs_alu_rd hobs14 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64) + sign_extend (m := 64) (0x001#12) : BitVec 64) = (0x1#64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi14, hmi14⟩ := obs_alu_minstret hobs14
  have hx2_14 : σ14.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs14 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_13
  have hx11_14 : σ14.regs.get? Register.x11 = some (vsp + sign_extend (m := 64) (0x0a7#12)) :=
    obs_alu_other hobs14 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_13
  have hx12_14 : σ14.regs.get? Register.x12 = some (vcur + sign_extend (m := 64) (0x001#12)) :=
    obs_alu_other hobs14 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_13
  have hx23_14 : σ14.regs.get? Register.x23 = some viov :=
    obs_alu_other hobs14 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_13
  have hx27_14 : σ14.regs.get? Register.x27 = some (0#64) :=
    obs_alu_other hobs14 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27_13
  have hx29_14 : σ14.regs.get? Register.x29 = some (sign_extend (m := 64)
      (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0)) :=
    obs_alu_other hobs14 Register.x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx29_13
  have hload14 : SvfprintfSliceLoaded σ14.mem := hmem14 ▸ hload13
  have hfp14 : FlushPinsLoaded σ14.mem := hmem14 ▸ hfp13
  -- abbreviations for the store data
  have hmemeq14 : σ14.mem = c.σ.mem := by
    rw [hmem14, hmem13, hmem12, hmem11, hmem10, hmem9, hmem8, hmem7, hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]
  -- iov-buffer effective-address facts
  have hiovlt : viov.toNat < 2 ^ 64 := viov.isLt
  -- === 785c: sd a1,0(s7)  ⇒  mem[viov] := (vsp+167) ===
  obtain ⟨hr0, hr1, hr2, hr3⟩ := Vsa.Sim.Code.svfprintfSlice_at_8000785c hload14
  have hx23n15 : (afterNextPC (afterPrelude σ14) (0x8000785c#64)).regs.get? Register.x23 = some viov := by
    rw [get?_afterNextPC σ14 (0x8000785c#64) _ (by decide) (by decide)]; exact hx23_14
  have hx11n15 : (afterNextPC (afterPrelude σ14) (0x8000785c#64)).regs.get? Register.x11
      = some (vsp + sign_extend (m := 64) (0x0a7#12)) := by
    rw [get?_afterNextPC σ14 (0x8000785c#64) _ (by decide) (by decide)]; exact hx11_14
  obtain ⟨σ15, i15, hs15s, hi15, hG15, hmem15, hobs15⟩ :=
    stepObs_store σ14 i14 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x8000785c#64) vmi14 (0x00bbb023#32)
      (instruction.STORE (0x000#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x17#5, 8))
      (writeMap8 (afterNextPC (afterPrelude σ14) (0x8000785c#64)).mem
        (viov + sign_extend (m := 64) (0x000#12)).toNat (sdData_val (vsp + sign_extend (m := 64) (0x0a7#12))))
      (0x23#8) (0xb0#8) (0xbb#8) (0x00#8)
      hG14 hpc14 hmi14 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_00bbb023 (afterPrelude σ14)
        (by rw [get?_afterPrelude σ14 _ (by decide)]; exact hG14.misa)
        (by rw [get?_afterPrelude σ14 _ (by decide)]; exact hG14.cur_privilege)
        (by rw [get?_afterPrelude σ14 _ (by decide)]; exact hG14.mseccfg))
      (exec_sd_val σ14 (0x8000785c#64) (0x000#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x17#5)
        viov (vsp + sign_extend (m := 64) (0x0a7#12)) hG14 (rX_bits_x23 _ viov hx23n15)
        (rX_bits_x11 _ (vsp + sign_extend (m := 64) (0x0a7#12)) hx11n15)
        (by rw [hoffiov0]; omega) (by rw [hoffiov0]; omega) (by rw [hoffiov0]; omega) (by rw [hoffiov0]; omega))
      hr0 hr1 hr2 hr3 (by decide) (by decide) (by decide) hi14
  have hstep15 : Step ⟨σ14, i14, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ15, i15, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs15s
  have hpc15 : σ15.regs.get? Register.PC = some (0x80007860#64) := by
    have := obs_store_pc_sn4 hobs15
    rwa [show BitVec.addInt (0x8000785c#64 : BitVec 64) 4 = (0x80007860#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi15, hmi15⟩ := obs_store_minstret_sn4 hobs15
  have hx2_15 : σ15.regs.get? Register.x2 = some vsp :=
    obs_store_other_sn4 Register.x2 hobs15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_14
  have hx12_15 : σ15.regs.get? Register.x12 = some (vcur + sign_extend (m := 64) (0x001#12)) :=
    obs_store_other_sn4 Register.x12 hobs15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_14
  have hx15_15 : σ15.regs.get? Register.x15 = some (0x1#64) :=
    obs_store_other_sn4 Register.x15 hobs15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_14
  have hx23_15 : σ15.regs.get? Register.x23 = some viov :=
    obs_store_other_sn4 Register.x23 hobs15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_14
  have hx27_15 : σ15.regs.get? Register.x27 = some (0#64) :=
    obs_store_other_sn4 Register.x27 hobs15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27_14
  have hx29_15 : σ15.regs.get? Register.x29 = some (sign_extend (m := 64)
      (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0)) :=
    obs_store_other_sn4 Register.x29 hobs15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx29_14
  have hNP15 : (afterNextPC (afterPrelude σ14) (0x8000785c#64)).mem = σ14.mem := rfl
  have hmem15' : σ15.mem = writeMap8 σ14.mem viov.toNat
      (sdData_val (vsp + sign_extend (m := 64) (0x0a7#12))) := by
    rw [hmem15, hNP15, hoffiov0]
  have hload15 : SvfprintfSliceLoaded σ15.mem := by
    rw [hmem15']; exact svfprintfSlice_writeMap8_sn5 _ _ _ (by omega) hload14
  -- === 7860: sd a5,8(s7)  ⇒  mem[viov+8] := 1 ===
  obtain ⟨hs0, hs1, hs2, hs3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80007860 hload15
  have hx23n16 : (afterNextPC (afterPrelude σ15) (0x80007860#64)).regs.get? Register.x23 = some viov := by
    rw [get?_afterNextPC σ15 (0x80007860#64) _ (by decide) (by decide)]; exact hx23_15
  have hx15n16 : (afterNextPC (afterPrelude σ15) (0x80007860#64)).regs.get? Register.x15 = some (0x1#64) := by
    rw [get?_afterNextPC σ15 (0x80007860#64) _ (by decide) (by decide)]; exact hx15_15
  obtain ⟨σ16, i16, hs16s, hi16, hG16, hmem16, hobs16⟩ :=
    stepObs_store σ15 i15 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80007860#64) vmi15 (0x00fbb423#32)
      (instruction.STORE (0x008#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x17#5, 8))
      (writeMap8 (afterNextPC (afterPrelude σ15) (0x80007860#64)).mem
        (viov + sign_extend (m := 64) (0x008#12)).toNat (sdData_val (0x1#64)))
      (0x23#8) (0xb4#8) (0xfb#8) (0x00#8)
      hG15 hpc15 hmi15 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_00fbb423 (afterPrelude σ15)
        (by rw [get?_afterPrelude σ15 _ (by decide)]; exact hG15.misa)
        (by rw [get?_afterPrelude σ15 _ (by decide)]; exact hG15.cur_privilege)
        (by rw [get?_afterPrelude σ15 _ (by decide)]; exact hG15.mseccfg))
      (exec_sd_val σ15 (0x80007860#64) (0x008#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x17#5)
        viov (0x1#64) hG15 (rX_bits_x23 _ viov hx23n16) (rX_bits_x15 _ (0x1#64) hx15n16)
        (by rw [hoffiov8]; omega) (by rw [hoffiov8]; omega) (by rw [hoffiov8]; omega) (by rw [hoffiov8]; omega))
      hs0 hs1 hs2 hs3 (by decide) (by decide) (by decide) hi15
  have hstep16 : Step ⟨σ15, i15, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ16, i16, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs16s
  have hpc16 : σ16.regs.get? Register.PC = some (0x80007864#64) := by
    have := obs_store_pc_sn4 hobs16
    rwa [show BitVec.addInt (0x80007860#64 : BitVec 64) 4 = (0x80007864#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi16, hmi16⟩ := obs_store_minstret_sn4 hobs16
  have hx2_16 : σ16.regs.get? Register.x2 = some vsp :=
    obs_store_other_sn4 Register.x2 hobs16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_15
  have hx12_16 : σ16.regs.get? Register.x12 = some (vcur + sign_extend (m := 64) (0x001#12)) :=
    obs_store_other_sn4 Register.x12 hobs16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_15
  have hx23_16 : σ16.regs.get? Register.x23 = some viov :=
    obs_store_other_sn4 Register.x23 hobs16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_15
  have hx27_16 : σ16.regs.get? Register.x27 = some (0#64) :=
    obs_store_other_sn4 Register.x27 hobs16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27_15
  have hx29_16 : σ16.regs.get? Register.x29 = some (sign_extend (m := 64)
      (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0)) :=
    obs_store_other_sn4 Register.x29 hobs16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx29_15
  have hNP16 : (afterNextPC (afterPrelude σ15) (0x80007860#64)).mem = σ15.mem := rfl
  have hmem16' : σ16.mem = writeMap8 σ15.mem (viov + sign_extend (m := 64) (0x008#12)).toNat
      (sdData_val (0x1#64)) := by rw [hmem16, hNP16]
  have hload16 : SvfprintfSliceLoaded σ16.mem := by
    rw [hmem16']; exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoffiov8]; omega) hload15
  -- === 7864: sd a2,240(sp)  ⇒  mem[sp+240] := vcur+1 ===
  obtain ⟨ht0, ht1, ht2, ht3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80007864 hload16
  have hx2n17 : (afterNextPC (afterPrelude σ16) (0x80007864#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ16 (0x80007864#64) _ (by decide) (by decide)]; exact hx2_16
  have hx12n17 : (afterNextPC (afterPrelude σ16) (0x80007864#64)).regs.get? Register.x12
      = some (vcur + sign_extend (m := 64) (0x001#12)) := by
    rw [get?_afterNextPC σ16 (0x80007864#64) _ (by decide) (by decide)]; exact hx12_16
  obtain ⟨σ17, i17, hs17s, hi17, hG17, hmem17, hobs17⟩ :=
    stepObs_store σ16 i16 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80007864#64) vmi16 (0x0ec13823#32)
      (instruction.STORE (0x0f0#12, regidx.Regidx 0x0c#5, regidx.Regidx 0x02#5, 8))
      (writeMap8 (afterNextPC (afterPrelude σ16) (0x80007864#64)).mem
        (vsp + sign_extend (m := 64) (0x0f0#12)).toNat (sdData_val (vcur + sign_extend (m := 64) (0x001#12))))
      (0x23#8) (0x38#8) (0xc1#8) (0x0e#8)
      hG16 hpc16 hmi16 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_0ec13823 (afterPrelude σ16)
        (by rw [get?_afterPrelude σ16 _ (by decide)]; exact hG16.misa)
        (by rw [get?_afterPrelude σ16 _ (by decide)]; exact hG16.cur_privilege)
        (by rw [get?_afterPrelude σ16 _ (by decide)]; exact hG16.mseccfg))
      (exec_sd_val σ16 (0x80007864#64) (0x0f0#12) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x02#5)
        vsp (vcur + sign_extend (m := 64) (0x001#12)) hG16 (rX_bits_x2 _ vsp hx2n17)
        (rX_bits_x12 _ (vcur + sign_extend (m := 64) (0x001#12)) hx12n17)
        (by rw [hoff240]; omega) (by rw [hoff240]; omega) (by rw [hoff240]; omega) (by rw [hoff240]; omega))
      ht0 ht1 ht2 ht3 (by decide) (by decide) (by decide) hi16
  have hstep17 : Step ⟨σ16, i16, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ17, i17, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs17s
  have hpc17 : σ17.regs.get? Register.PC = some (0x80007868#64) := by
    have := obs_store_pc_sn4 hobs17
    rwa [show BitVec.addInt (0x80007864#64 : BitVec 64) 4 = (0x80007868#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi17, hmi17⟩ := obs_store_minstret_sn4 hobs17
  have hx2_17 : σ17.regs.get? Register.x2 = some vsp :=
    obs_store_other_sn4 Register.x2 hobs17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_16
  have hx23_17 : σ17.regs.get? Register.x23 = some viov :=
    obs_store_other_sn4 Register.x23 hobs17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_16
  have hx27_17 : σ17.regs.get? Register.x27 = some (0#64) :=
    obs_store_other_sn4 Register.x27 hobs17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27_16
  have hx29_17 : σ17.regs.get? Register.x29 = some (sign_extend (m := 64)
      (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0)) :=
    obs_store_other_sn4 Register.x29 hobs17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx29_16
  have hNP17 : (afterNextPC (afterPrelude σ16) (0x80007864#64)).mem = σ16.mem := rfl
  have hmem17' : σ17.mem = writeMap8 σ16.mem (vsp + sign_extend (m := 64) (0x0f0#12)).toNat
      (sdData_val (vcur + sign_extend (m := 64) (0x001#12))) := by rw [hmem17, hNP17]
  have hload17 : SvfprintfSliceLoaded σ17.mem := by
    rw [hmem17']; exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff240]; omega) hload16
  -- === 7868: sw t4,232(sp)  ⇒  mem[sp+232] := swData x29 (4-byte) ===
  obtain ⟨hu0, hu1, hu2, hu3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80007868 hload17
  have hx2n18 : (afterNextPC (afterPrelude σ17) (0x80007868#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ17 (0x80007868#64) _ (by decide) (by decide)]; exact hx2_17
  have hx29n18 : (afterNextPC (afterPrelude σ17) (0x80007868#64)).regs.get? Register.x29
      = some (sign_extend (m := 64)
        (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0)) := by
    rw [get?_afterNextPC σ17 (0x80007868#64) _ (by decide) (by decide)]; exact hx29_17
  obtain ⟨σ18, i18, hs18s, hi18, hG18, hmem18, hobs18⟩ :=
    stepObs_store σ17 i17 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80007868#64) vmi17 (0x0fd12423#32)
      (instruction.STORE (0x0e8#12, regidx.Regidx 0x1d#5, regidx.Regidx 0x02#5, 4))
      (writeMap4 (afterNextPC (afterPrelude σ17) (0x80007868#64)).mem
        (vsp + sign_extend (m := 64) (0x0e8#12)).toNat (swData (sign_extend (m := 64)
          (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0))))
      (0x23#8) (0x24#8) (0xd1#8) (0x0f#8)
      hG17 hpc17 hmi17 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_0fd12423 (afterPrelude σ17)
        (by rw [get?_afterPrelude σ17 _ (by decide)]; exact hG17.misa)
        (by rw [get?_afterPrelude σ17 _ (by decide)]; exact hG17.cur_privilege)
        (by rw [get?_afterPrelude σ17 _ (by decide)]; exact hG17.mseccfg))
      (exec_sw σ17 (0x80007868#64) (0x0e8#12) (regidx.Regidx 0x1d#5) (regidx.Regidx 0x02#5)
        vsp (sign_extend (m := 64)
          (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0))
        hG17 (rX_bits_x2 _ vsp hx2n18) (rX_bits_x29 _ _ hx29n18)
        (by rw [hoff232]; omega) (by rw [hoff232]; omega) (by rw [hoff232]; omega) (by rw [hoff232]; omega))
      hu0 hu1 hu2 hu3 (by decide) (by decide) (by decide) hi17
  have hstep18 : Step ⟨σ17, i17, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ18, i18, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs18s
  have hpc18 : σ18.regs.get? Register.PC = some (0x8000786c#64) := by
    have := obs_store_pc_sn4 hobs18
    rwa [show BitVec.addInt (0x80007868#64 : BitVec 64) 4 = (0x8000786c#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi18, hmi18⟩ := obs_store_minstret_sn4 hobs18
  have hx2_18 : σ18.regs.get? Register.x2 = some vsp :=
    obs_store_other_sn4 Register.x2 hobs18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_17
  have hx23_18 : σ18.regs.get? Register.x23 = some viov :=
    obs_store_other_sn4 Register.x23 hobs18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_17
  have hx27_18 : σ18.regs.get? Register.x27 = some (0#64) :=
    obs_store_other_sn4 Register.x27 hobs18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27_17
  have hx29_18 : σ18.regs.get? Register.x29 = some (sign_extend (m := 64)
      (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0)) :=
    obs_store_other_sn4 Register.x29 hobs18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx29_17
  have hNP18 : (afterNextPC (afterPrelude σ17) (0x80007868#64)).mem = σ17.mem := rfl
  have hmem18' : σ18.mem = writeMap4 σ17.mem (vsp + sign_extend (m := 64) (0x0e8#12)).toNat
      (swData (sign_extend (m := 64)
        (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0))) := by
    rw [hmem18, hNP18]
  have hload18 : SvfprintfSliceLoaded σ18.mem := by
    rw [hmem18']; exact svfprintfSlice_writeMap4_pe _ _ _ (by rw [hoff232]; omega) hload17
  -- === 786c: li a1,7  ⇒  x11 := 7 ===
  obtain ⟨hv0, hv1, hv2, hv3⟩ := Vsa.Sim.Code.svfprintfSlice_at_8000786c hload18
  obtain ⟨σ19, i19, hs19s, hi19, hG19, hmem19, hobs19⟩ :=
    stepObs_alu σ18 i18 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x8000786c#64) vmi18 (0x00700593#32)
      (instruction.ITYPE (0x007#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0b#5, iop.ADDI))
      Register.x11 ((0#64) + sign_extend (m := 64) (0x007#12))
      (0x93#8) (0x05#8) (0x70#8) (0x00#8)
      hG18 hpc18 hmi18 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_00700593 (afterPrelude σ18)
        (by rw [get?_afterPrelude σ18 _ (by decide)]; exact hG18.misa)
        (by rw [get?_afterPrelude σ18 _ (by decide)]; exact hG18.cur_privilege)
        (by rw [get?_afterPrelude σ18 _ (by decide)]; exact hG18.mseccfg))
      (execute_itype_addi_char (0x007#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0b#5) (0#64)
        (afterNextPC (afterPrelude σ18) (0x8000786c#64))
        (sigma3_alu σ18 (0x8000786c#64) Register.x11 ((0#64) + sign_extend (m := 64) (0x007#12)))
        (rX_bits_zero _) (wX_bits_x11 _ ((0#64) + sign_extend (m := 64) (0x007#12))))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hv0 hv1 hv2 hv3 (by decide) (by decide) (by decide) hi18
  have hstep19 : Step ⟨σ18, i18, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ19, i19, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs19s
  have hpc19 : σ19.regs.get? Register.PC = some (0x80007870#64) := by
    have := obs_alu_pc hobs19
    rwa [show BitVec.addInt (0x8000786c#64 : BitVec 64) 4 = (0x80007870#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx11_19 : σ19.regs.get? Register.x11 = some (0x7#64) := by
    have := obs_alu_rd hobs19 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64) + sign_extend (m := 64) (0x007#12) : BitVec 64) = (0x7#64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi19, hmi19⟩ := obs_alu_minstret hobs19
  have hx2_19 : σ19.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs19 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_18
  have hx23_19 : σ19.regs.get? Register.x23 = some viov :=
    obs_alu_other hobs19 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_18
  have hx27_19 : σ19.regs.get? Register.x27 = some (0#64) :=
    obs_alu_other hobs19 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27_18
  have hx29_19 : σ19.regs.get? Register.x29 = some (sign_extend (m := 64)
      (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0)) :=
    obs_alu_other hobs19 Register.x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx29_18
  have hmem19eq : σ19.mem = σ18.mem := hmem19
  -- === 7870: addi s7,s7,16  ⇒  x23 := viov + 16 ===
  obtain ⟨hw0, hw1, hw2, hw3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80007870 (hmem19eq ▸ hload18)
  have hx23n20 : (afterNextPC (afterPrelude σ19) (0x80007870#64)).regs.get? Register.x23 = some viov := by
    rw [get?_afterNextPC σ19 (0x80007870#64) _ (by decide) (by decide)]; exact hx23_19
  obtain ⟨σ20, i20, hs20s, hi20, hG20, hmem20, hobs20⟩ :=
    stepObs_alu σ19 i19 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80007870#64) vmi19 (0x010b8b93#32)
      (instruction.ITYPE (0x010#12, regidx.Regidx 0x17#5, regidx.Regidx 0x17#5, iop.ADDI))
      Register.x23 (viov + sign_extend (m := 64) (0x010#12))
      (0x93#8) (0x8b#8) (0x0b#8) (0x01#8)
      hG19 hpc19 hmi19 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_010b8b93 (afterPrelude σ19)
        (by rw [get?_afterPrelude σ19 _ (by decide)]; exact hG19.misa)
        (by rw [get?_afterPrelude σ19 _ (by decide)]; exact hG19.cur_privilege)
        (by rw [get?_afterPrelude σ19 _ (by decide)]; exact hG19.mseccfg))
      (execute_itype_addi_char (0x010#12) (regidx.Regidx 0x17#5) (regidx.Regidx 0x17#5) viov
        (afterNextPC (afterPrelude σ19) (0x80007870#64))
        (sigma3_alu σ19 (0x80007870#64) Register.x23 (viov + sign_extend (m := 64) (0x010#12)))
        (rX_bits_x23 _ viov hx23n20) (wX_bits_x23 _ (viov + sign_extend (m := 64) (0x010#12))))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hw0 hw1 hw2 hw3 (by decide) (by decide) (by decide) hi19
  have hstep20 : Step ⟨σ19, i19, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ20, i20, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs20s
  have hpc20 : σ20.regs.get? Register.PC = some (0x80007874#64) := by
    have := obs_alu_pc hobs20
    rwa [show BitVec.addInt (0x80007870#64 : BitVec 64) 4 = (0x80007874#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx23_20 : σ20.regs.get? Register.x23 = some (viov + sign_extend (m := 64) (0x010#12)) :=
    obs_alu_rd hobs20 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi20, hmi20⟩ := obs_alu_minstret hobs20
  have hx2_20 : σ20.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs20 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_19
  have hx11_20 : σ20.regs.get? Register.x11 = some (0x7#64) :=
    obs_alu_other hobs20 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_19
  have hx27_20 : σ20.regs.get? Register.x27 = some (0#64) :=
    obs_alu_other hobs20 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27_19
  have hx29_20 : σ20.regs.get? Register.x29 = some (sign_extend (m := 64)
      (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0)) :=
    obs_alu_other hobs20 Register.x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx29_19
  have hload20 : SvfprintfSliceLoaded σ20.mem := hmem20 ▸ (hmem19eq ▸ hload18)
  -- === 7874: blt a1,t4,7b00  (NOT taken: hcntlt, 7 < iovcnt+1 fails) ===
  obtain ⟨hy0, hy1, hy2, hy3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80007874 hload20
  have hx11n21 : (rX_bits (regidx.Regidx 0x0b#5)).run (afterNextPC (afterPrelude σ20) (0x80007874#64))
      = .ok (0x7#64) (afterNextPC (afterPrelude σ20) (0x80007874#64)) := by
    apply rX_bits_x11
    rw [get?_afterNextPC σ20 (0x80007874#64) _ (by decide) (by decide)]; exact hx11_20
  have hx29n21 : (rX_bits (regidx.Regidx 0x1d#5)).run (afterNextPC (afterPrelude σ20) (0x80007874#64))
      = .ok (sign_extend (m := 64)
        (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0))
        (afterNextPC (afterPrelude σ20) (0x80007874#64)) := by
    apply rX_bits_x29
    rw [get?_afterNextPC σ20 (0x80007874#64) _ (by decide) (by decide)]; exact hx29_20
  obtain ⟨σ21, i21, hs21s, hi21, hG21, hmem21, hobs21⟩ :=
    stepObs_branch_nottaken σ20 i20 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80007874#64) vmi20
      (0x028c#13) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x1d#5) bop.BLT (0x29d5c663#32)
      (0x63#8) (0xc6#8) (0xd5#8) (0x29#8)
      hG20 hpc20 hmi20 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_29d5c663 (afterPrelude σ20)
        (by rw [get?_afterPrelude σ20 _ (by decide)]; exact hG20.misa)
        (by rw [get?_afterPrelude σ20 _ (by decide)]; exact hG20.cur_privilege)
        (by rw [get?_afterPrelude σ20 _ (by decide)]; exact hG20.mseccfg))
      (execute_btype_blt_nottaken (0x028c#13) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x1d#5)
        (0x7#64) (sign_extend (m := 64)
          (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0))
        (afterNextPC (afterPrelude σ20) (0x80007874#64)) hx11n21 hx29n21 hcntlt)
      hy0 hy1 hy2 hy3 (by decide) (by decide) (by decide) hi20
  have hstep21 : Step ⟨σ20, i20, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ21, i21, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs21s
  have hpc21 : σ21.regs.get? Register.PC = some (0x80007878#64) := by
    have := obs_branch_nottaken_pc hobs21
    rwa [show BitVec.addInt (0x80007874#64 : BitVec 64) 4 = (0x80007878#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi21, hmi21⟩ := obs_branch_nottaken_minstret hobs21
  have hx2_21 : σ21.regs.get? Register.x2 = some vsp :=
    obs_branch_nottaken_other hobs21 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_20
  have hx23_21 : σ21.regs.get? Register.x23 = some (viov + sign_extend (m := 64) (0x010#12)) :=
    obs_branch_nottaken_other hobs21 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_20
  have hx27_21 : σ21.regs.get? Register.x27 = some (0#64) :=
    obs_branch_nottaken_other hobs21 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx27_20
  have hload21 : SvfprintfSliceLoaded σ21.mem := hmem21 ▸ hload20
  -- === 7878: beq s11,zero,78ac  (taken: x27 = 0) ===
  obtain ⟨hz0, hz1, hz2, hz3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80007878 hload21
  have hx27n22 : (rX_bits (regidx.Regidx 0x1b#5)).run (afterNextPC (afterPrelude σ21) (0x80007878#64))
      = .ok (0#64) (afterNextPC (afterPrelude σ21) (0x80007878#64)) := by
    apply rX_bits_x27
    rw [get?_afterNextPC σ21 (0x80007878#64) _ (by decide) (by decide)]; exact hx27_21
  obtain ⟨σ22, i22, hs22s, hi22, hG22, hmem22, hobs22⟩ :=
    stepObs_branch_taken σ21 i21 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80007878#64) vmi21
      (0x0034#13) (regidx.Regidx 0x1b#5) (regidx.Regidx 0x00#5) bop.BEQ (0x020d8a63#32)
      (0x63#8) (0x8a#8) (0x0d#8) (0x02#8)
      hG21 hpc21 hmi21 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_020d8a63 (afterPrelude σ21)
        (by rw [get?_afterPrelude σ21 _ (by decide)]; exact hG21.misa)
        (by rw [get?_afterPrelude σ21 _ (by decide)]; exact hG21.cur_privilege)
        (by rw [get?_afterPrelude σ21 _ (by decide)]; exact hG21.mseccfg))
      (execute_btype_beq_taken (0x0034#13) (regidx.Regidx 0x1b#5) (regidx.Regidx 0x00#5)
        (0#64) (0#64) (0x80007878#64) initMisa (afterNextPC (afterPrelude σ21) (0x80007878#64))
        hx27n22 (rX_bits_zero _)
        (by rw [get?_afterNextPC σ21 (0x80007878#64) _ (by decide) (by decide)]; exact hpc21)
        (by rw [get?_afterNextPC σ21 (0x80007878#64) _ (by decide) (by decide)]; exact hG21.misa)
        (by decide) (by decide))
      hz0 hz1 hz2 hz3 (by decide) (by decide) (by decide) hi21
  have hstep22 : Step ⟨σ21, i21, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ22, i22, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs22s
  have hpc22 : σ22.regs.get? Register.PC = some (0x800078ac#64) := by
    have := obs_branch_taken_pc hobs22
    rwa [show ((0x80007878#64 : BitVec 64) + sign_extend (m := 64) (0x0034#13))
      = (0x800078ac#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hx2_22 : σ22.regs.get? Register.x2 = some vsp :=
    obs_branch_taken_other hobs22 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_21
  have hx23_22 : σ22.regs.get? Register.x23 = some (viov + sign_extend (m := 64) (0x010#12)) :=
    obs_branch_taken_other hobs22 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_21
  have hG22' : GoodState σ22 := hG22
  have hmem22eq : σ22.mem = σ21.mem := hmem22
  -- === assemble final memory equation and the Steps chain ===
  have hmemfinal : σ22.mem = writeMap4
      (writeMap8
        (writeMap8
          (writeMap8 c.σ.mem
            viov.toNat (sdData_val (vsp + sign_extend (m := 64) (0x0a7#12))))
          (viov + sign_extend (m := 64) (0x008#12)).toNat (sdData_val (0x1#64)))
        (vsp + sign_extend (m := 64) (0x0f0#12)).toNat
          (sdData_val (vcur + sign_extend (m := 64) (0x001#12))))
      (vsp + sign_extend (m := 64) (0x0e8#12)).toNat
        (swData (sign_extend (m := 64)
          (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64)
            + sign_extend (m := 64) (0x001#12)) 31 0))) := by
    rw [hmem22eq, hmem21, hmem20, hmem19eq, hmem18', hmem17', hmem16', hmem15', hmemeq14]
  refine ⟨⟨σ22, i22, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩,
    ?_, hG22', hpc22, hx23_22, hx2_22, hmemfinal, ?_, hG22'.minstret⟩
  · exact (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans
      ((Steps.single hstep4).trans ((Steps.single hstep5).trans ((Steps.single hstep6).trans
      ((Steps.single hstep7).trans ((Steps.single hstep8).trans ((Steps.single hstep9).trans
      ((Steps.single hstep10).trans ((Steps.single hstep11).trans ((Steps.single hstep12).trans
      ((Steps.single hstep13).trans ((Steps.single hstep14).trans ((Steps.single hstep15).trans
      ((Steps.single hstep16).trans ((Steps.single hstep17).trans ((Steps.single hstep18).trans
      ((Steps.single hstep19).trans ((Steps.single hstep20).trans ((Steps.single hstep21).trans
      (Steps.single hstep22)))))))))))))))))))))
  · exact hi22

end Vsa.Sim
