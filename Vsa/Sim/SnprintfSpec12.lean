import Vsa.Sim.SnprintfSpec11
import Vsa.Sim.DecodeTable.Batch16Part26
import Vsa.Sim.DecodeTable.Batch13Part21
import Vsa.Sim.DecodeTable.Batch09Part07
import Vsa.Sim.DecodeTable.Batch08Part09
import Vsa.Sim.DecodeTable.Batch04Part29
import Vsa.Sim.DecodeTable.Batch02Part30
import Vsa.Sim.DecodeTable.Batch01Part31
import Vsa.Sim.DecodeTable.Batch01Part09
import Vsa.Sim.DecodeTable.Batch01Part02
import Vsa.Sim.DecodeTable.Batch01Part01

/-!
# M3 Layer-3 — `SnprintfSpec12` : `%`-format parse-init (width/flags reset) (`_pi`)

The single upstream `svfprintf` fact that all remaining `snprintf("%lld", …)`
residuals funnel through: the **parse-init block** that (immediately after the
`'%'` conversion-spec introducer is found) resets the field-width accumulator
`x20` and the flags word `x6` to their "nothing specified" defaults.

## Executed footprint `[0x8000776c, 0x80007798)` (11 instructions, straight-line)

```
  776c: addi x15,x22,1      x15 := fmt+1          (fmt-pointer past '%')
  7770: lbu  x24,1(x22)     x24 := format[1]      (the char after '%')
  7774: sb   x0,167(sp)     mem[sp+167] := 0      (sign-byte slot cleared)
  7778: sd   x15,0(sp)      mem[sp+0]   := fmt+1  (spilled fmt cursor)
  777c: addi x20,x0,-1      x20 := -1             ← WIDTH accumulator = "unset"
  7780: addi x6,x0,0        x6  := 0              ← FLAGS word = 0 (no flags)
  7784: addi x26,x0,90      x26 := 90  ('Z')      (dispatch upper bound)
  7788: auipc x22,0x13000                          jump-table base hi
  778c: addi x22,x22,-1676  x22 := 0x8001a0fc     (conv-char jump-table base)
  7790: addi x27,x0,0       x27 := 0
  7794: addi x25,x15,0      x25 := fmt+1          (scan cursor)
  --> 7798  (the flag/length/conversion char-read + jump-table dispatch loop head)
```

`parseInit_spec` is one `Steps` chain over exactly these 11 instructions.  Its
postcondition pins the two load-bearing parse facts at `0x80007798`:

* **`x20 = -1`** (the width accumulator's "no field width" sentinel), and
* **`x6  = 0`**  (the flags word — no `-`/`+`/`0`/`#`/`' '` flag seen).

These are exactly the facts the two `snprintf("%lld")` residuals reduce to:

* `SnprintfSpec8.entryToPrint_neg_spec`'s `hwidth` — `v20.toInt < (p+1)` — holds
  because the parsed width is `-1 < 1 ≤ p+1`.  On the executed `%lld` path
  (`'l' → "ll" → 'd'`, `0x80009060` then `0x800080d8`) `x20` is **never** written
  between `0x8000777c` and `0x800080e4`, so `v20 = -1` there.
* `SnprintfSpec11.printEntryToSignIov_spec`'s `hflag84` — `vt1 &&& 0x84 = 0` —
  and `SnprintfSpec6`'s `hflag` — `vt1 &&& 0x400 = 0` — hold because the flags
  word entering the digit path is `x6 = 0x20` (only the "ll"-handler's
  `ori x6,x6,32` fires on the `%lld` path), and `0x20 &&& 0x84 = 0`,
  `0x20 &&& 0x400 = 0`.  This module pins the *reset to 0* that the `ori`s build
  on; the `%lld`-specific `0x20` is added downstream (`0x80009060`).

The format string `"%lld"` enters only through the byte at `fmt+1` read by
`lbu x24,1(x22)`.  That byte is carried as an opaque pinned precondition
(`hfmt1 : mem[fmt+1]? = some bfmt1`); for the concrete `"%lld"` literal in rodata
`bfmt1 = 'l' = 0x6c`, but the width/flags reset is independent of it — hence it is
left general.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (SvfprintfSliceLoaded)

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- **`%`-format parse-init `Triple`.**

From `0x8000776c` (the parse-init block entry, reached right after the `'%'`
introducer is detected) to `0x80007798` (the char-read + jump-table dispatch loop
head), one `Steps` chain over the 11 straight-line instructions that reset the
`svfprintf` field-width accumulator and flags word.

Register naming at entry: `x2 = vsp` (frame pointer), `x22 = vfmt` (the format
pointer, positioned at the `'%'`).  The only memory read is `format[1]` at
`vfmt+1`, pinned opaquely as `bfmt1` (the `"%lld"` literal contributes `'l'`
here).  The two stores land in the stack frame (sign-byte slot `sp+167`, fmt
spill `sp+0`), disjoint from the code slice.

Postcondition (the load-bearing parse facts):

* `x20 = -1` — the field-width accumulator, "no width specified";
* `x6  = 0`  — the flags word, "no conversion flags seen".

Both feed the negative-`%lld` digit/PRINT path downstream:
`entryToPrint_neg_spec.hwidth` (via `(-1).toInt < p+1`) and
`printEntryToSignIov_spec.hflag84` / `SnprintfSpec6.hflag` (via the flags being
built from `0`). -/
theorem parseInit_spec
    (vsp vfmt : BitVec 64) (bfmt1 : BitVec 8)
    (c : Config)
    (hG : GoodState c.σ)
    (hload : SvfprintfSliceLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x8000776c#64))
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx22 : c.σ.regs.get? Register.x22 = some vfmt)
    -- the format byte at fmt+1 (the char after '%'); for "%lld" this is 'l'
    (hfmt1 : c.σ.mem[(vfmt + sign_extend (m := 64) (0x001#12)).toNat]? = some bfmt1)
    -- fmt+1 is readable RAM, above HTIF (the format string lives in rodata/RAM)
    (hfmtlo : 0x80000000 ≤ (vfmt + sign_extend (m := 64) (0x001#12)).toNat)
    (hfmthi : (vfmt + sign_extend (m := 64) (0x001#12)).toNat + 1 ≤ 0x100000000)
    (hfmtwin : (vfmt + sign_extend (m := 64) (0x001#12)).toNat + 1 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vfmt + sign_extend (m := 64) (0x001#12)).toNat)
    -- stack frame: RAM above the svfprintf code region, above HTIF, 8-aligned
    (hsplo : 0x80009000 ≤ vsp.toNat)
    (hsphi : vsp.toNat + 356 ≤ 0x100000000)
    (hspwin : tohostAddr + 16 + 64 ≤ vsp.toNat)
    (hspalign : vsp.toNat % 8 = 0)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x80007798#64) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      -- the field-width accumulator: "no width specified"
      c'.σ.regs.get? Register.x20 = some ((0#64) - (0x1#64)) ∧
      -- the flags word reset to 0 (no conversion flags)
      c'.σ.regs.get? Register.x6 = some (0#64) ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) := by
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
  have hnw : vsp.toNat + 348 < 2 ^ 64 := by omega
  -- effective-address facts for the two stack stores (sp+167 sign byte, sp+0 fmt)
  have hoff167 : (vsp + sign_extend (m := 64) (0x0a7#12)).toNat = vsp.toNat + 167 :=
    addoff_toNat_sn5 vsp (0x0a7#12) 167 (by omega) (by decide) hnw
  have hoff0 : (vsp + sign_extend (m := 64) (0x000#12)).toNat = vsp.toNat :=
    addoff_toNat_sn5 vsp (0x000#12) 0 (by omega) (by decide) hnw
  -- === 776c: addi x15,x22,1  ⇒  x15 := vfmt + 1 ===
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_8000776c hload
  have hx22n1 : (afterNextPC (afterPrelude c.σ) (0x8000776c#64)).regs.get? Register.x22 = some vfmt := by
    rw [get?_afterNextPC c.σ (0x8000776c#64) _ (by decide) (by decide)]; exact hx22
  obtain ⟨σ1, i1, hs1s, hi1, hG1, hmem1, hobs1⟩ :=
    stepObs_alu c.σ c.tick c.steps (0x8000776c#64) vmi0 (0x001b0793#32)
      (instruction.ITYPE (0x001#12, regidx.Regidx 0x16#5, regidx.Regidx 0x0f#5, iop.ADDI))
      Register.x15 (vfmt + sign_extend (m := 64) (0x001#12))
      (0x93#8) (0x07#8) (0x1b#8) (0x00#8)
      hG hpc hmi0 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_001b0793 (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (execute_itype_addi_char (0x001#12) (regidx.Regidx 0x16#5) (regidx.Regidx 0x0f#5) vfmt
        (afterNextPC (afterPrelude c.σ) (0x8000776c#64))
        (sigma3_alu c.σ (0x8000776c#64) Register.x15 (vfmt + sign_extend (m := 64) (0x001#12)))
        (rX_bits_x22 _ vfmt hx22n1) (wX_bits_x15 _ (vfmt + sign_extend (m := 64) (0x001#12))))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1s
  have hpc1 : σ1.regs.get? Register.PC = some (0x80007770#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x8000776c#64 : BitVec 64) 4 = (0x80007770#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx15_1 : σ1.regs.get? Register.x15 = some (vfmt + sign_extend (m := 64) (0x001#12)) :=
    obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hx2_1 : σ1.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2
  have hx22_1 : σ1.regs.get? Register.x22 = some vfmt :=
    obs_alu_other hobs1 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22
  have hload1 : SvfprintfSliceLoaded σ1.mem := hmem1 ▸ hload
  have hfmt1_1 : σ1.mem[(vfmt + sign_extend (m := 64) (0x001#12)).toNat]? = some bfmt1 := hmem1 ▸ hfmt1
  -- === 7770: lbu x24,1(x22)  ⇒  x24 := zext bfmt1 ===
  obtain ⟨hc0, hc1, hc2, hc3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80007770 hload1
  have hx22n2 : (afterNextPC (afterPrelude σ1) (0x80007770#64)).regs.get? Register.x22 = some vfmt := by
    rw [get?_afterNextPC σ1 (0x80007770#64) _ (by decide) (by decide)]; exact hx22_1
  obtain ⟨σ2, i2, hs2s, hi2, hG2, hmem2, hobs2⟩ :=
    stepObs_alu σ1 i1 (c.steps + 1) (0x80007770#64) vmi1 (0x001b4c03#32)
      (instruction.LOAD (0x001#12, regidx.Regidx 0x16#5, regidx.Regidx 0x18#5, true, 1))
      Register.x24 (zero_extend (m := 64) bfmt1)
      (0x03#8) (0x4c#8) (0x1b#8) (0x00#8)
      hG1 hpc1 hmi1 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_001b4c03 (afterPrelude σ1)
        (by rw [get?_afterPrelude σ1 _ (by decide)]; exact hG1.misa)
        (by rw [get?_afterPrelude σ1 _ (by decide)]; exact hG1.cur_privilege)
        (by rw [get?_afterPrelude σ1 _ (by decide)]; exact hG1.mseccfg))
      (exec_lbu_gen σ1 (0x80007770#64) (0x001#12) (regidx.Regidx 0x16#5) (regidx.Regidx 0x18#5)
        vfmt bfmt1 _ hG1 (rX_bits_x22 _ vfmt hx22n2)
        (wX_bits_x24 _ (zero_extend (m := 64) bfmt1))
        hfmtlo hfmthi hfmtwin hfmt1_1)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hc0 hc1 hc2 hc3 (by decide) (by decide) (by decide) hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2s
  have hpc2 : σ2.regs.get? Register.PC = some (0x80007774#64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x80007770#64 : BitVec 64) 4 = (0x80007774#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hx2_2 : σ2.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs2 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_1
  have hx15_2 : σ2.regs.get? Register.x15 = some (vfmt + sign_extend (m := 64) (0x001#12)) :=
    obs_alu_other hobs2 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_1
  have hload2 : SvfprintfSliceLoaded σ2.mem := hmem2 ▸ hload1
  -- === 7774: sb x0,167(sp)  ⇒  mem[sp+167] := 0 ===
  obtain ⟨hd0, hd1, hd2, hd3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80007774 hload2
  have hx2n3 : (afterNextPC (afterPrelude σ2) (0x80007774#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ2 (0x80007774#64) _ (by decide) (by decide)]; exact hx2_2
  obtain ⟨σ3, i3, hs3s, hi3, hG3, hmem3, hobs3⟩ :=
    stepObs_store σ2 i2 (c.steps + 1 + 1) (0x80007774#64) vmi2 (0x0a0103a3#32)
      (instruction.STORE (0x0a7#12, regidx.Regidx 0x00#5, regidx.Regidx 0x02#5, 1))
      ((afterNextPC (afterPrelude σ2) (0x80007774#64)).mem.insert
        (vsp + sign_extend (m := 64) (0x0a7#12)).toNat (stData 1 (0#64)))
      (0xa3#8) (0x03#8) (0x01#8) (0x0a#8)
      hG2 hpc2 hmi2 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_0a0103a3 (afterPrelude σ2)
        (by rw [get?_afterPrelude σ2 _ (by decide)]; exact hG2.misa)
        (by rw [get?_afterPrelude σ2 _ (by decide)]; exact hG2.cur_privilege)
        (by rw [get?_afterPrelude σ2 _ (by decide)]; exact hG2.mseccfg))
      (exec_sb σ2 (0x80007774#64) (0x0a7#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x02#5)
        vsp (0#64) hG2 (rX_bits_x2 _ vsp hx2n3) (rX_bits_zero _)
        (by rw [hoff167]; omega) (by rw [hoff167]; omega) (by rw [hoff167]; omega))
      hd0 hd1 hd2 hd3 (by decide) (by decide) (by decide) hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3s
  have hpc3 : σ3.regs.get? Register.PC = some (0x80007778#64) := by
    have := obs_store_pc_sn4 hobs3
    rwa [show BitVec.addInt (0x80007774#64 : BitVec 64) 4 = (0x80007778#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi3, hmi3⟩ := obs_store_minstret_sn4 hobs3
  have hx2_3 : σ3.regs.get? Register.x2 = some vsp :=
    obs_store_other_sn4 Register.x2 hobs3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_2
  have hx15_3 : σ3.regs.get? Register.x15 = some (vfmt + sign_extend (m := 64) (0x001#12)) :=
    obs_store_other_sn4 Register.x15 hobs3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_2
  have hmem3' : σ3.mem = σ2.mem.insert (vsp + sign_extend (m := 64) (0x0a7#12)).toNat (stData 1 (0#64)) := by
    rw [hmem3]
  have hload3 : SvfprintfSliceLoaded σ3.mem := by
    rw [hmem3']; exact svfprintfSlice_insert_sn4 _ _ _ (by rw [hoff167]; omega) hload2
  -- === 7778: sd x15,0(sp)  ⇒  mem[sp+0] := fmt+1 ===
  obtain ⟨he0, he1, he2, he3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80007778 hload3
  have hx2n4 : (afterNextPC (afterPrelude σ3) (0x80007778#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ3 (0x80007778#64) _ (by decide) (by decide)]; exact hx2_3
  have hx15n4 : (afterNextPC (afterPrelude σ3) (0x80007778#64)).regs.get? Register.x15
      = some (vfmt + sign_extend (m := 64) (0x001#12)) := by
    rw [get?_afterNextPC σ3 (0x80007778#64) _ (by decide) (by decide)]; exact hx15_3
  obtain ⟨σ4, i4, hs4s, hi4, hG4, hmem4, hobs4⟩ :=
    stepObs_store σ3 i3 (c.steps + 1 + 1 + 1) (0x80007778#64) vmi3 (0x00f13023#32)
      (instruction.STORE (0x000#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x02#5, 8))
      (writeMap8 (afterNextPC (afterPrelude σ3) (0x80007778#64)).mem
        (vsp + sign_extend (m := 64) (0x000#12)).toNat (sdData_val (vfmt + sign_extend (m := 64) (0x001#12))))
      (0x23#8) (0x30#8) (0xf1#8) (0x00#8)
      hG3 hpc3 hmi3 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_00f13023 (afterPrelude σ3)
        (by rw [get?_afterPrelude σ3 _ (by decide)]; exact hG3.misa)
        (by rw [get?_afterPrelude σ3 _ (by decide)]; exact hG3.cur_privilege)
        (by rw [get?_afterPrelude σ3 _ (by decide)]; exact hG3.mseccfg))
      (exec_sd_val σ3 (0x80007778#64) (0x000#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x02#5)
        vsp (vfmt + sign_extend (m := 64) (0x001#12)) hG3 (rX_bits_x2 _ vsp hx2n4)
        (rX_bits_x15 _ (vfmt + sign_extend (m := 64) (0x001#12)) hx15n4)
        (by rw [hoff0]; omega) (by rw [hoff0]; omega) (by rw [hoff0]; omega) (by rw [hoff0]; omega))
      he0 he1 he2 he3 (by decide) (by decide) (by decide) hi3
  have hstep4 : Step ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ := hs4s
  have hpc4 : σ4.regs.get? Register.PC = some (0x8000777c#64) := by
    have := obs_store_pc_sn4 hobs4
    rwa [show BitVec.addInt (0x80007778#64 : BitVec 64) 4 = (0x8000777c#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi4, hmi4⟩ := obs_store_minstret_sn4 hobs4
  have hx2_4 : σ4.regs.get? Register.x2 = some vsp :=
    obs_store_other_sn4 Register.x2 hobs4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_3
  have hmem4' : σ4.mem = writeMap8 σ3.mem (vsp + sign_extend (m := 64) (0x000#12)).toNat
      (sdData_val (vfmt + sign_extend (m := 64) (0x001#12))) := by
    rw [hmem4]
  have hload4 : SvfprintfSliceLoaded σ4.mem := by
    rw [hmem4']; exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff0]; omega) hload3
  -- === 777c: addi x20,x0,-1  ⇒  x20 := -1  (WIDTH accumulator reset) ===
  obtain ⟨hf0, hf1, hf2, hf3⟩ := Vsa.Sim.Code.svfprintfSlice_at_8000777c hload4
  obtain ⟨σ5, i5, hs5s, hi5, hG5, hmem5, hobs5⟩ :=
    stepObs_alu σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x8000777c#64) vmi4 (0xfff00a13#32)
      (instruction.ITYPE (0xfff#12, regidx.Regidx 0x00#5, regidx.Regidx 0x14#5, iop.ADDI))
      Register.x20 ((0#64) + sign_extend (m := 64) (0xfff#12))
      (0x13#8) (0x0a#8) (0xf0#8) (0xff#8)
      hG4 hpc4 hmi4 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_fff00a13 (afterPrelude σ4)
        (by rw [get?_afterPrelude σ4 _ (by decide)]; exact hG4.misa)
        (by rw [get?_afterPrelude σ4 _ (by decide)]; exact hG4.cur_privilege)
        (by rw [get?_afterPrelude σ4 _ (by decide)]; exact hG4.mseccfg))
      (execute_itype_addi_char (0xfff#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x14#5) (0#64)
        (afterNextPC (afterPrelude σ4) (0x8000777c#64))
        (sigma3_alu σ4 (0x8000777c#64) Register.x20 ((0#64) + sign_extend (m := 64) (0xfff#12)))
        (rX_bits_zero _) (wX_bits_x20 _ ((0#64) + sign_extend (m := 64) (0xfff#12))))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hf0 hf1 hf2 hf3 (by decide) (by decide) (by decide) hi4
  have hstep5 : Step ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ := hs5s
  have hpc5 : σ5.regs.get? Register.PC = some (0x80007780#64) := by
    have := obs_alu_pc hobs5
    rwa [show BitVec.addInt (0x8000777c#64 : BitVec 64) 4 = (0x80007780#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx20_5 : σ5.regs.get? Register.x20 = some ((0#64) - (0x1#64)) := by
    have := obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64) + sign_extend (m := 64) (0xfff#12) : BitVec 64) = ((0#64) - (0x1#64)) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi5, hmi5⟩ := obs_alu_minstret hobs5
  have hx2_5 : σ5.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs5 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_4
  have hload5 : SvfprintfSliceLoaded σ5.mem := hmem5 ▸ hload4
  -- === 7780: addi x6,x0,0  ⇒  x6 := 0  (FLAGS word reset) ===
  obtain ⟨hg0, hg1, hg2, hg3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80007780 hload5
  obtain ⟨σ6, i6, hs6s, hi6, hG6, hmem6, hobs6⟩ :=
    stepObs_alu σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x80007780#64) vmi5 (0x00000313#32)
      (instruction.ITYPE (0x000#12, regidx.Regidx 0x00#5, regidx.Regidx 0x06#5, iop.ADDI))
      Register.x6 ((0#64) + sign_extend (m := 64) (0x000#12))
      (0x13#8) (0x03#8) (0x00#8) (0x00#8)
      hG5 hpc5 hmi5 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_00000313 (afterPrelude σ5)
        (by rw [get?_afterPrelude σ5 _ (by decide)]; exact hG5.misa)
        (by rw [get?_afterPrelude σ5 _ (by decide)]; exact hG5.cur_privilege)
        (by rw [get?_afterPrelude σ5 _ (by decide)]; exact hG5.mseccfg))
      (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x06#5) (0#64)
        (afterNextPC (afterPrelude σ5) (0x80007780#64))
        (sigma3_alu σ5 (0x80007780#64) Register.x6 ((0#64) + sign_extend (m := 64) (0x000#12)))
        (rX_bits_zero _) (wX_bits_x6 _ ((0#64) + sign_extend (m := 64) (0x000#12))))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hg0 hg1 hg2 hg3 (by decide) (by decide) (by decide) hi5
  have hstep6 : Step ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ ⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs6s
  have hpc6 : σ6.regs.get? Register.PC = some (0x80007784#64) := by
    have := obs_alu_pc hobs6
    rwa [show BitVec.addInt (0x80007780#64 : BitVec 64) 4 = (0x80007784#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx6_6 : σ6.regs.get? Register.x6 = some (0#64) := by
    have := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64) + sign_extend (m := 64) (0x000#12) : BitVec 64) = (0#64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi6, hmi6⟩ := obs_alu_minstret hobs6
  have hx2_6 : σ6.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs6 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_5
  have hx20_6 : σ6.regs.get? Register.x20 = some ((0#64) - (0x1#64)) :=
    obs_alu_other hobs6 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_5
  have hload6 : SvfprintfSliceLoaded σ6.mem := hmem6 ▸ hload5
  -- === 7784: addi x26,x0,90  ⇒  x26 := 90 ===
  obtain ⟨hh0, hh1, hh2, hh3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80007784 hload6
  obtain ⟨σ7, i7, hs7s, hi7, hG7, hmem7, hobs7⟩ :=
    stepObs_alu σ6 i6 (c.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x80007784#64) vmi6 (0x05a00d13#32)
      (instruction.ITYPE (0x05a#12, regidx.Regidx 0x00#5, regidx.Regidx 0x1a#5, iop.ADDI))
      Register.x26 ((0#64) + sign_extend (m := 64) (0x05a#12))
      (0x13#8) (0x0d#8) (0xa0#8) (0x05#8)
      hG6 hpc6 hmi6 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_05a00d13 (afterPrelude σ6)
        (by rw [get?_afterPrelude σ6 _ (by decide)]; exact hG6.misa)
        (by rw [get?_afterPrelude σ6 _ (by decide)]; exact hG6.cur_privilege)
        (by rw [get?_afterPrelude σ6 _ (by decide)]; exact hG6.mseccfg))
      (execute_itype_addi_char (0x05a#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x1a#5) (0#64)
        (afterNextPC (afterPrelude σ6) (0x80007784#64))
        (sigma3_alu σ6 (0x80007784#64) Register.x26 ((0#64) + sign_extend (m := 64) (0x05a#12)))
        (rX_bits_zero _) (wX_bits_x26 _ ((0#64) + sign_extend (m := 64) (0x05a#12))))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hh0 hh1 hh2 hh3 (by decide) (by decide) (by decide) hi6
  have hstep7 : Step ⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ7, i7, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs7s
  have hpc7 : σ7.regs.get? Register.PC = some (0x80007788#64) := by
    have := obs_alu_pc hobs7
    rwa [show BitVec.addInt (0x80007784#64 : BitVec 64) 4 = (0x80007788#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi7, hmi7⟩ := obs_alu_minstret hobs7
  have hx2_7 : σ7.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs7 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_6
  have hx20_7 : σ7.regs.get? Register.x20 = some ((0#64) - (0x1#64)) :=
    obs_alu_other hobs7 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_6
  have hx6_7 : σ7.regs.get? Register.x6 = some (0#64) :=
    obs_alu_other hobs7 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_6
  have hload7 : SvfprintfSliceLoaded σ7.mem := hmem7 ▸ hload6
  -- === 7788: auipc x22,0x13000  ⇒  x22 := pc + 0x13000 = 0x8001a788 ===
  obtain ⟨hj0, hj1, hj2, hj3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80007788 hload7
  obtain ⟨σ8, i8, hs8s, hi8, hG8, hmem8, hobs8⟩ :=
    stepObs_alu σ7 i7 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80007788#64) vmi7 (0x00013b17#32)
      (instruction.UTYPE (0x00013#20, regidx.Regidx 0x16#5, uop.AUIPC))
      Register.x22 ((0x80007788#64) + sign_extend (m := 64) ((0x00013#20) +++ 0x000#12))
      (0x17#8) (0x3b#8) (0x01#8) (0x00#8)
      hG7 hpc7 hmi7 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_00013b17 (afterPrelude σ7)
        (by rw [get?_afterPrelude σ7 _ (by decide)]; exact hG7.misa)
        (by rw [get?_afterPrelude σ7 _ (by decide)]; exact hG7.cur_privilege)
        (by rw [get?_afterPrelude σ7 _ (by decide)]; exact hG7.mseccfg))
      (execute_utype_auipc_char (0x00013#20) (regidx.Regidx 0x16#5) (0x80007788#64)
        (afterNextPC (afterPrelude σ7) (0x80007788#64))
        (sigma3_alu σ7 (0x80007788#64) Register.x22
          ((0x80007788#64) + sign_extend (m := 64) ((0x00013#20) +++ 0x000#12)))
        (by rw [get?_afterNextPC σ7 (0x80007788#64) _ (by decide) (by decide)]; exact hpc7)
        (wX_bits_x22 _ ((0x80007788#64) + sign_extend (m := 64) ((0x00013#20) +++ 0x000#12))))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hj0 hj1 hj2 hj3 (by decide) (by decide) (by decide) hi7
  have hstep8 : Step ⟨σ7, i7, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ8, i8, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs8s
  have hpc8 : σ8.regs.get? Register.PC = some (0x8000778c#64) := by
    have := obs_alu_pc hobs8
    rwa [show BitVec.addInt (0x80007788#64 : BitVec 64) 4 = (0x8000778c#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx22_8 : σ8.regs.get? Register.x22
      = some ((0x80007788#64) + sign_extend (m := 64) ((0x00013#20) +++ 0x000#12)) :=
    obs_alu_rd hobs8 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi8, hmi8⟩ := obs_alu_minstret hobs8
  have hx2_8 : σ8.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs8 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_7
  have hx20_8 : σ8.regs.get? Register.x20 = some ((0#64) - (0x1#64)) :=
    obs_alu_other hobs8 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_7
  have hx6_8 : σ8.regs.get? Register.x6 = some (0#64) :=
    obs_alu_other hobs8 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_7
  have hload8 : SvfprintfSliceLoaded σ8.mem := hmem8 ▸ hload7
  -- === 778c: addi x22,x22,-1676  ⇒  x22 := jump-table base 0x8001a0fc ===
  obtain ⟨hk0, hk1, hk2, hk3⟩ := Vsa.Sim.Code.svfprintfSlice_at_8000778c hload8
  have hx22n9 : (afterNextPC (afterPrelude σ8) (0x8000778c#64)).regs.get? Register.x22
      = some ((0x80007788#64) + sign_extend (m := 64) ((0x00013#20) +++ 0x000#12)) := by
    rw [get?_afterNextPC σ8 (0x8000778c#64) _ (by decide) (by decide)]; exact hx22_8
  obtain ⟨σ9, i9, hs9s, hi9, hG9, hmem9, hobs9⟩ :=
    stepObs_alu σ8 i8 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x8000778c#64) vmi8 (0x974b0b13#32)
      (instruction.ITYPE (0x974#12, regidx.Regidx 0x16#5, regidx.Regidx 0x16#5, iop.ADDI))
      Register.x22 (((0x80007788#64) + sign_extend (m := 64) ((0x00013#20) +++ 0x000#12))
        + sign_extend (m := 64) (0x974#12))
      (0x13#8) (0x0b#8) (0x4b#8) (0x97#8)
      hG8 hpc8 hmi8 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_974b0b13 (afterPrelude σ8)
        (by rw [get?_afterPrelude σ8 _ (by decide)]; exact hG8.misa)
        (by rw [get?_afterPrelude σ8 _ (by decide)]; exact hG8.cur_privilege)
        (by rw [get?_afterPrelude σ8 _ (by decide)]; exact hG8.mseccfg))
      (execute_itype_addi_char (0x974#12) (regidx.Regidx 0x16#5) (regidx.Regidx 0x16#5)
        ((0x80007788#64) + sign_extend (m := 64) ((0x00013#20) +++ 0x000#12))
        (afterNextPC (afterPrelude σ8) (0x8000778c#64))
        (sigma3_alu σ8 (0x8000778c#64) Register.x22
          (((0x80007788#64) + sign_extend (m := 64) ((0x00013#20) +++ 0x000#12))
            + sign_extend (m := 64) (0x974#12)))
        (rX_bits_x22 _ _ hx22n9)
        (wX_bits_x22 _ _))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hk0 hk1 hk2 hk3 (by decide) (by decide) (by decide) hi8
  have hstep9 : Step ⟨σ8, i8, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ9, i9, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs9s
  have hpc9 : σ9.regs.get? Register.PC = some (0x80007790#64) := by
    have := obs_alu_pc hobs9
    rwa [show BitVec.addInt (0x8000778c#64 : BitVec 64) 4 = (0x80007790#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi9, hmi9⟩ := obs_alu_minstret hobs9
  have hx2_9 : σ9.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs9 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_8
  have hx20_9 : σ9.regs.get? Register.x20 = some ((0#64) - (0x1#64)) :=
    obs_alu_other hobs9 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_8
  have hx6_9 : σ9.regs.get? Register.x6 = some (0#64) :=
    obs_alu_other hobs9 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_8
  have hload9 : SvfprintfSliceLoaded σ9.mem := hmem9 ▸ hload8
  -- === 7790: addi x27,x0,0  ⇒  x27 := 0 ===
  obtain ⟨hl0, hl1, hl2, hl3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80007790 hload9
  obtain ⟨σ10, i10, hs10s, hi10, hG10, hmem10, hobs10⟩ :=
    stepObs_alu σ9 i9 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80007790#64) vmi9 (0x00000d93#32)
      (instruction.ITYPE (0x000#12, regidx.Regidx 0x00#5, regidx.Regidx 0x1b#5, iop.ADDI))
      Register.x27 ((0#64) + sign_extend (m := 64) (0x000#12))
      (0x93#8) (0x0d#8) (0x00#8) (0x00#8)
      hG9 hpc9 hmi9 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_00000d93 (afterPrelude σ9)
        (by rw [get?_afterPrelude σ9 _ (by decide)]; exact hG9.misa)
        (by rw [get?_afterPrelude σ9 _ (by decide)]; exact hG9.cur_privilege)
        (by rw [get?_afterPrelude σ9 _ (by decide)]; exact hG9.mseccfg))
      (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x1b#5) (0#64)
        (afterNextPC (afterPrelude σ9) (0x80007790#64))
        (sigma3_alu σ9 (0x80007790#64) Register.x27 ((0#64) + sign_extend (m := 64) (0x000#12)))
        (rX_bits_zero _) (wX_bits_x27 _ ((0#64) + sign_extend (m := 64) (0x000#12))))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hl0 hl1 hl2 hl3 (by decide) (by decide) (by decide) hi9
  have hstep10 : Step ⟨σ9, i9, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ10, i10, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs10s
  have hpc10 : σ10.regs.get? Register.PC = some (0x80007794#64) := by
    have := obs_alu_pc hobs10
    rwa [show BitVec.addInt (0x80007790#64 : BitVec 64) 4 = (0x80007794#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi10, hmi10⟩ := obs_alu_minstret hobs10
  have hx2_10 : σ10.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs10 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_9
  have hx15_10 : σ10.regs.get? Register.x15 = some (vfmt + sign_extend (m := 64) (0x001#12)) := by
    -- x15 has not been touched since step 2 (only stores/other-rd writes between)
    have e2 := obs_store_other_sn4 Register.x15 hobs4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_3
    have e5 := obs_alu_other hobs5 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) e2
    have e6 := obs_alu_other hobs6 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) e5
    have e7 := obs_alu_other hobs7 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) e6
    have e8 := obs_alu_other hobs8 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) e7
    have e9 := obs_alu_other hobs9 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) e8
    exact obs_alu_other hobs10 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) e9
  have hx20_10 : σ10.regs.get? Register.x20 = some ((0#64) - (0x1#64)) :=
    obs_alu_other hobs10 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_9
  have hx6_10 : σ10.regs.get? Register.x6 = some (0#64) :=
    obs_alu_other hobs10 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_9
  have hload10 : SvfprintfSliceLoaded σ10.mem := hmem10 ▸ hload9
  -- === 7794: addi x25,x15,0  ⇒  x25 := fmt+1  (final step; falls through to 7798) ===
  obtain ⟨hn0, hn1, hn2, hn3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80007794 hload10
  have hx15n11 : (afterNextPC (afterPrelude σ10) (0x80007794#64)).regs.get? Register.x15
      = some (vfmt + sign_extend (m := 64) (0x001#12)) := by
    rw [get?_afterNextPC σ10 (0x80007794#64) _ (by decide) (by decide)]; exact hx15_10
  obtain ⟨σ11, i11, hs11s, hi11, hG11, hmem11, hobs11⟩ :=
    stepObs_alu σ10 i10 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80007794#64) vmi10 (0x00078c93#32)
      (instruction.ITYPE (0x000#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x19#5, iop.ADDI))
      Register.x25 ((vfmt + sign_extend (m := 64) (0x001#12)) + sign_extend (m := 64) (0x000#12))
      (0x93#8) (0x8c#8) (0x07#8) (0x00#8)
      hG10 hpc10 hmi10 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_00078c93 (afterPrelude σ10)
        (by rw [get?_afterPrelude σ10 _ (by decide)]; exact hG10.misa)
        (by rw [get?_afterPrelude σ10 _ (by decide)]; exact hG10.cur_privilege)
        (by rw [get?_afterPrelude σ10 _ (by decide)]; exact hG10.mseccfg))
      (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x19#5)
        (vfmt + sign_extend (m := 64) (0x001#12))
        (afterNextPC (afterPrelude σ10) (0x80007794#64))
        (sigma3_alu σ10 (0x80007794#64) Register.x25
          ((vfmt + sign_extend (m := 64) (0x001#12)) + sign_extend (m := 64) (0x000#12)))
        (rX_bits_x15 _ (vfmt + sign_extend (m := 64) (0x001#12)) hx15n11)
        (wX_bits_x25 _ ((vfmt + sign_extend (m := 64) (0x001#12)) + sign_extend (m := 64) (0x000#12))))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hn0 hn1 hn2 hn3 (by decide) (by decide) (by decide) hi10
  have hstep11 : Step ⟨σ10, i10, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ11, i11, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs11s
  have hpc11 : σ11.regs.get? Register.PC = some (0x80007798#64) := by
    have := obs_alu_pc hobs11
    rwa [show BitVec.addInt (0x80007794#64 : BitVec 64) 4 = (0x80007798#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi11, hmi11⟩ := obs_alu_minstret hobs11
  have hx2_11 : σ11.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs11 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_10
  have hx20_11 : σ11.regs.get? Register.x20 = some ((0#64) - (0x1#64)) :=
    obs_alu_other hobs11 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_10
  have hx6_11 : σ11.regs.get? Register.x6 = some (0#64) :=
    obs_alu_other hobs11 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_10
  -- === assemble the Steps chain ===
  refine ⟨⟨σ11, i11, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩, ?_, hG11, hpc11, hx2_11,
    hx20_11, hx6_11, hi11, ⟨vmi11, hmi11⟩⟩
  exact (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans
    ((Steps.single hstep4).trans ((Steps.single hstep5).trans ((Steps.single hstep6).trans
    ((Steps.single hstep7).trans ((Steps.single hstep8).trans ((Steps.single hstep9).trans
    ((Steps.single hstep10).trans (Steps.single hstep11))))))))))

end Vsa.Sim
