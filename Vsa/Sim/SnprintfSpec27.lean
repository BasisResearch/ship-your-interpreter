import Vsa.Sim.SnprintfProCommon
import Vsa.Sim.SnprintfSitesPro
import Vsa.Sim.SnprintfSitesPro2

/-!
# M3 Layer-3 — `SnprintfSpec27` : svfprintf prologue segment A
## `0x80007654` (entry) → `0x8000768c` (the `jal strlen`)

First segment of the svfprintf PROLOGUE + first-parse-pass chain (pctrace
`[0x80007654, 0x800077c0)`).  16 machine steps: `addi sp,sp,-592`, the six
early spills, the `mv` triple, `jal _localeconv_r` with the 2-instruction
callee body inlined (`addi a0,gp,904; ret` — gp is the concrete link-time
`0x8001b510`), the `ld` of the static `decimal_point` pointer
(`0x8001b898 → 0x80019770`), `mv a0,a4`, and the spill of the pointer to
`sp+80`.  Generated in the SnprintfSpec22 house style by /tmp/gen_spec27.py.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- **Segment A of the svfprintf prologue**: `0x80007654 → 0x8000768c`.

Entry: the `_svfprintf_r` ABI entry (`a0` = reent, `a1` = FILE, `a2` = fmt,
`a3` = va_list, `sp = vsp + 592`).  Runs `addi sp,sp,-592`, the first six
spills (`ra/a3/a1/s0/s1/s6`), the register moves, the `_localeconv_r` call
(2 callee instructions, inlined), the `ld` of the static `decimal_point`
pointer, and its spill to `sp+80`; stops poised at the `jal strlen`. -/
theorem svfProA_spec
    (vsp vra0 va0 vfile vfmt vva : BitVec 64)
    (vS0o vS1o vS2o vS3o vS4o vS5o vS6o vS7o vS8o vS9o vS10o vS11o : BitVec 64)
    (c : Config)
    (hG : GoodState c.σ)
    (hsl0 : Vsa.Sim.Code.SvfprintfSliceLoaded c.σ.mem)
    (hlc0 : Vsa.Sim.Code._localeconv_rLoaded c.σ.mem)
    (hstrl : Vsa.Sim.Code.StrlenLoaded c.σ.mem)
    (hms : Vsa.Sim.Code.MemsetLoaded c.σ.mem)
    (hlm : Vsa.Sim.Code.__locale_mb_cur_maxLoaded c.σ.mem)
    (hamb : Vsa.Sim.Code.__ascii_mbtowcLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x80007654#64))
    (hx2 : c.σ.regs.get? Register.x2 = some (vsp + (592#64)))
    (hx1 : c.σ.regs.get? Register.x1 = some vra0)
    (hx3 : c.σ.regs.get? Register.x3 = some (0x8001b510#64))
    (hx10 : c.σ.regs.get? Register.x10 = some va0)
    (hx11 : c.σ.regs.get? Register.x11 = some vfile)
    (hx12 : c.σ.regs.get? Register.x12 = some vfmt)
    (hx13 : c.σ.regs.get? Register.x13 = some vva)
    (hx8 : c.σ.regs.get? Register.x8 = some vS0o)
    (hx9 : c.σ.regs.get? Register.x9 = some vS1o)
    (hx22 : c.σ.regs.get? Register.x22 = some vS6o)
    (hx18 : c.σ.regs.get? Register.x18 = some vS2o)
    (hx19 : c.σ.regs.get? Register.x19 = some vS3o)
    (hx20 : c.σ.regs.get? Register.x20 = some vS4o)
    (hx21 : c.σ.regs.get? Register.x21 = some vS5o)
    (hx23 : c.σ.regs.get? Register.x23 = some vS7o)
    (hx24 : c.σ.regs.get? Register.x24 = some vS8o)
    (hx25 : c.σ.regs.get? Register.x25 = some vS9o)
    (hx26 : c.σ.regs.get? Register.x26 = some vS10o)
    (hx27 : c.σ.regs.get? Register.x27 = some vS11o)
    (hdp0 : c.σ.mem[(0x8001b898 : Nat)]? = some (0x70#8))
    (hdp1 : c.σ.mem[(0x8001b898 : Nat) + 1]? = some (0x97#8))
    (hdp2 : c.σ.mem[(0x8001b898 : Nat) + 2]? = some (0x01#8))
    (hdp3 : c.σ.mem[(0x8001b898 : Nat) + 3]? = some (0x80#8))
    (hdp4 : c.σ.mem[(0x8001b898 : Nat) + 4]? = some (0x00#8))
    (hdp5 : c.σ.mem[(0x8001b898 : Nat) + 5]? = some (0x00#8))
    (hdp6 : c.σ.mem[(0x8001b898 : Nat) + 6]? = some (0x00#8))
    (hdp7 : c.σ.mem[(0x8001b898 : Nat) + 7]? = some (0x00#8))
    (hsplo : 0x8001c000 ≤ vsp.toNat)
    (hsphi : vsp.toNat + 592 ≤ 0x100000000)
    (hspal : vsp.toNat % 8 = 0)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x8000768c#64) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.σ.regs.get? Register.x1 = some (0x80007680#64) ∧
      c'.σ.regs.get? Register.x3 = some (0x8001b510#64) ∧
      c'.σ.regs.get? Register.x8 = some va0 ∧
      c'.σ.regs.get? Register.x9 = some vfile ∧
      c'.σ.regs.get? Register.x22 = some vfmt ∧
      c'.σ.regs.get? Register.x10 = some (0x80019770#64) ∧
      c'.σ.regs.get? Register.x14 = some (0x80019770#64) ∧
      c'.σ.regs.get? Register.x12 = some vfmt ∧
      c'.σ.regs.get? Register.x13 = some vva ∧
      c'.σ.regs.get? Register.x18 = some vS2o ∧
      c'.σ.regs.get? Register.x19 = some vS3o ∧
      c'.σ.regs.get? Register.x20 = some vS4o ∧
      c'.σ.regs.get? Register.x21 = some vS5o ∧
      c'.σ.regs.get? Register.x23 = some vS7o ∧
      c'.σ.regs.get? Register.x24 = some vS8o ∧
      c'.σ.regs.get? Register.x25 = some vS9o ∧
      c'.σ.regs.get? Register.x26 = some vS10o ∧
      c'.σ.regs.get? Register.x27 = some vS11o ∧
      SlotHolds vsp 0x248 vra0 c'.σ.mem ∧
      SlotHolds vsp 0x018 vva c'.σ.mem ∧
      SlotHolds vsp 0x008 vfile c'.σ.mem ∧
      SlotHolds vsp 0x240 vS0o c'.σ.mem ∧
      SlotHolds vsp 0x238 vS1o c'.σ.mem ∧
      SlotHolds vsp 0x210 vS6o c'.σ.mem ∧
      SlotHolds vsp 0x050 (0x80019770#64) c'.σ.mem ∧
      (∀ a : Nat, ¬(vsp.toNat + 584 ≤ a ∧ a < vsp.toNat + 592) →
      ¬(vsp.toNat + 24 ≤ a ∧ a < vsp.toNat + 32) →
      ¬(vsp.toNat + 8 ≤ a ∧ a < vsp.toNat + 16) →
      ¬(vsp.toNat + 576 ≤ a ∧ a < vsp.toNat + 584) →
      ¬(vsp.toNat + 568 ≤ a ∧ a < vsp.toNat + 576) →
      ¬(vsp.toNat + 528 ≤ a ∧ a < vsp.toNat + 536) →
      ¬(vsp.toNat + 80 ≤ a ∧ a < vsp.toNat + 88) →
        c'.σ.mem[a]? = c.σ.mem[a]?) ∧
      Vsa.Sim.Code.SvfprintfSliceLoaded c'.σ.mem ∧
      Vsa.Sim.Code._localeconv_rLoaded c'.σ.mem ∧
      Vsa.Sim.Code.StrlenLoaded c'.σ.mem ∧
      Vsa.Sim.Code.MemsetLoaded c'.σ.mem ∧
      Vsa.Sim.Code.__locale_mb_cur_maxLoaded c'.σ.mem ∧
      Vsa.Sim.Code.__ascii_mbtowcLoaded c'.σ.mem ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
  have hoff584 : (vsp + sign_extend (m := 64) (0x248#12)).toNat = vsp.toNat + 584 := ptr_addoff vsp _ 584 (by decide) (by omega)
  have hoff24 : (vsp + sign_extend (m := 64) (0x018#12)).toNat = vsp.toNat + 24 := ptr_addoff vsp _ 24 (by decide) (by omega)
  have hoff8 : (vsp + sign_extend (m := 64) (0x008#12)).toNat = vsp.toNat + 8 := ptr_addoff vsp _ 8 (by decide) (by omega)
  have hoff576 : (vsp + sign_extend (m := 64) (0x240#12)).toNat = vsp.toNat + 576 := ptr_addoff vsp _ 576 (by decide) (by omega)
  have hoff568 : (vsp + sign_extend (m := 64) (0x238#12)).toNat = vsp.toNat + 568 := ptr_addoff vsp _ 568 (by decide) (by omega)
  have hoff528 : (vsp + sign_extend (m := 64) (0x210#12)).toNat = vsp.toNat + 528 := ptr_addoff vsp _ 528 (by decide) (by omega)
  have hoff80 : (vsp + sign_extend (m := 64) (0x050#12)).toNat = vsp.toNat + 80 := ptr_addoff vsp _ 80 (by decide) (by omega)
  have hoffdp : ((0x8001b898#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)).toNat = (0x8001b898 : Nat) := by decide
  have hp0 : PinsHold c.σ [⟨Register.x2, vsp + (592#64)⟩, ⟨Register.x1, vra0⟩, ⟨Register.x3, (0x8001b510#64)⟩, ⟨Register.x10, va0⟩, ⟨Register.x11, vfile⟩, ⟨Register.x12, vfmt⟩, ⟨Register.x13, vva⟩, ⟨Register.x8, vS0o⟩, ⟨Register.x9, vS1o⟩, ⟨Register.x22, vS6o⟩, ⟨Register.x18, vS2o⟩, ⟨Register.x19, vS3o⟩, ⟨Register.x20, vS4o⟩, ⟨Register.x21, vS5o⟩, ⟨Register.x23, vS7o⟩, ⟨Register.x24, vS8o⟩, ⟨Register.x25, vS9o⟩, ⟨Register.x26, vS10o⟩, ⟨Register.x27, vS11o⟩] :=
    ⟨hx2, hx1, hx3, hx10, hx11, hx12, hx13, hx8, hx9, hx22, hx18, hx19, hx20, hx21, hx23, hx24, hx25, hx26, hx27, trivial⟩
  -- === 0x80007654: addi sp,sp,-592 ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80007654_pr c.σ c.tick c.steps _ vmi0 (vsp + (592#64))
      hG hpc hmi0 hp0.1 hsl0 rfl htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1
  have hpc1 : σ1.regs.get? Register.PC = some (0x80007658#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x80007654#64) 4 = (0x80007658#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hrd1 : σ1.regs.get? Register.x2 = some (vsp) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sp_dec592_pro vsp] at this
  have hp1 := pins_cons_pro hrd1 (pins_alu hobs1 (by rfl) hp0.2)
  have hmE1 : σ1.mem = c.σ.mem := hmem1
  have hsl1 : Vsa.Sim.Code.SvfprintfSliceLoaded σ1.mem := by rw [hmem1]; exact hsl0
  have hlc1 : Vsa.Sim.Code._localeconv_rLoaded σ1.mem := by rw [hmem1]; exact hlc0

  -- === 0x80007658: sd -> sp+584 ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80007658_pr σ1 i1 (c.steps + 1) _ vmi1 vsp _
      hG1 hpc1 hmi1 hp1.1 hp1.2.1 hsl1 rfl (by rw [hoff584]; omega) (by rw [hoff584]; omega) (by rw [hoff584, htoh]; omega) (by rw [hoff584]; omega) hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 2⟩ := hs2
  have hpc2 : σ2.regs.get? Register.PC = some (0x8000765c#64) := by
    have := obs_store_pc hobs2
    rwa [show BitVec.addInt (0x80007658#64) 4 = (0x8000765c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi2, hmi2⟩ := obs_store_minstret hobs2
  have hp2 := pins_store hobs2 (by rfl) hp1
  have hmE2 : σ2.mem = writeMap8 (c.σ.mem) (vsp.toNat + 584) (sdData_val vra0) := by
    rw [hmem2, mem_afterNextPC, hmE1, hoff584]
  have hsl2 : Vsa.Sim.Code.SvfprintfSliceLoaded σ2.mem := by
    rw [hmem2, mem_afterNextPC]
    exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff584]; omega) hsl1
  have hlc2 : Vsa.Sim.Code._localeconv_rLoaded σ2.mem := by
    rw [hmem2, mem_afterNextPC]
    exact localeconv_w8_pro _ _ _ (by rw [hoff584]; omega) hlc1

  -- === 0x8000765c: sd -> sp+24 ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_8000765c_pr σ2 i2 (c.steps + 2) _ vmi2 vsp _
      hG2 hpc2 hmi2 hp2.1 hp2.2.2.2.2.2.2.1 hsl2 rfl (by rw [hoff24]; omega) (by rw [hoff24]; omega) (by rw [hoff24, htoh]; omega) (by rw [hoff24]; omega) hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 2⟩ ⟨σ3, i3, c.steps + 3⟩ := hs3
  have hpc3 : σ3.regs.get? Register.PC = some (0x80007660#64) := by
    have := obs_store_pc hobs3
    rwa [show BitVec.addInt (0x8000765c#64) 4 = (0x80007660#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi3, hmi3⟩ := obs_store_minstret hobs3
  have hp3 := pins_store hobs3 (by rfl) hp2
  have hmE3 : σ3.mem = writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 584) (sdData_val vra0)) (vsp.toNat + 24) (sdData_val vva) := by
    rw [hmem3, mem_afterNextPC, hmE2, hoff24]
  have hsl3 : Vsa.Sim.Code.SvfprintfSliceLoaded σ3.mem := by
    rw [hmem3, mem_afterNextPC]
    exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff24]; omega) hsl2
  have hlc3 : Vsa.Sim.Code._localeconv_rLoaded σ3.mem := by
    rw [hmem3, mem_afterNextPC]
    exact localeconv_w8_pro _ _ _ (by rw [hoff24]; omega) hlc2

  -- === 0x80007660: sd -> sp+8 ===
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80007660_pr σ3 i3 (c.steps + 3) _ vmi3 vsp _
      hG3 hpc3 hmi3 hp3.1 hp3.2.2.2.2.1 hsl3 rfl (by rw [hoff8]; omega) (by rw [hoff8]; omega) (by rw [hoff8, htoh]; omega) (by rw [hoff8]; omega) hi3
  have hstep4 : Step ⟨σ3, i3, c.steps + 3⟩ ⟨σ4, i4, c.steps + 4⟩ := hs4
  have hpc4 : σ4.regs.get? Register.PC = some (0x80007664#64) := by
    have := obs_store_pc hobs4
    rwa [show BitVec.addInt (0x80007660#64) 4 = (0x80007664#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi4, hmi4⟩ := obs_store_minstret hobs4
  have hp4 := pins_store hobs4 (by rfl) hp3
  have hmE4 : σ4.mem = writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 584) (sdData_val vra0)) (vsp.toNat + 24) (sdData_val vva)) (vsp.toNat + 8) (sdData_val vfile) := by
    rw [hmem4, mem_afterNextPC, hmE3, hoff8]
  have hsl4 : Vsa.Sim.Code.SvfprintfSliceLoaded σ4.mem := by
    rw [hmem4, mem_afterNextPC]
    exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff8]; omega) hsl3
  have hlc4 : Vsa.Sim.Code._localeconv_rLoaded σ4.mem := by
    rw [hmem4, mem_afterNextPC]
    exact localeconv_w8_pro _ _ _ (by rw [hoff8]; omega) hlc3

  -- === 0x80007664: sd -> sp+576 ===
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80007664_pr σ4 i4 (c.steps + 4) _ vmi4 vsp _
      hG4 hpc4 hmi4 hp4.1 hp4.2.2.2.2.2.2.2.1 hsl4 rfl (by rw [hoff576]; omega) (by rw [hoff576]; omega) (by rw [hoff576, htoh]; omega) (by rw [hoff576]; omega) hi4
  have hstep5 : Step ⟨σ4, i4, c.steps + 4⟩ ⟨σ5, i5, c.steps + 5⟩ := hs5
  have hpc5 : σ5.regs.get? Register.PC = some (0x80007668#64) := by
    have := obs_store_pc hobs5
    rwa [show BitVec.addInt (0x80007664#64) 4 = (0x80007668#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi5, hmi5⟩ := obs_store_minstret hobs5
  have hp5 := pins_store hobs5 (by rfl) hp4
  have hmE5 : σ5.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 584) (sdData_val vra0)) (vsp.toNat + 24) (sdData_val vva)) (vsp.toNat + 8) (sdData_val vfile)) (vsp.toNat + 576) (sdData_val vS0o) := by
    rw [hmem5, mem_afterNextPC, hmE4, hoff576]
  have hsl5 : Vsa.Sim.Code.SvfprintfSliceLoaded σ5.mem := by
    rw [hmem5, mem_afterNextPC]
    exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff576]; omega) hsl4
  have hlc5 : Vsa.Sim.Code._localeconv_rLoaded σ5.mem := by
    rw [hmem5, mem_afterNextPC]
    exact localeconv_w8_pro _ _ _ (by rw [hoff576]; omega) hlc4

  -- === 0x80007668: sd -> sp+568 ===
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_80007668_pr σ5 i5 (c.steps + 5) _ vmi5 vsp _
      hG5 hpc5 hmi5 hp5.1 hp5.2.2.2.2.2.2.2.2.1 hsl5 rfl (by rw [hoff568]; omega) (by rw [hoff568]; omega) (by rw [hoff568, htoh]; omega) (by rw [hoff568]; omega) hi5
  have hstep6 : Step ⟨σ5, i5, c.steps + 5⟩ ⟨σ6, i6, c.steps + 6⟩ := hs6
  have hpc6 : σ6.regs.get? Register.PC = some (0x8000766c#64) := by
    have := obs_store_pc hobs6
    rwa [show BitVec.addInt (0x80007668#64) 4 = (0x8000766c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi6, hmi6⟩ := obs_store_minstret hobs6
  have hp6 := pins_store hobs6 (by rfl) hp5
  have hmE6 : σ6.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 584) (sdData_val vra0)) (vsp.toNat + 24) (sdData_val vva)) (vsp.toNat + 8) (sdData_val vfile)) (vsp.toNat + 576) (sdData_val vS0o)) (vsp.toNat + 568) (sdData_val vS1o) := by
    rw [hmem6, mem_afterNextPC, hmE5, hoff568]
  have hsl6 : Vsa.Sim.Code.SvfprintfSliceLoaded σ6.mem := by
    rw [hmem6, mem_afterNextPC]
    exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff568]; omega) hsl5
  have hlc6 : Vsa.Sim.Code._localeconv_rLoaded σ6.mem := by
    rw [hmem6, mem_afterNextPC]
    exact localeconv_w8_pro _ _ _ (by rw [hoff568]; omega) hlc5

  -- === 0x8000766c: sd -> sp+528 ===
  obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
    site_8000766c_pr σ6 i6 (c.steps + 6) _ vmi6 vsp _
      hG6 hpc6 hmi6 hp6.1 hp6.2.2.2.2.2.2.2.2.2.1 hsl6 rfl (by rw [hoff528]; omega) (by rw [hoff528]; omega) (by rw [hoff528, htoh]; omega) (by rw [hoff528]; omega) hi6
  have hstep7 : Step ⟨σ6, i6, c.steps + 6⟩ ⟨σ7, i7, c.steps + 7⟩ := hs7
  have hpc7 : σ7.regs.get? Register.PC = some (0x80007670#64) := by
    have := obs_store_pc hobs7
    rwa [show BitVec.addInt (0x8000766c#64) 4 = (0x80007670#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi7, hmi7⟩ := obs_store_minstret hobs7
  have hp7 := pins_store hobs7 (by rfl) hp6
  have hmE7 : σ7.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 584) (sdData_val vra0)) (vsp.toNat + 24) (sdData_val vva)) (vsp.toNat + 8) (sdData_val vfile)) (vsp.toNat + 576) (sdData_val vS0o)) (vsp.toNat + 568) (sdData_val vS1o)) (vsp.toNat + 528) (sdData_val vS6o) := by
    rw [hmem7, mem_afterNextPC, hmE6, hoff528]
  have hsl7 : Vsa.Sim.Code.SvfprintfSliceLoaded σ7.mem := by
    rw [hmem7, mem_afterNextPC]
    exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff528]; omega) hsl6
  have hlc7 : Vsa.Sim.Code._localeconv_rLoaded σ7.mem := by
    rw [hmem7, mem_afterNextPC]
    exact localeconv_w8_pro _ _ _ (by rw [hoff528]; omega) hlc6

  -- === 0x80007670: mv s1,a1 ===
  obtain ⟨σ8, i8, hs8, hi8, hG8, hmem8, hobs8⟩ :=
    site_80007670_pr σ7 i7 (c.steps + 7) _ vmi7 vfile
      hG7 hpc7 hmi7 hp7.2.2.2.2.1 hsl7 rfl hi7
  have hstep8 : Step ⟨σ7, i7, c.steps + 7⟩ ⟨σ8, i8, c.steps + 8⟩ := hs8
  have hpc8 : σ8.regs.get? Register.PC = some (0x80007674#64) := by
    have := obs_alu_pc hobs8
    rwa [show BitVec.addInt (0x80007670#64) 4 = (0x80007674#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi8, hmi8⟩ := obs_alu_minstret hobs8
  have hrd8 : σ8.regs.get? Register.x9 = some (vfile) := by
    have := obs_alu_rd hobs8 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add_pro vfile] at this
  have hp8 := pins_cons_pro hrd8 (pins_alu hobs8 (by rfl) (pins_drop9_pro hp7))
  have hmE8 : σ8.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 584) (sdData_val vra0)) (vsp.toNat + 24) (sdData_val vva)) (vsp.toNat + 8) (sdData_val vfile)) (vsp.toNat + 576) (sdData_val vS0o)) (vsp.toNat + 568) (sdData_val vS1o)) (vsp.toNat + 528) (sdData_val vS6o) := hmem8.trans hmE7
  have hsl8 : Vsa.Sim.Code.SvfprintfSliceLoaded σ8.mem := by rw [hmem8]; exact hsl7
  have hlc8 : Vsa.Sim.Code._localeconv_rLoaded σ8.mem := by rw [hmem8]; exact hlc7

  -- === 0x80007674: mv s6,a2 ===
  obtain ⟨σ9, i9, hs9, hi9, hG9, hmem9, hobs9⟩ :=
    site_80007674_pr σ8 i8 (c.steps + 8) _ vmi8 vfmt
      hG8 hpc8 hmi8 hp8.2.2.2.2.2.2.1 hsl8 rfl hi8
  have hstep9 : Step ⟨σ8, i8, c.steps + 8⟩ ⟨σ9, i9, c.steps + 9⟩ := hs9
  have hpc9 : σ9.regs.get? Register.PC = some (0x80007678#64) := by
    have := obs_alu_pc hobs9
    rwa [show BitVec.addInt (0x80007674#64) 4 = (0x80007678#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi9, hmi9⟩ := obs_alu_minstret hobs9
  have hrd9 : σ9.regs.get? Register.x22 = some (vfmt) := by
    have := obs_alu_rd hobs9 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add_pro vfmt] at this
  have hp9 := pins_cons_pro hrd9 (pins_alu hobs9 (by rfl) (pins_drop10_pro hp8))
  have hmE9 : σ9.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 584) (sdData_val vra0)) (vsp.toNat + 24) (sdData_val vva)) (vsp.toNat + 8) (sdData_val vfile)) (vsp.toNat + 576) (sdData_val vS0o)) (vsp.toNat + 568) (sdData_val vS1o)) (vsp.toNat + 528) (sdData_val vS6o) := hmem9.trans hmE8
  have hsl9 : Vsa.Sim.Code.SvfprintfSliceLoaded σ9.mem := by rw [hmem9]; exact hsl8
  have hlc9 : Vsa.Sim.Code._localeconv_rLoaded σ9.mem := by rw [hmem9]; exact hlc8

  -- === 0x80007678: mv s0,a0 ===
  obtain ⟨σ10, i10, hs10, hi10, hG10, hmem10, hobs10⟩ :=
    site_80007678_pr σ9 i9 (c.steps + 9) _ vmi9 va0
      hG9 hpc9 hmi9 hp9.2.2.2.2.2.1 hsl9 rfl hi9
  have hstep10 : Step ⟨σ9, i9, c.steps + 9⟩ ⟨σ10, i10, c.steps + 10⟩ := hs10
  have hpc10 : σ10.regs.get? Register.PC = some (0x8000767c#64) := by
    have := obs_alu_pc hobs10
    rwa [show BitVec.addInt (0x80007678#64) 4 = (0x8000767c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi10, hmi10⟩ := obs_alu_minstret hobs10
  have hrd10 : σ10.regs.get? Register.x8 = some (va0) := by
    have := obs_alu_rd hobs10 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add_pro va0] at this
  have hp10 := pins_cons_pro hrd10 (pins_alu hobs10 (by rfl) (pins_drop10_pro hp9))
  have hmE10 : σ10.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 584) (sdData_val vra0)) (vsp.toNat + 24) (sdData_val vva)) (vsp.toNat + 8) (sdData_val vfile)) (vsp.toNat + 576) (sdData_val vS0o)) (vsp.toNat + 568) (sdData_val vS1o)) (vsp.toNat + 528) (sdData_val vS6o) := hmem10.trans hmE9
  have hsl10 : Vsa.Sim.Code.SvfprintfSliceLoaded σ10.mem := by rw [hmem10]; exact hsl9
  have hlc10 : Vsa.Sim.Code._localeconv_rLoaded σ10.mem := by rw [hmem10]; exact hlc9

  -- === 0x8000767c: jal _localeconv_r ===
  obtain ⟨σ11, i11, hs11, hi11, hG11, hmem11, hobs11⟩ :=
    site_8000767c_pr σ10 i10 (c.steps + 10) _ vmi10
      hG10 hpc10 hmi10 hsl10 rfl hi10
  have hstep11 : Step ⟨σ10, i10, c.steps + 10⟩ ⟨σ11, i11, c.steps + 11⟩ := hs11
  have hpc11 : σ11.regs.get? Register.PC = some (0x80010258#64) := by
    have := obs_jal_pc hobs11
    rwa [show (0x8000767c#64 : BitVec 64) + sign_extend (m := 64) (0x008bdc#21) = (0x80010258#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi11, hmi11⟩ := obs_jal_minstret hobs11
  have hrd11 : σ11.regs.get? Register.x1 = some ((0x80007680#64)) := by
    have := obs_jal_rd hobs11 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x8000767c#64) 4 = (0x80007680#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp11 := pins_cons_pro hrd11 (pins_jal hobs11 (by rfl) (pins_drop5_pro hp10))
  have hmE11 : σ11.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 584) (sdData_val vra0)) (vsp.toNat + 24) (sdData_val vva)) (vsp.toNat + 8) (sdData_val vfile)) (vsp.toNat + 576) (sdData_val vS0o)) (vsp.toNat + 568) (sdData_val vS1o)) (vsp.toNat + 528) (sdData_val vS6o) := hmem11.trans hmE10
  have hsl11 : Vsa.Sim.Code.SvfprintfSliceLoaded σ11.mem := by rw [hmem11]; exact hsl10
  have hlc11 : Vsa.Sim.Code._localeconv_rLoaded σ11.mem := by rw [hmem11]; exact hlc10

  -- === 0x80010258: addi a0,gp,904 (lconv = 0x8001b898) ===
  obtain ⟨σ12, i12, hs12, hi12, hG12, hmem12, hobs12⟩ :=
    site_80010258_pl σ11 i11 (c.steps + 11) _ vmi11 (0x8001b510#64)
      hG11 hpc11 hmi11 hp11.2.2.2.2.2.1 hlc11 rfl hi11
  have hstep12 : Step ⟨σ11, i11, c.steps + 11⟩ ⟨σ12, i12, c.steps + 12⟩ := hs12
  have hpc12 : σ12.regs.get? Register.PC = some (0x8001025c#64) := by
    have := obs_alu_pc hobs12
    rwa [show BitVec.addInt (0x80010258#64) 4 = (0x8001025c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi12, hmi12⟩ := obs_alu_minstret hobs12
  have hrd12 : σ12.regs.get? Register.x10 = some ((0x8001b898#64)) := by
    have := obs_alu_rd hobs12 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (0x8001b510#64 : BitVec 64) + sign_extend (m := 64) (0x388#12) = (0x8001b898#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp12 := pins_cons_pro hrd12 (pins_alu hobs12 (by rfl) (pins_drop7_pro hp11))
  have hmE12 : σ12.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 584) (sdData_val vra0)) (vsp.toNat + 24) (sdData_val vva)) (vsp.toNat + 8) (sdData_val vfile)) (vsp.toNat + 576) (sdData_val vS0o)) (vsp.toNat + 568) (sdData_val vS1o)) (vsp.toNat + 528) (sdData_val vS6o) := hmem12.trans hmE11
  have hsl12 : Vsa.Sim.Code.SvfprintfSliceLoaded σ12.mem := by rw [hmem12]; exact hsl11
  have hlc12 : Vsa.Sim.Code._localeconv_rLoaded σ12.mem := by rw [hmem12]; exact hlc11

  -- === 0x8001025c: ret (back to 0x80007680) ===
  obtain ⟨σ13, i13, hs13, hi13, hG13, hmem13, hobs13⟩ :=
    site_8001025c_pl σ12 i12 (c.steps + 12) _ vmi12 (0x80007680#64)
      hG12 hpc12 hmi12 hp12.2.1 hlc12 rfl (by rw [ret_tgt _ (by decide)]; decide) hi12
  have hstep13 : Step ⟨σ12, i12, c.steps + 12⟩ ⟨σ13, i13, c.steps + 13⟩ := hs13
  have hpc13 : σ13.regs.get? Register.PC = some (0x80007680#64) := by
    have := obs_jr_pc hobs13
    rwa [ret_tgt _ (by decide)] at this
  obtain ⟨vmi13, hmi13⟩ := obs_jr_minstret hobs13
  have hp13 := pins_jr hobs13 (by rfl) hp12
  have hmE13 : σ13.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 584) (sdData_val vra0)) (vsp.toNat + 24) (sdData_val vva)) (vsp.toNat + 8) (sdData_val vfile)) (vsp.toNat + 576) (sdData_val vS0o)) (vsp.toNat + 568) (sdData_val vS1o)) (vsp.toNat + 528) (sdData_val vS6o) := hmem13.trans hmE12
  have hsl13 : Vsa.Sim.Code.SvfprintfSliceLoaded σ13.mem := by rw [hmem13]; exact hsl12
  have hlc13 : Vsa.Sim.Code._localeconv_rLoaded σ13.mem := by rw [hmem13]; exact hlc12

  -- agreement below the frame after the six spills (all keys ≥ vsp)
  have hag13 : ∀ a : Nat, a < vsp.toNat → σ13.mem[a]? = c.σ.mem[a]? := by
    intro a ha
    rw [hmE13,
      getElem?_writeMap8_out _ (vsp.toNat + 528) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 568) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 576) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 8) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 24) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 584) _ a (by omega)]

  -- === 0x80007680: ld a4,0(a0) — decimal_point = 0x80019770 ===
  obtain ⟨σ14, i14, hs14, hi14, hG14, hmem14, hobs14⟩ :=
    site_80007680_pr σ13 i13 (c.steps + 13) _ vmi13 (0x8001b898#64) _ _ _ _ _ _ _ _
      hG13 hpc13 hmi13 hp13.1 hsl13 rfl (by rw [hoffdp]; omega) (by rw [hoffdp]; omega) (by rw [hoffdp, htoh]; omega) (by rw [hoffdp]) (by rw [hoffdp]; exact (hag13 _ (by omega)).trans hdp0) (by rw [hoffdp]; exact (hag13 _ (by omega)).trans hdp1) (by rw [hoffdp]; exact (hag13 _ (by omega)).trans hdp2) (by rw [hoffdp]; exact (hag13 _ (by omega)).trans hdp3) (by rw [hoffdp]; exact (hag13 _ (by omega)).trans hdp4) (by rw [hoffdp]; exact (hag13 _ (by omega)).trans hdp5) (by rw [hoffdp]; exact (hag13 _ (by omega)).trans hdp6) (by rw [hoffdp]; exact (hag13 _ (by omega)).trans hdp7) hi13
  have hstep14 : Step ⟨σ13, i13, c.steps + 13⟩ ⟨σ14, i14, c.steps + 14⟩ := hs14
  have hpc14 : σ14.regs.get? Register.PC = some (0x80007684#64) := by
    have := obs_alu_pc hobs14
    rwa [show BitVec.addInt (0x80007680#64) 4 = (0x80007684#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi14, hmi14⟩ := obs_alu_minstret hobs14
  have hrd14 : σ14.regs.get? Register.x14 = some ((0x80019770#64)) := by
    have := obs_alu_rd hobs14 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (sign_extend (m := 64) (((((((((0x00#8).append (0x00#8)).append (0x00#8)).append (0x00#8)).append (0x80#8)).append (0x01#8)).append (0x97#8)).append (0x70#8)) : BitVec (8 * 8)) : BitVec 64) = (0x80019770#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp14 := pins_cons_pro hrd14 (pins_alu hobs14 (by rfl) hp13)
  have hmE14 : σ14.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 584) (sdData_val vra0)) (vsp.toNat + 24) (sdData_val vva)) (vsp.toNat + 8) (sdData_val vfile)) (vsp.toNat + 576) (sdData_val vS0o)) (vsp.toNat + 568) (sdData_val vS1o)) (vsp.toNat + 528) (sdData_val vS6o) := hmem14.trans hmE13
  have hsl14 : Vsa.Sim.Code.SvfprintfSliceLoaded σ14.mem := by rw [hmem14]; exact hsl13
  have hlc14 : Vsa.Sim.Code._localeconv_rLoaded σ14.mem := by rw [hmem14]; exact hlc13

  -- === 0x80007684: mv a0,a4 ===
  obtain ⟨σ15, i15, hs15, hi15, hG15, hmem15, hobs15⟩ :=
    site_80007684_pr σ14 i14 (c.steps + 14) _ vmi14 (0x80019770#64)
      hG14 hpc14 hmi14 hp14.1 hsl14 rfl hi14
  have hstep15 : Step ⟨σ14, i14, c.steps + 14⟩ ⟨σ15, i15, c.steps + 15⟩ := hs15
  have hpc15 : σ15.regs.get? Register.PC = some (0x80007688#64) := by
    have := obs_alu_pc hobs15
    rwa [show BitVec.addInt (0x80007684#64) 4 = (0x80007688#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi15, hmi15⟩ := obs_alu_minstret hobs15
  have hrd15 : σ15.regs.get? Register.x10 = some ((0x80019770#64)) := by
    have := obs_alu_rd hobs15 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add_pro (0x80019770#64)] at this
  have hp15 := pins_cons_pro hrd15 (pins_alu hobs15 (by rfl) (pins_drop2_pro hp14))
  have hmE15 : σ15.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 584) (sdData_val vra0)) (vsp.toNat + 24) (sdData_val vva)) (vsp.toNat + 8) (sdData_val vfile)) (vsp.toNat + 576) (sdData_val vS0o)) (vsp.toNat + 568) (sdData_val vS1o)) (vsp.toNat + 528) (sdData_val vS6o) := hmem15.trans hmE14
  have hsl15 : Vsa.Sim.Code.SvfprintfSliceLoaded σ15.mem := by rw [hmem15]; exact hsl14
  have hlc15 : Vsa.Sim.Code._localeconv_rLoaded σ15.mem := by rw [hmem15]; exact hlc14

  -- === 0x80007688: sd a4,80(sp) — lconv decimal_point spill ===
  obtain ⟨σ16, i16, hs16, hi16, hG16, hmem16, hobs16⟩ :=
    site_80007688_pr σ15 i15 (c.steps + 15) _ vmi15 vsp _
      hG15 hpc15 hmi15 hp15.2.2.2.2.2.2.1 hp15.2.1 hsl15 rfl (by rw [hoff80]; omega) (by rw [hoff80]; omega) (by rw [hoff80, htoh]; omega) (by rw [hoff80]; omega) hi15
  have hstep16 : Step ⟨σ15, i15, c.steps + 15⟩ ⟨σ16, i16, c.steps + 16⟩ := hs16
  have hpc16 : σ16.regs.get? Register.PC = some (0x8000768c#64) := by
    have := obs_store_pc hobs16
    rwa [show BitVec.addInt (0x80007688#64) 4 = (0x8000768c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi16, hmi16⟩ := obs_store_minstret hobs16
  have hp16 := pins_store hobs16 (by rfl) hp15
  have hmE16 : σ16.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 584) (sdData_val vra0)) (vsp.toNat + 24) (sdData_val vva)) (vsp.toNat + 8) (sdData_val vfile)) (vsp.toNat + 576) (sdData_val vS0o)) (vsp.toNat + 568) (sdData_val vS1o)) (vsp.toNat + 528) (sdData_val vS6o)) (vsp.toNat + 80) (sdData_val (0x80019770#64)) := by
    rw [hmem16, mem_afterNextPC, hmE15, hoff80]
  have hsl16 : Vsa.Sim.Code.SvfprintfSliceLoaded σ16.mem := by
    rw [hmem16, mem_afterNextPC]
    exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff80]; omega) hsl15
  have hlc16 : Vsa.Sim.Code._localeconv_rLoaded σ16.mem := by
    rw [hmem16, mem_afterNextPC]
    exact localeconv_w8_pro _ _ _ (by rw [hoff80]; omega) hlc15

  -- exported Loaded predicates for the later segments
  have hstrlN : Vsa.Sim.Code.StrlenLoaded σ16.mem := by
    rw [hmE16]
    exact strlen_w8_pro _ _ _ (by omega) (strlen_w8_pro _ _ _ (by omega)
      (strlen_w8_pro _ _ _ (by omega) (strlen_w8_pro _ _ _ (by omega)
      (strlen_w8_pro _ _ _ (by omega) (strlen_w8_pro _ _ _ (by omega)
      (strlen_w8_pro _ _ _ (by omega) hstrl))))))
  have hmsN : Vsa.Sim.Code.MemsetLoaded σ16.mem := by
    rw [hmE16]
    exact memset_w8_pro _ _ _ (by omega) (memset_w8_pro _ _ _ (by omega)
      (memset_w8_pro _ _ _ (by omega) (memset_w8_pro _ _ _ (by omega)
      (memset_w8_pro _ _ _ (by omega) (memset_w8_pro _ _ _ (by omega)
      (memset_w8_pro _ _ _ (by omega) hms))))))
  have hlmN : Vsa.Sim.Code.__locale_mb_cur_maxLoaded σ16.mem := by
    rw [hmE16]
    exact localemb_w8_pro _ _ _ (by omega) (localemb_w8_pro _ _ _ (by omega)
      (localemb_w8_pro _ _ _ (by omega) (localemb_w8_pro _ _ _ (by omega)
      (localemb_w8_pro _ _ _ (by omega) (localemb_w8_pro _ _ _ (by omega)
      (localemb_w8_pro _ _ _ (by omega) hlm))))))
  have hambN : Vsa.Sim.Code.__ascii_mbtowcLoaded σ16.mem := by
    rw [hmE16]
    exact amb_w8_pro _ _ _ (by omega) (amb_w8_pro _ _ _ (by omega)
      (amb_w8_pro _ _ _ (by omega) (amb_w8_pro _ _ _ (by omega)
      (amb_w8_pro _ _ _ (by omega) (amb_w8_pro _ _ _ (by omega)
      (amb_w8_pro _ _ _ (by omega) hamb))))))
  have hS248 : SlotHolds vsp 0x248 vra0 σ16.mem := by
    rw [hmE16]
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff584]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff584]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff584]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff584]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff584]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff584]; omega) ?_
    exact slot_save vsp 0x248 vra0 _ _ _ hoff584 rfl
  have hS018 : SlotHolds vsp 0x018 vva σ16.mem := by
    rw [hmE16]
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff24]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff24]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff24]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff24]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff24]; omega) ?_
    exact slot_save vsp 0x018 vva _ _ _ hoff24 rfl
  have hS008 : SlotHolds vsp 0x008 vfile σ16.mem := by
    rw [hmE16]
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff8]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff8]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff8]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff8]; omega) ?_
    exact slot_save vsp 0x008 vfile _ _ _ hoff8 rfl
  have hS240 : SlotHolds vsp 0x240 vS0o σ16.mem := by
    rw [hmE16]
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff576]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff576]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff576]; omega) ?_
    exact slot_save vsp 0x240 vS0o _ _ _ hoff576 rfl
  have hS238 : SlotHolds vsp 0x238 vS1o σ16.mem := by
    rw [hmE16]
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff568]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff568]; omega) ?_
    exact slot_save vsp 0x238 vS1o _ _ _ hoff568 rfl
  have hS210 : SlotHolds vsp 0x210 vS6o σ16.mem := by
    rw [hmE16]
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff528]; omega) ?_
    exact slot_save vsp 0x210 vS6o _ _ _ hoff528 rfl
  have hS050 : SlotHolds vsp 0x050 (0x80019770#64) σ16.mem := by
    rw [hmE16]
    exact slot_save vsp 0x050 (0x80019770#64) _ _ _ hoff80 rfl
  have hagN : ∀ a : Nat, ¬(vsp.toNat + 584 ≤ a ∧ a < vsp.toNat + 592) →
      ¬(vsp.toNat + 24 ≤ a ∧ a < vsp.toNat + 32) →
      ¬(vsp.toNat + 8 ≤ a ∧ a < vsp.toNat + 16) →
      ¬(vsp.toNat + 576 ≤ a ∧ a < vsp.toNat + 584) →
      ¬(vsp.toNat + 568 ≤ a ∧ a < vsp.toNat + 576) →
      ¬(vsp.toNat + 528 ≤ a ∧ a < vsp.toNat + 536) →
      ¬(vsp.toNat + 80 ≤ a ∧ a < vsp.toNat + 88) →
      σ16.mem[a]? = c.σ.mem[a]? := by
    intro a hw0 hw1 hw2 hw3 hw4 hw5 hw6
    rw [hmE16,
      getElem?_writeMap8_out _ (vsp.toNat + 80) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 528) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 568) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 576) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 8) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 24) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 584) _ a (by omega)]
  refine ⟨⟨σ16, i16, c.steps + 16⟩, ?_,
    hG16,
    hpc16,
    hp16.2.2.2.2.2.2.1,
    hp16.2.2.1,
    hp16.2.2.2.2.2.2.2.1,
    hp16.2.2.2.1,
    hp16.2.2.2.2.2.1,
    hp16.2.2.2.2.1,
    hp16.1,
    hp16.2.1,
    hp16.2.2.2.2.2.2.2.2.2.1,
    hp16.2.2.2.2.2.2.2.2.2.2.1,
    hp16.2.2.2.2.2.2.2.2.2.2.2.1,
    hp16.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp16.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp16.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp16.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp16.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp16.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp16.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp16.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hS248,
    hS018,
    hS008,
    hS240,
    hS238,
    hS210,
    hS050,
    hagN,
    hsl16,
    hlc16,
    hstrlN,
    hmsN,
    hlmN,
    hambN,
    hi16,
    ⟨vmi16, hmi16⟩⟩
  exact (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans ((Steps.single hstep4).trans ((Steps.single hstep5).trans ((Steps.single hstep6).trans ((Steps.single hstep7).trans ((Steps.single hstep8).trans ((Steps.single hstep9).trans ((Steps.single hstep10).trans ((Steps.single hstep11).trans ((Steps.single hstep12).trans ((Steps.single hstep13).trans ((Steps.single hstep14).trans ((Steps.single hstep15).trans (Steps.single hstep16)))))))))))))))

end Vsa.Sim
