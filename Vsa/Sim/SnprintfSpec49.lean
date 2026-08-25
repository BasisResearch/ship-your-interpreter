import Vsa.Sim.SnprintfSpec17
import Vsa.Sim.SnprintfSpec43
import Vsa.Sim.SnprintfSitesPrint
import Vsa.Sim.SnprintfSitesPrint2
import Vsa.Sim.SnprintfSitesFast2

/-!
# M3 Layer-3 — `SnprintfSpec49` : the 1-iovec PRINT segment (nonneg arm)

`printToSsprintNN_spec`: from the PRINT-macro entry `0x8000782c` (where
`entryToPrintNN_any_spec`, Spec48, lands with the sign slot `0x00`) to the
completed `jal __ssprint_r` (`PC = 0x8000e908`, `ra = 0x80008688`).  The
`bnez` at `0x80007ce0` reads the CLEARED sign byte and is NOT taken — no
sign iovec is built; the single (digit) iovec entry is written at the iov
cursor `s7 = viov` (count `vcnt → vcnt+1`, cursor `vcur → vcur+len`).
The shared call tail from `0x80007908` is `iov2Tail_spec` (Spec17),
consumed with `vsel := vlen` (the `bge t3,a6` NOT-taken arm).

Emitted by `scripts/pro_emitter/gen_spec49.py`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (SvfprintfSliceLoaded FlushPinsLoaded ArmPinsLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- **PRINT entry → `__ssprint_r` call, 1-iovec (nonneg) arm**
(`0x8000782c → 0x8000e908`, 35 steps incl. the Spec17 tail). -/
theorem printToSsprintNN_spec
    (vsp vt1 vt3 vlen vs6 v20 v8 viov vbase vcur vtot vstr : BitVec 64)
    (vcnt : BitVec 32)
    (c : Config)
    (hG : GoodState c.σ)
    (hload : SvfprintfSliceLoaded c.σ.mem)
    (hfp : FlushPinsLoaded c.σ.mem)
    (hap : ArmPinsLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x8000782c#64))
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx6 : c.σ.regs.get? Register.x6 = some vt1)
    (hx8 : c.σ.regs.get? Register.x8 = some v8)
    (hx16 : c.σ.regs.get? Register.x16 = some vlen)
    (hx20 : c.σ.regs.get? Register.x20 = some v20)
    (hx22 : c.σ.regs.get? Register.x22 = some vs6)
    (hx23 : c.σ.regs.get? Register.x23 = some viov)
    (hx26 : c.σ.regs.get? Register.x26 = some vbase)
    (hx28 : c.σ.regs.get? Register.x28 = some vt3)
    -- FILE fields + the cleared sign byte
    (hcur : SlotHolds vsp 0x0f0 vcur c.σ.mem)
    (hcnt0 : c.σ.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat]? = some (vcnt.extractLsb' 0 8))
    (hcnt1 : c.σ.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 1]? = some (vcnt.extractLsb' 8 8))
    (hcnt2 : c.σ.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 2]? = some (vcnt.extractLsb' 16 8))
    (hcnt3 : c.σ.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 3]? = some (vcnt.extractLsb' 24 8))
    (hz167 : c.σ.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some (0x00#8))
    (htot : SlotHolds vsp 0x010 vtot c.σ.mem)
    (hstr : SlotHolds vsp 0x008 vstr c.σ.mem)
    -- branch guards (nonneg-%lld path, upstream provenance)
    (hflag84 : vt1 &&& sign_extend (m := 64) (0x084#12) = 0#64)
    (hflag256 : vt1 &&& sign_extend (m := 64) (0x100#12) = 0#64)
    (hflag4z : vt1 &&& sign_extend (m := 64) (0x004#12) = 0#64)
    (hpad : zopz0zI_s (0#64) (sign_extend (m := 64) ((Sail.BitVec.extractLsb vt3 31 0) - (Sail.BitVec.extractLsb vlen 31 0))) = false)
    (hprec : zopz0zKzJ_s (0#64) (sign_extend (m := 64) ((Sail.BitVec.extractLsb v20 31 0) - (Sail.BitVec.extractLsb vs6 31 0))) = true)
    (hcntlt : zopz0zI_s (0x7#64) (sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0)) = false)
    (hwlen : zopz0zKzJ_s vt3 vlen = false)
    (hvc2 : ((vcur + vs6) != (0#64)) = true)
    -- layout
    (hspwin : tohostAddr + 16 + 64 ≤ vsp.toNat)
    (hsphi : vsp.toNat + 356 ≤ 0x100000000)
    (hspalign : vsp.toNat % 8 = 0)
    (hiovwin : tohostAddr + 16 ≤ viov.toNat)
    (hiovhi : viov.toNat + 16 ≤ 0x100000000)
    (hiovalign : viov.toNat % 8 = 0)
    (hiovsep : vsp.toNat + 24 ≤ viov.toNat)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x8000e908#64) ∧
      c'.σ.regs.get? Register.x1 = some (0x80008688#64) ∧
      c'.σ.regs.get? Register.x10 = some v8 ∧
      c'.σ.regs.get? Register.x11 = some vstr ∧
      c'.σ.regs.get? Register.x12 = some (vsp + sign_extend (m := 64) (0x0e0#12)) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.σ.regs.get? Register.x5 = some (0#64) ∧
      c'.σ.regs.get? Register.x6 = some (0#64) ∧
      c'.σ.regs.get? Register.x8 = some v8 ∧
      c'.σ.regs.get? Register.x16 = some vlen ∧
      c'.σ.regs.get? Register.x20 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb v20 31 0) - (Sail.BitVec.extractLsb vs6 31 0))) ∧
      c'.σ.regs.get? Register.x22 = some vs6 ∧
      c'.σ.regs.get? Register.x23 = some (viov + sign_extend (m := 64) (0x010#12)) ∧
      c'.σ.regs.get? Register.x26 = some vbase ∧
      c'.σ.regs.get? Register.x28 = some vt3 ∧
      c'.σ.mem = writeMap8
        (writeMap4
          (writeMap8
            (writeMap8
              (writeMap8 c.σ.mem
                ((vsp + sign_extend (m := 64) (0x0f0#12)).toNat) (sdData_val (vcur + vs6)))
              ((viov + sign_extend (m := 64) (0x000#12)).toNat) (sdData_val vbase))
            ((viov + sign_extend (m := 64) (0x008#12)).toNat) (sdData_val vs6))
          ((vsp + sign_extend (m := 64) (0x0e8#12)).toNat)
            (swData (sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0))))
        ((vsp + sign_extend (m := 64) (0x010#12)).toNat)
          (sdData_val (sign_extend (m := 64)
            (Sail.BitVec.extractLsb vlen 31 0 + Sail.BitVec.extractLsb vtot 31 0))) ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) ∧
      KeepRegs midRegs5 c.σ c'.σ := by
  have htohv : tohostAddr = 0x8001ad00 := rfl
  have hnw : vsp.toNat + 348 < 2 ^ 64 := by omega
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
  have hoff240 : (vsp + sign_extend (m := 64) (0x0f0#12)).toNat = vsp.toNat + 240 :=
    addoff_toNat_sn5 vsp (0x0f0#12) 240 (by omega) (by decide) hnw
  have hoff232 : (vsp + sign_extend (m := 64) (0x0e8#12)).toNat = vsp.toNat + 232 :=
    addoff_toNat_sn5 vsp (0x0e8#12) 232 (by omega) (by decide) hnw
  have hoff167 : (vsp + sign_extend (m := 64) (0x0a7#12)).toNat = vsp.toNat + 167 :=
    addoff_toNat_sn5 vsp (0x0a7#12) 167 (by omega) (by decide) hnw
  have hoff16 : (vsp + sign_extend (m := 64) (0x010#12)).toNat = vsp.toNat + 16 :=
    addoff_toNat_sn5 vsp (0x010#12) 16 (by omega) (by decide) hnw
  have hoff8 : (vsp + sign_extend (m := 64) (0x008#12)).toNat = vsp.toNat + 8 :=
    addoff_toNat_sn5 vsp (0x008#12) 8 (by omega) (by decide) hnw
  have hoffiov0 : (viov + sign_extend (m := 64) (0x000#12)).toNat = viov.toNat :=
    addoff_toNat_sn5 viov (0x000#12) 0 (by omega) (by decide) (by omega)
  have hoffiov8 : (viov + sign_extend (m := 64) (0x008#12)).toNat = viov.toNat + 8 :=
    addoff_toNat_sn5 viov (0x008#12) 8 (by omega) (by decide) (by omega)
  -- step-0 aliases
  have hx2_0 := hx2
  have hx6_0 := hx6
  have hx8_0 := hx8
  have hx16_0 := hx16
  have hx20_0 := hx20
  have hx22_0 := hx22
  have hx23_0 := hx23
  have hx26_0 := hx26
  have hx28_0 := hx28
  have hload0 : SvfprintfSliceLoaded c.σ.mem := hload
  have hfp0 : FlushPinsLoaded c.σ.mem := hfp
  have hap0 : ArmPinsLoaded c.σ.mem := hap
  obtain ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7⟩ := hcur

  -- === 0x8000782c: ld a2,240(sp) — the running cursor ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_8000782c_pv c.σ c.tick (c.steps) (0x8000782c#64) vmi0 vsp ((sdData_val vcur).extractLsb' 0 8) ((sdData_val vcur).extractLsb' 8 8) ((sdData_val vcur).extractLsb' 16 8) ((sdData_val vcur).extractLsb' 24 8) ((sdData_val vcur).extractLsb' 32 8) ((sdData_val vcur).extractLsb' 40 8) ((sdData_val vcur).extractLsb' 48 8) ((sdData_val vcur).extractLsb' 56 8)
      hG hpc hmi0 hx2_0 hload0 rfl (by rw [hoff240]; omega) (by rw [hoff240]; omega) (Or.inr (by rw [hoff240]; omega)) (by rw [hoff240]; omega) hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 htick
  have hstep1 : Step c ⟨σ1, i1, c.steps+1⟩ := by cases c; exact hs1
  have hpc1 : σ1.regs.get? Register.PC = some (0x80007830#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x8000782c#64 : BitVec 64) 4 = (0x80007830#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hx12_1 : σ1.regs.get? Register.x12 = some (sign_extend (m := 64) (((((((((sdData_val vcur).extractLsb' 56 8).append ((sdData_val vcur).extractLsb' 48 8)).append ((sdData_val vcur).extractLsb' 40 8)).append ((sdData_val vcur).extractLsb' 32 8)).append ((sdData_val vcur).extractLsb' 24 8)).append ((sdData_val vcur).extractLsb' 16 8)).append ((sdData_val vcur).extractLsb' 8 8)).append ((sdData_val vcur).extractLsb' 0 8) : BitVec (8 * 8))) :=
    obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [ve_sext_reassemble vcur] at hx12_1
  have hx2_1 : σ1.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_0
  have hx6_1 : σ1.regs.get? Register.x6 = some vt1 :=
    obs_alu_other hobs1 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_0
  have hx8_1 : σ1.regs.get? Register.x8 = some v8 :=
    obs_alu_other hobs1 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_0
  have hx16_1 : σ1.regs.get? Register.x16 = some vlen :=
    obs_alu_other hobs1 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_0
  have hx20_1 : σ1.regs.get? Register.x20 = some v20 :=
    obs_alu_other hobs1 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_0
  have hx22_1 : σ1.regs.get? Register.x22 = some vs6 :=
    obs_alu_other hobs1 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_0
  have hx23_1 : σ1.regs.get? Register.x23 = some viov :=
    obs_alu_other hobs1 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_0
  have hx26_1 : σ1.regs.get? Register.x26 = some vbase :=
    obs_alu_other hobs1 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_0
  have hx28_1 : σ1.regs.get? Register.x28 = some vt3 :=
    obs_alu_other hobs1 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_0
  have hmE1 : σ1.mem = c.σ.mem := hmem1
  have hload1 : SvfprintfSliceLoaded σ1.mem := hmem1 ▸ hload0
  have hfp1 : FlushPinsLoaded σ1.mem := hmem1 ▸ hfp0
  have hap1 : ArmPinsLoaded σ1.mem := hmem1 ▸ hap0

  -- === 0x80007830: andi t0,t1,132 — flags & 0x84 = 0 ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80007830_pv σ1 i1 (c.steps+1) (0x80007830#64) vmi1 vt1
      hG1 hpc1 hmi1 hx6_1 hload1 rfl hi1
  have hstep2 : Step ⟨σ1,i1,c.steps+1⟩ ⟨σ2,i2,c.steps+1+1⟩ := hs2
  have hpc2 : σ2.regs.get? Register.PC = some (0x80007834#64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x80007830#64 : BitVec 64) 4 = (0x80007834#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hx5_2 : σ2.regs.get? Register.x5 = some (vt1 &&& sign_extend (m := 64) (0x084#12)) :=
    obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [hflag84] at hx5_2
  have hx2_2 : σ2.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs2 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_1
  have hx6_2 : σ2.regs.get? Register.x6 = some vt1 :=
    obs_alu_other hobs2 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_1
  have hx8_2 : σ2.regs.get? Register.x8 = some v8 :=
    obs_alu_other hobs2 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_1
  have hx16_2 : σ2.regs.get? Register.x16 = some vlen :=
    obs_alu_other hobs2 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_1
  have hx20_2 : σ2.regs.get? Register.x20 = some v20 :=
    obs_alu_other hobs2 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_1
  have hx22_2 : σ2.regs.get? Register.x22 = some vs6 :=
    obs_alu_other hobs2 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_1
  have hx23_2 : σ2.regs.get? Register.x23 = some viov :=
    obs_alu_other hobs2 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_1
  have hx26_2 : σ2.regs.get? Register.x26 = some vbase :=
    obs_alu_other hobs2 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_1
  have hx28_2 : σ2.regs.get? Register.x28 = some vt3 :=
    obs_alu_other hobs2 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_1
  have hx12_2 : σ2.regs.get? Register.x12 = some vcur :=
    obs_alu_other hobs2 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_1
  have hmE2 : σ2.mem = c.σ.mem := hmem2.trans hmE1
  have hload2 : SvfprintfSliceLoaded σ2.mem := hmem2 ▸ hload1
  have hfp2 : FlushPinsLoaded σ2.mem := hmem2 ▸ hfp1
  have hap2 : ArmPinsLoaded σ2.mem := hmem2 ▸ hap1

  -- === 0x80007834: mv a0,a2 ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80007834_pv σ2 i2 (c.steps+1+1) (0x80007834#64) vmi2 vcur
      hG2 hpc2 hmi2 hx12_2 hload2 rfl hi2
  have hstep3 : Step ⟨σ2,i2,c.steps+1+1⟩ ⟨σ3,i3,c.steps+1+1+1⟩ := hs3
  have hpc3 : σ3.regs.get? Register.PC = some (0x80007838#64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x80007834#64 : BitVec 64) 4 = (0x80007838#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hx10_3 : σ3.regs.get? Register.x10 = some (vcur + sign_extend (m := 64) (0x000#12)) :=
    obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx2_3 : σ3.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs3 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_2
  have hx6_3 : σ3.regs.get? Register.x6 = some vt1 :=
    obs_alu_other hobs3 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_2
  have hx8_3 : σ3.regs.get? Register.x8 = some v8 :=
    obs_alu_other hobs3 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_2
  have hx16_3 : σ3.regs.get? Register.x16 = some vlen :=
    obs_alu_other hobs3 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_2
  have hx20_3 : σ3.regs.get? Register.x20 = some v20 :=
    obs_alu_other hobs3 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_2
  have hx22_3 : σ3.regs.get? Register.x22 = some vs6 :=
    obs_alu_other hobs3 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_2
  have hx23_3 : σ3.regs.get? Register.x23 = some viov :=
    obs_alu_other hobs3 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_2
  have hx26_3 : σ3.regs.get? Register.x26 = some vbase :=
    obs_alu_other hobs3 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_2
  have hx28_3 : σ3.regs.get? Register.x28 = some vt3 :=
    obs_alu_other hobs3 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_2
  have hx12_3 : σ3.regs.get? Register.x12 = some vcur :=
    obs_alu_other hobs3 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_2
  have hx5_3 : σ3.regs.get? Register.x5 = some (0#64) :=
    obs_alu_other hobs3 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_2
  have hmE3 : σ3.mem = c.σ.mem := hmem3.trans hmE2
  have hload3 : SvfprintfSliceLoaded σ3.mem := hmem3 ▸ hload2
  have hfp3 : FlushPinsLoaded σ3.mem := hmem3 ▸ hfp2
  have hap3 : ArmPinsLoaded σ3.mem := hmem3 ▸ hap2

  -- === 0x80007838: beqz t0 TAKEN (no adjust flags) ===
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80007838_taken_pv σ3 i3 (c.steps+1+1+1) (0x80007838#64) vmi3 (0#64)
      hG3 hpc3 hmi3 hx5_3 hload3 rfl (by decide) hi3
  have hstep4 : Step ⟨σ3,i3,c.steps+1+1+1⟩ ⟨σ4,i4,c.steps+1+1+1+1⟩ := hs4
  have hpc4 : σ4.regs.get? Register.PC = some (0x80007cd4#64) := by
    have := obs_btaken_pc hobs4
    rwa [site_80007838_taken_pv_tgt] at this
  obtain ⟨vmi4, hmi4⟩ := obs_btaken_minstret hobs4
  have hx2_4 : σ4.regs.get? Register.x2 = some vsp :=
    obs_btaken_other hobs4 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_3
  have hx6_4 : σ4.regs.get? Register.x6 = some vt1 :=
    obs_btaken_other hobs4 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_3
  have hx8_4 : σ4.regs.get? Register.x8 = some v8 :=
    obs_btaken_other hobs4 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_3
  have hx16_4 : σ4.regs.get? Register.x16 = some vlen :=
    obs_btaken_other hobs4 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_3
  have hx20_4 : σ4.regs.get? Register.x20 = some v20 :=
    obs_btaken_other hobs4 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_3
  have hx22_4 : σ4.regs.get? Register.x22 = some vs6 :=
    obs_btaken_other hobs4 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_3
  have hx23_4 : σ4.regs.get? Register.x23 = some viov :=
    obs_btaken_other hobs4 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_3
  have hx26_4 : σ4.regs.get? Register.x26 = some vbase :=
    obs_btaken_other hobs4 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_3
  have hx28_4 : σ4.regs.get? Register.x28 = some vt3 :=
    obs_btaken_other hobs4 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_3
  have hx12_4 : σ4.regs.get? Register.x12 = some vcur :=
    obs_btaken_other hobs4 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_3
  have hx5_4 : σ4.regs.get? Register.x5 = some (0#64) :=
    obs_btaken_other hobs4 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_3
  have hmE4 : σ4.mem = c.σ.mem := hmem4.trans hmE3
  have hload4 : SvfprintfSliceLoaded σ4.mem := hmem4 ▸ hload3
  have hfp4 : FlushPinsLoaded σ4.mem := hmem4 ▸ hfp3
  have hap4 : ArmPinsLoaded σ4.mem := hmem4 ▸ hap3

  -- === 0x80007cd4: subw a4,t3,a6 — pad count (≤ 0) ===
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80007cd4_pv2 σ4 i4 (c.steps+1+1+1+1) (0x80007cd4#64) vmi4 vt3 vlen
      hG4 hpc4 hmi4 hx28_4 hx16_4 hfp4 rfl hi4
  have hstep5 : Step ⟨σ4,i4,c.steps+1+1+1+1⟩ ⟨σ5,i5,c.steps+1+1+1+1+1⟩ := hs5
  have hpc5 : σ5.regs.get? Register.PC = some (0x80007cd8#64) := by
    have := obs_alu_pc hobs5
    rwa [show BitVec.addInt (0x80007cd4#64 : BitVec 64) 4 = (0x80007cd8#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi5, hmi5⟩ := obs_alu_minstret hobs5
  have hx14_5 : σ5.regs.get? Register.x14 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb vt3 31 0) - (Sail.BitVec.extractLsb vlen 31 0))) :=
    obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx2_5 : σ5.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs5 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_4
  have hx6_5 : σ5.regs.get? Register.x6 = some vt1 :=
    obs_alu_other hobs5 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_4
  have hx8_5 : σ5.regs.get? Register.x8 = some v8 :=
    obs_alu_other hobs5 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_4
  have hx16_5 : σ5.regs.get? Register.x16 = some vlen :=
    obs_alu_other hobs5 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_4
  have hx20_5 : σ5.regs.get? Register.x20 = some v20 :=
    obs_alu_other hobs5 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_4
  have hx22_5 : σ5.regs.get? Register.x22 = some vs6 :=
    obs_alu_other hobs5 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_4
  have hx23_5 : σ5.regs.get? Register.x23 = some viov :=
    obs_alu_other hobs5 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_4
  have hx26_5 : σ5.regs.get? Register.x26 = some vbase :=
    obs_alu_other hobs5 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_4
  have hx28_5 : σ5.regs.get? Register.x28 = some vt3 :=
    obs_alu_other hobs5 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_4
  have hx12_5 : σ5.regs.get? Register.x12 = some vcur :=
    obs_alu_other hobs5 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_4
  have hx5_5 : σ5.regs.get? Register.x5 = some (0#64) :=
    obs_alu_other hobs5 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_4
  have hmE5 : σ5.mem = c.σ.mem := hmem5.trans hmE4
  have hload5 : SvfprintfSliceLoaded σ5.mem := hmem5 ▸ hload4
  have hfp5 : FlushPinsLoaded σ5.mem := hmem5 ▸ hfp4
  have hap5 : ArmPinsLoaded σ5.mem := hmem5 ▸ hap4

  -- === 0x80007cd8: bgtz a4 NOT taken (no left pad) ===
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_80007cd8_nottaken_pv2 σ5 i5 (c.steps+1+1+1+1+1) (0x80007cd8#64) vmi5 (sign_extend (m := 64) ((Sail.BitVec.extractLsb vt3 31 0) - (Sail.BitVec.extractLsb vlen 31 0)))
      hG5 hpc5 hmi5 hx14_5 hfp5 rfl hpad hi5
  have hstep6 : Step ⟨σ5,i5,c.steps+1+1+1+1+1⟩ ⟨σ6,i6,c.steps+1+1+1+1+1+1⟩ := hs6
  have hpc6 : σ6.regs.get? Register.PC = some (0x80007cdc#64) := by
    have := obs_bnottaken_pc hobs6
    rwa [show BitVec.addInt (0x80007cd8#64 : BitVec 64) 4 = (0x80007cdc#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi6, hmi6⟩ := obs_bnottaken_minstret hobs6
  have hx2_6 : σ6.regs.get? Register.x2 = some vsp :=
    obs_bnottaken_other hobs6 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_5
  have hx6_6 : σ6.regs.get? Register.x6 = some vt1 :=
    obs_bnottaken_other hobs6 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_5
  have hx8_6 : σ6.regs.get? Register.x8 = some v8 :=
    obs_bnottaken_other hobs6 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_5
  have hx16_6 : σ6.regs.get? Register.x16 = some vlen :=
    obs_bnottaken_other hobs6 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_5
  have hx20_6 : σ6.regs.get? Register.x20 = some v20 :=
    obs_bnottaken_other hobs6 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_5
  have hx22_6 : σ6.regs.get? Register.x22 = some vs6 :=
    obs_bnottaken_other hobs6 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_5
  have hx23_6 : σ6.regs.get? Register.x23 = some viov :=
    obs_bnottaken_other hobs6 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_5
  have hx26_6 : σ6.regs.get? Register.x26 = some vbase :=
    obs_bnottaken_other hobs6 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_5
  have hx28_6 : σ6.regs.get? Register.x28 = some vt3 :=
    obs_bnottaken_other hobs6 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_5
  have hx12_6 : σ6.regs.get? Register.x12 = some vcur :=
    obs_bnottaken_other hobs6 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_5
  have hx5_6 : σ6.regs.get? Register.x5 = some (0#64) :=
    obs_bnottaken_other hobs6 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_5
  have hx14_6 : σ6.regs.get? Register.x14 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb vt3 31 0) - (Sail.BitVec.extractLsb vlen 31 0))) :=
    obs_bnottaken_other hobs6 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_5
  have hmE6 : σ6.mem = c.σ.mem := hmem6.trans hmE5
  have hload6 : SvfprintfSliceLoaded σ6.mem := hmem6 ▸ hload5
  have hfp6 : FlushPinsLoaded σ6.mem := hmem6 ▸ hfp5
  have hap6 : ArmPinsLoaded σ6.mem := hmem6 ▸ hap5

  have hz167_6 : σ6.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some (0x00#8) := by
    rw [hmE6]; exact hz167
  -- === 0x80007cdc: lbu a4,167(sp) — reads 0x00 (no sign) ===
  obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
    site_80007cdc_pv2 σ6 i6 (c.steps+1+1+1+1+1+1) (0x80007cdc#64) vmi6 vsp (0x00#8)
      hG6 hpc6 hmi6 hx2_6 hfp6 rfl (by rw [hoff167]; omega) (by rw [hoff167]; omega) (Or.inr (by rw [hoff167]; omega)) hz167_6 hi6
  have hstep7 : Step ⟨σ6,i6,c.steps+1+1+1+1+1+1⟩ ⟨σ7,i7,c.steps+1+1+1+1+1+1+1⟩ := hs7
  have hpc7 : σ7.regs.get? Register.PC = some (0x80007ce0#64) := by
    have := obs_alu_pc hobs7
    rwa [show BitVec.addInt (0x80007cdc#64 : BitVec 64) 4 = (0x80007ce0#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi7, hmi7⟩ := obs_alu_minstret hobs7
  have hx14_7 : σ7.regs.get? Register.x14 = some (zero_extend (m := 64) (0x00#8)) :=
    obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [show (zero_extend (m := 64) (0x00#8) : BitVec 64) = (0#64) from by decide] at hx14_7
  have hx2_7 : σ7.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs7 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_6
  have hx6_7 : σ7.regs.get? Register.x6 = some vt1 :=
    obs_alu_other hobs7 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_6
  have hx8_7 : σ7.regs.get? Register.x8 = some v8 :=
    obs_alu_other hobs7 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_6
  have hx16_7 : σ7.regs.get? Register.x16 = some vlen :=
    obs_alu_other hobs7 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_6
  have hx20_7 : σ7.regs.get? Register.x20 = some v20 :=
    obs_alu_other hobs7 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_6
  have hx22_7 : σ7.regs.get? Register.x22 = some vs6 :=
    obs_alu_other hobs7 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_6
  have hx23_7 : σ7.regs.get? Register.x23 = some viov :=
    obs_alu_other hobs7 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_6
  have hx26_7 : σ7.regs.get? Register.x26 = some vbase :=
    obs_alu_other hobs7 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_6
  have hx28_7 : σ7.regs.get? Register.x28 = some vt3 :=
    obs_alu_other hobs7 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_6
  have hx12_7 : σ7.regs.get? Register.x12 = some vcur :=
    obs_alu_other hobs7 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_6
  have hx5_7 : σ7.regs.get? Register.x5 = some (0#64) :=
    obs_alu_other hobs7 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_6
  have hmE7 : σ7.mem = c.σ.mem := hmem7.trans hmE6
  have hload7 : SvfprintfSliceLoaded σ7.mem := hmem7 ▸ hload6
  have hfp7 : FlushPinsLoaded σ7.mem := hmem7 ▸ hfp6
  have hap7 : ArmPinsLoaded σ7.mem := hmem7 ▸ hap6

  -- === 0x80007ce0: bnez a4 NOT taken — NO sign iovec ===
  obtain ⟨σ8, i8, hs8, hi8, hG8, hmem8, hobs8⟩ :=
    site_80007ce0_nottaken_pv2 σ7 i7 (c.steps+1+1+1+1+1+1+1) (0x80007ce0#64) vmi7 (0#64)
      hG7 hpc7 hmi7 hx14_7 hfp7 rfl (by decide) hi7
  have hstep8 : Step ⟨σ7,i7,c.steps+1+1+1+1+1+1+1⟩ ⟨σ8,i8,c.steps+1+1+1+1+1+1+1+1⟩ := hs8
  have hpc8 : σ8.regs.get? Register.PC = some (0x80007ce4#64) := by
    have := obs_bnottaken_pc hobs8
    rwa [show BitVec.addInt (0x80007ce0#64 : BitVec 64) 4 = (0x80007ce4#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi8, hmi8⟩ := obs_bnottaken_minstret hobs8
  have hx2_8 : σ8.regs.get? Register.x2 = some vsp :=
    obs_bnottaken_other hobs8 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_7
  have hx6_8 : σ8.regs.get? Register.x6 = some vt1 :=
    obs_bnottaken_other hobs8 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_7
  have hx8_8 : σ8.regs.get? Register.x8 = some v8 :=
    obs_bnottaken_other hobs8 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_7
  have hx16_8 : σ8.regs.get? Register.x16 = some vlen :=
    obs_bnottaken_other hobs8 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_7
  have hx20_8 : σ8.regs.get? Register.x20 = some v20 :=
    obs_bnottaken_other hobs8 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_7
  have hx22_8 : σ8.regs.get? Register.x22 = some vs6 :=
    obs_bnottaken_other hobs8 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_7
  have hx23_8 : σ8.regs.get? Register.x23 = some viov :=
    obs_bnottaken_other hobs8 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_7
  have hx26_8 : σ8.regs.get? Register.x26 = some vbase :=
    obs_bnottaken_other hobs8 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_7
  have hx28_8 : σ8.regs.get? Register.x28 = some vt3 :=
    obs_bnottaken_other hobs8 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_7
  have hx12_8 : σ8.regs.get? Register.x12 = some vcur :=
    obs_bnottaken_other hobs8 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_7
  have hx5_8 : σ8.regs.get? Register.x5 = some (0#64) :=
    obs_bnottaken_other hobs8 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_7
  have hx14_8 : σ8.regs.get? Register.x14 = some (0#64) :=
    obs_bnottaken_other hobs8 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_7
  have hmE8 : σ8.mem = c.σ.mem := hmem8.trans hmE7
  have hload8 : SvfprintfSliceLoaded σ8.mem := hmem8 ▸ hload7
  have hfp8 : FlushPinsLoaded σ8.mem := hmem8 ▸ hfp7
  have hap8 : ArmPinsLoaded σ8.mem := hmem8 ▸ hap7

  -- === 0x80007ce4: subw s4,s4,s6 — precision − len ===
  obtain ⟨σ9, i9, hs9, hi9, hG9, hmem9, hobs9⟩ :=
    site_80007ce4_fs2 σ8 i8 (c.steps+1+1+1+1+1+1+1+1) (0x80007ce4#64) vmi8 v20 vs6
      hG8 hpc8 hmi8 hx20_8 hx22_8 hap8 rfl hi8
  have hstep9 : Step ⟨σ8,i8,c.steps+1+1+1+1+1+1+1+1⟩ ⟨σ9,i9,c.steps+1+1+1+1+1+1+1+1+1⟩ := hs9
  have hpc9 : σ9.regs.get? Register.PC = some (0x80007ce8#64) := by
    have := obs_alu_pc hobs9
    rwa [show BitVec.addInt (0x80007ce4#64 : BitVec 64) 4 = (0x80007ce8#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi9, hmi9⟩ := obs_alu_minstret hobs9
  have hx20_9 : σ9.regs.get? Register.x20 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb v20 31 0) - (Sail.BitVec.extractLsb vs6 31 0))) :=
    obs_alu_rd hobs9 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx2_9 : σ9.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs9 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_8
  have hx6_9 : σ9.regs.get? Register.x6 = some vt1 :=
    obs_alu_other hobs9 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_8
  have hx8_9 : σ9.regs.get? Register.x8 = some v8 :=
    obs_alu_other hobs9 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_8
  have hx16_9 : σ9.regs.get? Register.x16 = some vlen :=
    obs_alu_other hobs9 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_8
  have hx22_9 : σ9.regs.get? Register.x22 = some vs6 :=
    obs_alu_other hobs9 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_8
  have hx23_9 : σ9.regs.get? Register.x23 = some viov :=
    obs_alu_other hobs9 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_8
  have hx26_9 : σ9.regs.get? Register.x26 = some vbase :=
    obs_alu_other hobs9 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_8
  have hx28_9 : σ9.regs.get? Register.x28 = some vt3 :=
    obs_alu_other hobs9 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_8
  have hx12_9 : σ9.regs.get? Register.x12 = some vcur :=
    obs_alu_other hobs9 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_8
  have hx5_9 : σ9.regs.get? Register.x5 = some (0#64) :=
    obs_alu_other hobs9 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_8
  have hx14_9 : σ9.regs.get? Register.x14 = some (0#64) :=
    obs_alu_other hobs9 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_8
  have hmE9 : σ9.mem = c.σ.mem := hmem9.trans hmE8
  have hload9 : SvfprintfSliceLoaded σ9.mem := hmem9 ▸ hload8
  have hfp9 : FlushPinsLoaded σ9.mem := hmem9 ▸ hfp8
  have hap9 : ArmPinsLoaded σ9.mem := hmem9 ▸ hap8

  -- === 0x80007ce8: blez s4 TAKEN → the iovec fill ===
  obtain ⟨σ10, i10, hs10, hi10, hG10, hmem10, hobs10⟩ :=
    site_80007ce8_taken_fs2 σ9 i9 (c.steps+1+1+1+1+1+1+1+1+1) (0x80007ce8#64) vmi9 (sign_extend (m := 64) ((Sail.BitVec.extractLsb v20 31 0) - (Sail.BitVec.extractLsb vs6 31 0)))
      hG9 hpc9 hmi9 hx20_9 hap9 rfl hprec hi9
  have hstep10 : Step ⟨σ9,i9,c.steps+1+1+1+1+1+1+1+1+1⟩ ⟨σ10,i10,c.steps+1+1+1+1+1+1+1+1+1+1⟩ := hs10
  have hpc10 : σ10.regs.get? Register.PC = some (0x800078bc#64) := by
    have := obs_btaken_pc hobs10
    rwa [site_80007ce8_taken_fs2_tgt] at this
  obtain ⟨vmi10, hmi10⟩ := obs_btaken_minstret hobs10
  have hx2_10 : σ10.regs.get? Register.x2 = some vsp :=
    obs_btaken_other hobs10 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_9
  have hx6_10 : σ10.regs.get? Register.x6 = some vt1 :=
    obs_btaken_other hobs10 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_9
  have hx8_10 : σ10.regs.get? Register.x8 = some v8 :=
    obs_btaken_other hobs10 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_9
  have hx16_10 : σ10.regs.get? Register.x16 = some vlen :=
    obs_btaken_other hobs10 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_9
  have hx20_10 : σ10.regs.get? Register.x20 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb v20 31 0) - (Sail.BitVec.extractLsb vs6 31 0))) :=
    obs_btaken_other hobs10 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_9
  have hx22_10 : σ10.regs.get? Register.x22 = some vs6 :=
    obs_btaken_other hobs10 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_9
  have hx23_10 : σ10.regs.get? Register.x23 = some viov :=
    obs_btaken_other hobs10 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_9
  have hx26_10 : σ10.regs.get? Register.x26 = some vbase :=
    obs_btaken_other hobs10 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_9
  have hx28_10 : σ10.regs.get? Register.x28 = some vt3 :=
    obs_btaken_other hobs10 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_9
  have hx12_10 : σ10.regs.get? Register.x12 = some vcur :=
    obs_btaken_other hobs10 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_9
  have hx5_10 : σ10.regs.get? Register.x5 = some (0#64) :=
    obs_btaken_other hobs10 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_9
  have hx14_10 : σ10.regs.get? Register.x14 = some (0#64) :=
    obs_btaken_other hobs10 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_9
  have hmE10 : σ10.mem = c.σ.mem := hmem10.trans hmE9
  have hload10 : SvfprintfSliceLoaded σ10.mem := hmem10 ▸ hload9
  have hfp10 : FlushPinsLoaded σ10.mem := hmem10 ▸ hfp9
  have hap10 : ArmPinsLoaded σ10.mem := hmem10 ▸ hap9

  -- === 0x800078bc: andi a4,t1,256 — flags & 0x100 = 0 ===
  obtain ⟨σ11, i11, hs11, hi11, hG11, hmem11, hobs11⟩ :=
    site_800078bc_pv σ10 i10 (c.steps+1+1+1+1+1+1+1+1+1+1) (0x800078bc#64) vmi10 vt1
      hG10 hpc10 hmi10 hx6_10 hload10 rfl hi10
  have hstep11 : Step ⟨σ10,i10,c.steps+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ11,i11,c.steps+1+1+1+1+1+1+1+1+1+1+1⟩ := hs11
  have hpc11 : σ11.regs.get? Register.PC = some (0x800078c0#64) := by
    have := obs_alu_pc hobs11
    rwa [show BitVec.addInt (0x800078bc#64 : BitVec 64) 4 = (0x800078c0#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi11, hmi11⟩ := obs_alu_minstret hobs11
  have hx14_11 : σ11.regs.get? Register.x14 = some (vt1 &&& sign_extend (m := 64) (0x100#12)) :=
    obs_alu_rd hobs11 (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [hflag256] at hx14_11
  have hx2_11 : σ11.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs11 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_10
  have hx6_11 : σ11.regs.get? Register.x6 = some vt1 :=
    obs_alu_other hobs11 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_10
  have hx8_11 : σ11.regs.get? Register.x8 = some v8 :=
    obs_alu_other hobs11 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_10
  have hx16_11 : σ11.regs.get? Register.x16 = some vlen :=
    obs_alu_other hobs11 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_10
  have hx20_11 : σ11.regs.get? Register.x20 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb v20 31 0) - (Sail.BitVec.extractLsb vs6 31 0))) :=
    obs_alu_other hobs11 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_10
  have hx22_11 : σ11.regs.get? Register.x22 = some vs6 :=
    obs_alu_other hobs11 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_10
  have hx23_11 : σ11.regs.get? Register.x23 = some viov :=
    obs_alu_other hobs11 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_10
  have hx26_11 : σ11.regs.get? Register.x26 = some vbase :=
    obs_alu_other hobs11 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_10
  have hx28_11 : σ11.regs.get? Register.x28 = some vt3 :=
    obs_alu_other hobs11 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_10
  have hx12_11 : σ11.regs.get? Register.x12 = some vcur :=
    obs_alu_other hobs11 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_10
  have hx5_11 : σ11.regs.get? Register.x5 = some (0#64) :=
    obs_alu_other hobs11 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_10
  have hmE11 : σ11.mem = c.σ.mem := hmem11.trans hmE10
  have hload11 : SvfprintfSliceLoaded σ11.mem := hmem11 ▸ hload10
  have hfp11 : FlushPinsLoaded σ11.mem := hmem11 ▸ hfp10
  have hap11 : ArmPinsLoaded σ11.mem := hmem11 ▸ hap10

  -- === 0x800078c0: bnez a4 NOT taken ===
  obtain ⟨σ12, i12, hs12, hi12, hG12, hmem12, hobs12⟩ :=
    site_800078c0_nottaken_pv σ11 i11 (c.steps+1+1+1+1+1+1+1+1+1+1+1) (0x800078c0#64) vmi11 (0#64)
      hG11 hpc11 hmi11 hx14_11 hload11 rfl (by decide) hi11
  have hstep12 : Step ⟨σ11,i11,c.steps+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ12,i12,c.steps+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs12
  have hpc12 : σ12.regs.get? Register.PC = some (0x800078c4#64) := by
    have := obs_bnottaken_pc hobs12
    rwa [show BitVec.addInt (0x800078c0#64 : BitVec 64) 4 = (0x800078c4#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi12, hmi12⟩ := obs_bnottaken_minstret hobs12
  have hx2_12 : σ12.regs.get? Register.x2 = some vsp :=
    obs_bnottaken_other hobs12 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_11
  have hx6_12 : σ12.regs.get? Register.x6 = some vt1 :=
    obs_bnottaken_other hobs12 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_11
  have hx8_12 : σ12.regs.get? Register.x8 = some v8 :=
    obs_bnottaken_other hobs12 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_11
  have hx16_12 : σ12.regs.get? Register.x16 = some vlen :=
    obs_bnottaken_other hobs12 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_11
  have hx20_12 : σ12.regs.get? Register.x20 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb v20 31 0) - (Sail.BitVec.extractLsb vs6 31 0))) :=
    obs_bnottaken_other hobs12 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_11
  have hx22_12 : σ12.regs.get? Register.x22 = some vs6 :=
    obs_bnottaken_other hobs12 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_11
  have hx23_12 : σ12.regs.get? Register.x23 = some viov :=
    obs_bnottaken_other hobs12 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_11
  have hx26_12 : σ12.regs.get? Register.x26 = some vbase :=
    obs_bnottaken_other hobs12 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_11
  have hx28_12 : σ12.regs.get? Register.x28 = some vt3 :=
    obs_bnottaken_other hobs12 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_11
  have hx12_12 : σ12.regs.get? Register.x12 = some vcur :=
    obs_bnottaken_other hobs12 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_11
  have hx5_12 : σ12.regs.get? Register.x5 = some (0#64) :=
    obs_bnottaken_other hobs12 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_11
  have hx14_12 : σ12.regs.get? Register.x14 = some (0#64) :=
    obs_bnottaken_other hobs12 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_11
  have hmE12 : σ12.mem = c.σ.mem := hmem12.trans hmE11
  have hload12 : SvfprintfSliceLoaded σ12.mem := hmem12 ▸ hload11
  have hfp12 : FlushPinsLoaded σ12.mem := hmem12 ▸ hfp11
  have hap12 : ArmPinsLoaded σ12.mem := hmem12 ▸ hap11

  have hcnt0_12 : σ12.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat]? = some (vcnt.extractLsb' 0 8) := by
    rw [hmE12]; exact hcnt0
  have hcnt1_12 : σ12.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 1]? = some (vcnt.extractLsb' 8 8) := by
    rw [hmE12]; exact hcnt1
  have hcnt2_12 : σ12.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 2]? = some (vcnt.extractLsb' 16 8) := by
    rw [hmE12]; exact hcnt2
  have hcnt3_12 : σ12.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 3]? = some (vcnt.extractLsb' 24 8) := by
    rw [hmE12]; exact hcnt3
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
  -- === 0x800078c4: lw a5,232(sp) — the iov count ===
  obtain ⟨σ13, i13, hs13, hi13, hG13, hmem13, hobs13⟩ :=
    site_800078c4_pv σ12 i12 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1) (0x800078c4#64) vmi12 vsp (vcnt.extractLsb' 0 8) (vcnt.extractLsb' 8 8) (vcnt.extractLsb' 16 8) (vcnt.extractLsb' 24 8)
      hG12 hpc12 hmi12 hx2_12 hload12 rfl (by rw [hoff232]; omega) (by rw [hoff232]; omega) (Or.inr (by rw [hoff232]; omega)) (by rw [hoff232]; omega) hcnt0_12 hcnt1_12 hcnt2_12 hcnt3_12 hi12
  have hstep13 : Step ⟨σ12,i12,c.steps+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ13,i13,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs13
  have hpc13 : σ13.regs.get? Register.PC = some (0x800078c8#64) := by
    have := obs_alu_pc hobs13
    rwa [show BitVec.addInt (0x800078c4#64 : BitVec 64) 4 = (0x800078c8#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi13, hmi13⟩ := obs_alu_minstret hobs13
  have hx15_13 : σ13.regs.get? Register.x15 = some (sign_extend (m := 64) ((((vcnt.extractLsb' 24 8).append (vcnt.extractLsb' 16 8)).append (vcnt.extractLsb' 8 8)).append (vcnt.extractLsb' 0 8) : BitVec (8 * 4))) :=
    obs_alu_rd hobs13 (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [hlwval] at hx15_13
  have hx2_13 : σ13.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs13 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_12
  have hx6_13 : σ13.regs.get? Register.x6 = some vt1 :=
    obs_alu_other hobs13 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_12
  have hx8_13 : σ13.regs.get? Register.x8 = some v8 :=
    obs_alu_other hobs13 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_12
  have hx16_13 : σ13.regs.get? Register.x16 = some vlen :=
    obs_alu_other hobs13 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_12
  have hx20_13 : σ13.regs.get? Register.x20 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb v20 31 0) - (Sail.BitVec.extractLsb vs6 31 0))) :=
    obs_alu_other hobs13 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_12
  have hx22_13 : σ13.regs.get? Register.x22 = some vs6 :=
    obs_alu_other hobs13 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_12
  have hx23_13 : σ13.regs.get? Register.x23 = some viov :=
    obs_alu_other hobs13 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_12
  have hx26_13 : σ13.regs.get? Register.x26 = some vbase :=
    obs_alu_other hobs13 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_12
  have hx28_13 : σ13.regs.get? Register.x28 = some vt3 :=
    obs_alu_other hobs13 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_12
  have hx12_13 : σ13.regs.get? Register.x12 = some vcur :=
    obs_alu_other hobs13 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_12
  have hx5_13 : σ13.regs.get? Register.x5 = some (0#64) :=
    obs_alu_other hobs13 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_12
  have hx14_13 : σ13.regs.get? Register.x14 = some (0#64) :=
    obs_alu_other hobs13 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_12
  have hmE13 : σ13.mem = c.σ.mem := hmem13.trans hmE12
  have hload13 : SvfprintfSliceLoaded σ13.mem := hmem13 ▸ hload12
  have hfp13 : FlushPinsLoaded σ13.mem := hmem13 ▸ hfp12
  have hap13 : ArmPinsLoaded σ13.mem := hmem13 ▸ hap12

  -- === 0x800078c8: add a2,a2,s6 — cursor + len ===
  obtain ⟨σ14, i14, hs14, hi14, hG14, hmem14, hobs14⟩ :=
    site_800078c8_pv σ13 i13 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x800078c8#64) vmi13 vcur vs6
      hG13 hpc13 hmi13 hx12_13 hx22_13 hload13 rfl hi13
  have hstep14 : Step ⟨σ13,i13,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ14,i14,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs14
  have hpc14 : σ14.regs.get? Register.PC = some (0x800078cc#64) := by
    have := obs_alu_pc hobs14
    rwa [show BitVec.addInt (0x800078c8#64 : BitVec 64) 4 = (0x800078cc#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi14, hmi14⟩ := obs_alu_minstret hobs14
  have hx12_14 : σ14.regs.get? Register.x12 = some (vcur + vs6) :=
    obs_alu_rd hobs14 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx2_14 : σ14.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs14 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_13
  have hx6_14 : σ14.regs.get? Register.x6 = some vt1 :=
    obs_alu_other hobs14 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_13
  have hx8_14 : σ14.regs.get? Register.x8 = some v8 :=
    obs_alu_other hobs14 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_13
  have hx16_14 : σ14.regs.get? Register.x16 = some vlen :=
    obs_alu_other hobs14 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_13
  have hx20_14 : σ14.regs.get? Register.x20 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb v20 31 0) - (Sail.BitVec.extractLsb vs6 31 0))) :=
    obs_alu_other hobs14 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_13
  have hx22_14 : σ14.regs.get? Register.x22 = some vs6 :=
    obs_alu_other hobs14 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_13
  have hx23_14 : σ14.regs.get? Register.x23 = some viov :=
    obs_alu_other hobs14 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_13
  have hx26_14 : σ14.regs.get? Register.x26 = some vbase :=
    obs_alu_other hobs14 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_13
  have hx28_14 : σ14.regs.get? Register.x28 = some vt3 :=
    obs_alu_other hobs14 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_13
  have hx5_14 : σ14.regs.get? Register.x5 = some (0#64) :=
    obs_alu_other hobs14 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_13
  have hx14_14 : σ14.regs.get? Register.x14 = some (0#64) :=
    obs_alu_other hobs14 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_13
  have hx15_14 : σ14.regs.get? Register.x15 = some (sign_extend (m := 64) vcnt : BitVec 64) :=
    obs_alu_other hobs14 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_13
  have hmE14 : σ14.mem = c.σ.mem := hmem14.trans hmE13
  have hload14 : SvfprintfSliceLoaded σ14.mem := hmem14 ▸ hload13
  have hfp14 : FlushPinsLoaded σ14.mem := hmem14 ▸ hfp13
  have hap14 : ArmPinsLoaded σ14.mem := hmem14 ▸ hap13

  -- === 0x800078cc: sd a2,240(sp) — the bumped cursor ===
  obtain ⟨σ15, i15, hs15, hi15, hG15, hmem15, hobs15⟩ :=
    site_800078cc_pv σ14 i14 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x800078cc#64) vmi14 vsp (vcur + vs6)
      hG14 hpc14 hmi14 hx2_14 hx12_14 hload14 rfl (by rw [hoff240]; omega) (by rw [hoff240]; omega) (by rw [hoff240]; omega) (by rw [hoff240]; omega) hi14
  have hstep15 : Step ⟨σ14,i14,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ15,i15,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs15
  have hpc15 : σ15.regs.get? Register.PC = some (0x800078d0#64) := by
    have := obs_store_pc_sn4 hobs15
    rwa [show BitVec.addInt (0x800078cc#64 : BitVec 64) 4 = (0x800078d0#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi15, hmi15⟩ := obs_store_minstret_sn4 hobs15
  have hx2_15 : σ15.regs.get? Register.x2 = some vsp :=
    obs_store_other_sn4 Register.x2 hobs15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_14
  have hx6_15 : σ15.regs.get? Register.x6 = some vt1 :=
    obs_store_other_sn4 Register.x6 hobs15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_14
  have hx8_15 : σ15.regs.get? Register.x8 = some v8 :=
    obs_store_other_sn4 Register.x8 hobs15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_14
  have hx16_15 : σ15.regs.get? Register.x16 = some vlen :=
    obs_store_other_sn4 Register.x16 hobs15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_14
  have hx20_15 : σ15.regs.get? Register.x20 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb v20 31 0) - (Sail.BitVec.extractLsb vs6 31 0))) :=
    obs_store_other_sn4 Register.x20 hobs15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_14
  have hx22_15 : σ15.regs.get? Register.x22 = some vs6 :=
    obs_store_other_sn4 Register.x22 hobs15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_14
  have hx23_15 : σ15.regs.get? Register.x23 = some viov :=
    obs_store_other_sn4 Register.x23 hobs15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_14
  have hx26_15 : σ15.regs.get? Register.x26 = some vbase :=
    obs_store_other_sn4 Register.x26 hobs15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_14
  have hx28_15 : σ15.regs.get? Register.x28 = some vt3 :=
    obs_store_other_sn4 Register.x28 hobs15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_14
  have hx12_15 : σ15.regs.get? Register.x12 = some (vcur + vs6) :=
    obs_store_other_sn4 Register.x12 hobs15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_14
  have hx5_15 : σ15.regs.get? Register.x5 = some (0#64) :=
    obs_store_other_sn4 Register.x5 hobs15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_14
  have hx14_15 : σ15.regs.get? Register.x14 = some (0#64) :=
    obs_store_other_sn4 Register.x14 hobs15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_14
  have hx15_15 : σ15.regs.get? Register.x15 = some (sign_extend (m := 64) vcnt : BitVec 64) :=
    obs_store_other_sn4 Register.x15 hobs15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_14
  have hNP14b : (afterNextPC (afterPrelude σ14) (0x800078cc#64)).mem = σ14.mem := rfl
  have hmE15 : σ15.mem = writeMap8 (c.σ.mem) ((vsp + sign_extend (m := 64) (0x0f0#12)).toNat) (sdData_val (vcur + vs6)) := by
    rw [hmem15, hNP14b, hmE14]
  have hload15 : SvfprintfSliceLoaded σ15.mem := by
    rw [hmem15, hNP14b]; exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff240]; omega) hload14
  have hfp15 : FlushPinsLoaded σ15.mem := by
    rw [hmem15, hNP14b]; exact flushPins_writeMap8_fl _ _ _ (by rw [hoff240]; omega) hfp14
  have hap15 : ArmPinsLoaded σ15.mem := by
    rw [hmem15, hNP14b]; exact armPins_writeMap8_43 _ _ _ (by rw [hoff240]; omega) hap14

  -- === 0x800078d0: addiw a5,a5,1 — count + 1 ===
  obtain ⟨σ16, i16, hs16, hi16, hG16, hmem16, hobs16⟩ :=
    site_800078d0_pv σ15 i15 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x800078d0#64) vmi15 (sign_extend (m := 64) vcnt : BitVec 64)
      hG15 hpc15 hmi15 hx15_15 hload15 rfl hi15
  have hstep16 : Step ⟨σ15,i15,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ16,i16,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs16
  have hpc16 : σ16.regs.get? Register.PC = some (0x800078d4#64) := by
    have := obs_alu_pc hobs16
    rwa [show BitVec.addInt (0x800078d0#64 : BitVec 64) 4 = (0x800078d4#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi16, hmi16⟩ := obs_alu_minstret hobs16
  have hx15_16 : σ16.regs.get? Register.x15 = some (sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0)) :=
    obs_alu_rd hobs16 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx2_16 : σ16.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs16 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_15
  have hx6_16 : σ16.regs.get? Register.x6 = some vt1 :=
    obs_alu_other hobs16 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_15
  have hx8_16 : σ16.regs.get? Register.x8 = some v8 :=
    obs_alu_other hobs16 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_15
  have hx16_16 : σ16.regs.get? Register.x16 = some vlen :=
    obs_alu_other hobs16 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_15
  have hx20_16 : σ16.regs.get? Register.x20 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb v20 31 0) - (Sail.BitVec.extractLsb vs6 31 0))) :=
    obs_alu_other hobs16 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_15
  have hx22_16 : σ16.regs.get? Register.x22 = some vs6 :=
    obs_alu_other hobs16 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_15
  have hx23_16 : σ16.regs.get? Register.x23 = some viov :=
    obs_alu_other hobs16 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_15
  have hx26_16 : σ16.regs.get? Register.x26 = some vbase :=
    obs_alu_other hobs16 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_15
  have hx28_16 : σ16.regs.get? Register.x28 = some vt3 :=
    obs_alu_other hobs16 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_15
  have hx12_16 : σ16.regs.get? Register.x12 = some (vcur + vs6) :=
    obs_alu_other hobs16 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_15
  have hx5_16 : σ16.regs.get? Register.x5 = some (0#64) :=
    obs_alu_other hobs16 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_15
  have hx14_16 : σ16.regs.get? Register.x14 = some (0#64) :=
    obs_alu_other hobs16 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_15
  have hmE16 : σ16.mem = writeMap8 (c.σ.mem) ((vsp + sign_extend (m := 64) (0x0f0#12)).toNat) (sdData_val (vcur + vs6)) := hmem16.trans hmE15
  have hload16 : SvfprintfSliceLoaded σ16.mem := hmem16 ▸ hload15
  have hfp16 : FlushPinsLoaded σ16.mem := hmem16 ▸ hfp15
  have hap16 : ArmPinsLoaded σ16.mem := hmem16 ▸ hap15

  -- === 0x800078d4: sd s10,0(s7) — iov[0].iov_base := digit base ===
  obtain ⟨σ17, i17, hs17, hi17, hG17, hmem17, hobs17⟩ :=
    site_800078d4_pv σ16 i16 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x800078d4#64) vmi16 viov vbase
      hG16 hpc16 hmi16 hx23_16 hx26_16 hload16 rfl (by rw [hoffiov0]; omega) (by rw [hoffiov0]; omega) (by rw [hoffiov0]; omega) (by rw [hoffiov0]; omega) hi16
  have hstep17 : Step ⟨σ16,i16,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ17,i17,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs17
  have hpc17 : σ17.regs.get? Register.PC = some (0x800078d8#64) := by
    have := obs_store_pc_sn4 hobs17
    rwa [show BitVec.addInt (0x800078d4#64 : BitVec 64) 4 = (0x800078d8#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi17, hmi17⟩ := obs_store_minstret_sn4 hobs17
  have hx2_17 : σ17.regs.get? Register.x2 = some vsp :=
    obs_store_other_sn4 Register.x2 hobs17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_16
  have hx6_17 : σ17.regs.get? Register.x6 = some vt1 :=
    obs_store_other_sn4 Register.x6 hobs17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_16
  have hx8_17 : σ17.regs.get? Register.x8 = some v8 :=
    obs_store_other_sn4 Register.x8 hobs17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_16
  have hx16_17 : σ17.regs.get? Register.x16 = some vlen :=
    obs_store_other_sn4 Register.x16 hobs17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_16
  have hx20_17 : σ17.regs.get? Register.x20 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb v20 31 0) - (Sail.BitVec.extractLsb vs6 31 0))) :=
    obs_store_other_sn4 Register.x20 hobs17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_16
  have hx22_17 : σ17.regs.get? Register.x22 = some vs6 :=
    obs_store_other_sn4 Register.x22 hobs17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_16
  have hx23_17 : σ17.regs.get? Register.x23 = some viov :=
    obs_store_other_sn4 Register.x23 hobs17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_16
  have hx26_17 : σ17.regs.get? Register.x26 = some vbase :=
    obs_store_other_sn4 Register.x26 hobs17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_16
  have hx28_17 : σ17.regs.get? Register.x28 = some vt3 :=
    obs_store_other_sn4 Register.x28 hobs17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_16
  have hx12_17 : σ17.regs.get? Register.x12 = some (vcur + vs6) :=
    obs_store_other_sn4 Register.x12 hobs17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_16
  have hx5_17 : σ17.regs.get? Register.x5 = some (0#64) :=
    obs_store_other_sn4 Register.x5 hobs17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_16
  have hx14_17 : σ17.regs.get? Register.x14 = some (0#64) :=
    obs_store_other_sn4 Register.x14 hobs17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_16
  have hx15_17 : σ17.regs.get? Register.x15 = some (sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0)) :=
    obs_store_other_sn4 Register.x15 hobs17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_16
  have hNP16b : (afterNextPC (afterPrelude σ16) (0x800078d4#64)).mem = σ16.mem := rfl
  have hmE17 : σ17.mem = writeMap8 (writeMap8 (c.σ.mem) ((vsp + sign_extend (m := 64) (0x0f0#12)).toNat) (sdData_val (vcur + vs6))) ((viov + sign_extend (m := 64) (0x000#12)).toNat) (sdData_val vbase) := by
    rw [hmem17, hNP16b, hmE16]
  have hload17 : SvfprintfSliceLoaded σ17.mem := by
    rw [hmem17, hNP16b]; exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoffiov0]; omega) hload16
  have hfp17 : FlushPinsLoaded σ17.mem := by
    rw [hmem17, hNP16b]; exact flushPins_writeMap8_fl _ _ _ (by rw [hoffiov0]; omega) hfp16
  have hap17 : ArmPinsLoaded σ17.mem := by
    rw [hmem17, hNP16b]; exact armPins_writeMap8_43 _ _ _ (by rw [hoffiov0]; omega) hap16

  -- === 0x800078d8: sd s6,8(s7) — iov[0].iov_len := len ===
  obtain ⟨σ18, i18, hs18, hi18, hG18, hmem18, hobs18⟩ :=
    site_800078d8_pv σ17 i17 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x800078d8#64) vmi17 viov vs6
      hG17 hpc17 hmi17 hx23_17 hx22_17 hload17 rfl (by rw [hoffiov8]; omega) (by rw [hoffiov8]; omega) (by rw [hoffiov8]; omega) (by rw [hoffiov8]; omega) hi17
  have hstep18 : Step ⟨σ17,i17,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ18,i18,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs18
  have hpc18 : σ18.regs.get? Register.PC = some (0x800078dc#64) := by
    have := obs_store_pc_sn4 hobs18
    rwa [show BitVec.addInt (0x800078d8#64 : BitVec 64) 4 = (0x800078dc#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi18, hmi18⟩ := obs_store_minstret_sn4 hobs18
  have hx2_18 : σ18.regs.get? Register.x2 = some vsp :=
    obs_store_other_sn4 Register.x2 hobs18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_17
  have hx6_18 : σ18.regs.get? Register.x6 = some vt1 :=
    obs_store_other_sn4 Register.x6 hobs18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_17
  have hx8_18 : σ18.regs.get? Register.x8 = some v8 :=
    obs_store_other_sn4 Register.x8 hobs18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_17
  have hx16_18 : σ18.regs.get? Register.x16 = some vlen :=
    obs_store_other_sn4 Register.x16 hobs18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_17
  have hx20_18 : σ18.regs.get? Register.x20 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb v20 31 0) - (Sail.BitVec.extractLsb vs6 31 0))) :=
    obs_store_other_sn4 Register.x20 hobs18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_17
  have hx22_18 : σ18.regs.get? Register.x22 = some vs6 :=
    obs_store_other_sn4 Register.x22 hobs18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_17
  have hx23_18 : σ18.regs.get? Register.x23 = some viov :=
    obs_store_other_sn4 Register.x23 hobs18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_17
  have hx26_18 : σ18.regs.get? Register.x26 = some vbase :=
    obs_store_other_sn4 Register.x26 hobs18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_17
  have hx28_18 : σ18.regs.get? Register.x28 = some vt3 :=
    obs_store_other_sn4 Register.x28 hobs18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_17
  have hx12_18 : σ18.regs.get? Register.x12 = some (vcur + vs6) :=
    obs_store_other_sn4 Register.x12 hobs18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_17
  have hx5_18 : σ18.regs.get? Register.x5 = some (0#64) :=
    obs_store_other_sn4 Register.x5 hobs18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_17
  have hx14_18 : σ18.regs.get? Register.x14 = some (0#64) :=
    obs_store_other_sn4 Register.x14 hobs18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_17
  have hx15_18 : σ18.regs.get? Register.x15 = some (sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0)) :=
    obs_store_other_sn4 Register.x15 hobs18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_17
  have hNP17b : (afterNextPC (afterPrelude σ17) (0x800078d8#64)).mem = σ17.mem := rfl
  have hmE18 : σ18.mem = writeMap8 (writeMap8 (writeMap8 (c.σ.mem) ((vsp + sign_extend (m := 64) (0x0f0#12)).toNat) (sdData_val (vcur + vs6))) ((viov + sign_extend (m := 64) (0x000#12)).toNat) (sdData_val vbase)) ((viov + sign_extend (m := 64) (0x008#12)).toNat) (sdData_val vs6) := by
    rw [hmem18, hNP17b, hmE17]
  have hload18 : SvfprintfSliceLoaded σ18.mem := by
    rw [hmem18, hNP17b]; exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoffiov8]; omega) hload17
  have hfp18 : FlushPinsLoaded σ18.mem := by
    rw [hmem18, hNP17b]; exact flushPins_writeMap8_fl _ _ _ (by rw [hoffiov8]; omega) hfp17
  have hap18 : ArmPinsLoaded σ18.mem := by
    rw [hmem18, hNP17b]; exact armPins_writeMap8_43 _ _ _ (by rw [hoffiov8]; omega) hap17

  -- === 0x800078dc: li a4,7 ===
  obtain ⟨σ19, i19, hs19, hi19, hG19, hmem19, hobs19⟩ :=
    site_800078dc_pv σ18 i18 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x800078dc#64) vmi18
      hG18 hpc18 hmi18 hload18 rfl hi18
  have hstep19 : Step ⟨σ18,i18,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ19,i19,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs19
  have hpc19 : σ19.regs.get? Register.PC = some (0x800078e0#64) := by
    have := obs_alu_pc hobs19
    rwa [show BitVec.addInt (0x800078dc#64 : BitVec 64) 4 = (0x800078e0#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi19, hmi19⟩ := obs_alu_minstret hobs19
  have hx14_19 : σ19.regs.get? Register.x14 = some ((0#64) + sign_extend (m := 64) (0x007#12)) :=
    obs_alu_rd hobs19 (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [show ((0#64) + sign_extend (m := 64) (0x007#12) : BitVec 64) = (0x7#64) from by decide] at hx14_19
  have hx2_19 : σ19.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs19 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_18
  have hx6_19 : σ19.regs.get? Register.x6 = some vt1 :=
    obs_alu_other hobs19 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_18
  have hx8_19 : σ19.regs.get? Register.x8 = some v8 :=
    obs_alu_other hobs19 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_18
  have hx16_19 : σ19.regs.get? Register.x16 = some vlen :=
    obs_alu_other hobs19 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_18
  have hx20_19 : σ19.regs.get? Register.x20 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb v20 31 0) - (Sail.BitVec.extractLsb vs6 31 0))) :=
    obs_alu_other hobs19 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_18
  have hx22_19 : σ19.regs.get? Register.x22 = some vs6 :=
    obs_alu_other hobs19 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_18
  have hx23_19 : σ19.regs.get? Register.x23 = some viov :=
    obs_alu_other hobs19 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_18
  have hx26_19 : σ19.regs.get? Register.x26 = some vbase :=
    obs_alu_other hobs19 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_18
  have hx28_19 : σ19.regs.get? Register.x28 = some vt3 :=
    obs_alu_other hobs19 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_18
  have hx12_19 : σ19.regs.get? Register.x12 = some (vcur + vs6) :=
    obs_alu_other hobs19 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_18
  have hx5_19 : σ19.regs.get? Register.x5 = some (0#64) :=
    obs_alu_other hobs19 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_18
  have hx15_19 : σ19.regs.get? Register.x15 = some (sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0)) :=
    obs_alu_other hobs19 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_18
  have hmE19 : σ19.mem = writeMap8 (writeMap8 (writeMap8 (c.σ.mem) ((vsp + sign_extend (m := 64) (0x0f0#12)).toNat) (sdData_val (vcur + vs6))) ((viov + sign_extend (m := 64) (0x000#12)).toNat) (sdData_val vbase)) ((viov + sign_extend (m := 64) (0x008#12)).toNat) (sdData_val vs6) := hmem19.trans hmE18
  have hload19 : SvfprintfSliceLoaded σ19.mem := hmem19 ▸ hload18
  have hfp19 : FlushPinsLoaded σ19.mem := hmem19 ▸ hfp18
  have hap19 : ArmPinsLoaded σ19.mem := hmem19 ▸ hap18

  -- === 0x800078e0: sw a5,232(sp) — the bumped count ===
  obtain ⟨σ20, i20, hs20, hi20, hG20, hmem20, hobs20⟩ :=
    site_800078e0_pv σ19 i19 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x800078e0#64) vmi19 vsp (sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0))
      hG19 hpc19 hmi19 hx2_19 hx15_19 hload19 rfl (by rw [hoff232]; omega) (by rw [hoff232]; omega) (by rw [hoff232]; omega) (by rw [hoff232]; omega) hi19
  have hstep20 : Step ⟨σ19,i19,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ20,i20,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs20
  have hpc20 : σ20.regs.get? Register.PC = some (0x800078e4#64) := by
    have := obs_store_pc_sn4 hobs20
    rwa [show BitVec.addInt (0x800078e0#64 : BitVec 64) 4 = (0x800078e4#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi20, hmi20⟩ := obs_store_minstret_sn4 hobs20
  have hx2_20 : σ20.regs.get? Register.x2 = some vsp :=
    obs_store_other_sn4 Register.x2 hobs20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_19
  have hx6_20 : σ20.regs.get? Register.x6 = some vt1 :=
    obs_store_other_sn4 Register.x6 hobs20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_19
  have hx8_20 : σ20.regs.get? Register.x8 = some v8 :=
    obs_store_other_sn4 Register.x8 hobs20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_19
  have hx16_20 : σ20.regs.get? Register.x16 = some vlen :=
    obs_store_other_sn4 Register.x16 hobs20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_19
  have hx20_20 : σ20.regs.get? Register.x20 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb v20 31 0) - (Sail.BitVec.extractLsb vs6 31 0))) :=
    obs_store_other_sn4 Register.x20 hobs20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_19
  have hx22_20 : σ20.regs.get? Register.x22 = some vs6 :=
    obs_store_other_sn4 Register.x22 hobs20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_19
  have hx23_20 : σ20.regs.get? Register.x23 = some viov :=
    obs_store_other_sn4 Register.x23 hobs20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_19
  have hx26_20 : σ20.regs.get? Register.x26 = some vbase :=
    obs_store_other_sn4 Register.x26 hobs20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_19
  have hx28_20 : σ20.regs.get? Register.x28 = some vt3 :=
    obs_store_other_sn4 Register.x28 hobs20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_19
  have hx12_20 : σ20.regs.get? Register.x12 = some (vcur + vs6) :=
    obs_store_other_sn4 Register.x12 hobs20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_19
  have hx5_20 : σ20.regs.get? Register.x5 = some (0#64) :=
    obs_store_other_sn4 Register.x5 hobs20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_19
  have hx14_20 : σ20.regs.get? Register.x14 = some (0x7#64) :=
    obs_store_other_sn4 Register.x14 hobs20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_19
  have hx15_20 : σ20.regs.get? Register.x15 = some (sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0)) :=
    obs_store_other_sn4 Register.x15 hobs20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_19
  have hNP19b : (afterNextPC (afterPrelude σ19) (0x800078e0#64)).mem = σ19.mem := rfl
  have hmE20 : σ20.mem = writeMap4 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) ((vsp + sign_extend (m := 64) (0x0f0#12)).toNat) (sdData_val (vcur + vs6))) ((viov + sign_extend (m := 64) (0x000#12)).toNat) (sdData_val vbase)) ((viov + sign_extend (m := 64) (0x008#12)).toNat) (sdData_val vs6)) ((vsp + sign_extend (m := 64) (0x0e8#12)).toNat) (swData (sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0))) := by
    rw [hmem20, hNP19b, hmE19]
  have hload20 : SvfprintfSliceLoaded σ20.mem := by
    rw [hmem20, hNP19b]; exact svfprintfSlice_writeMap4_pe _ _ _ (by rw [hoff232]; omega) hload19
  have hfp20 : FlushPinsLoaded σ20.mem := by
    rw [hmem20, hNP19b]; exact flushPins_writeMap4_pe _ _ _ (by rw [hoff232]; omega) hfp19
  have hap20 : ArmPinsLoaded σ20.mem := by
    rw [hmem20, hNP19b]
    exact armPins_insert_43 _ _ _ (by rw [hoff232]; omega) (armPins_insert_43 _ _ _ (by rw [hoff232]; omega)
      (armPins_insert_43 _ _ _ (by rw [hoff232]; omega) (armPins_insert_43 _ _ _ (by rw [hoff232]; omega) hap19)))

  -- === 0x800078e4: blt a4,a5 NOT taken (no early flush) ===
  obtain ⟨σ21, i21, hs21, hi21, hG21, hmem21, hobs21⟩ :=
    site_800078e4_nottaken_pv σ20 i20 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x800078e4#64) vmi20 (0x7#64) (sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0))
      hG20 hpc20 hmi20 hx14_20 hx15_20 hload20 rfl hcntlt hi20
  have hstep21 : Step ⟨σ20,i20,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ21,i21,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs21
  have hpc21 : σ21.regs.get? Register.PC = some (0x800078e8#64) := by
    have := obs_bnottaken_pc hobs21
    rwa [show BitVec.addInt (0x800078e4#64 : BitVec 64) 4 = (0x800078e8#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi21, hmi21⟩ := obs_bnottaken_minstret hobs21
  have hx2_21 : σ21.regs.get? Register.x2 = some vsp :=
    obs_bnottaken_other hobs21 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_20
  have hx6_21 : σ21.regs.get? Register.x6 = some vt1 :=
    obs_bnottaken_other hobs21 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_20
  have hx8_21 : σ21.regs.get? Register.x8 = some v8 :=
    obs_bnottaken_other hobs21 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_20
  have hx16_21 : σ21.regs.get? Register.x16 = some vlen :=
    obs_bnottaken_other hobs21 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_20
  have hx20_21 : σ21.regs.get? Register.x20 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb v20 31 0) - (Sail.BitVec.extractLsb vs6 31 0))) :=
    obs_bnottaken_other hobs21 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_20
  have hx22_21 : σ21.regs.get? Register.x22 = some vs6 :=
    obs_bnottaken_other hobs21 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_20
  have hx23_21 : σ21.regs.get? Register.x23 = some viov :=
    obs_bnottaken_other hobs21 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_20
  have hx26_21 : σ21.regs.get? Register.x26 = some vbase :=
    obs_bnottaken_other hobs21 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_20
  have hx28_21 : σ21.regs.get? Register.x28 = some vt3 :=
    obs_bnottaken_other hobs21 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_20
  have hx12_21 : σ21.regs.get? Register.x12 = some (vcur + vs6) :=
    obs_bnottaken_other hobs21 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_20
  have hx5_21 : σ21.regs.get? Register.x5 = some (0#64) :=
    obs_bnottaken_other hobs21 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_20
  have hx14_21 : σ21.regs.get? Register.x14 = some (0x7#64) :=
    obs_bnottaken_other hobs21 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_20
  have hx15_21 : σ21.regs.get? Register.x15 = some (sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0)) :=
    obs_bnottaken_other hobs21 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_20
  have hmE21 : σ21.mem = writeMap4 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) ((vsp + sign_extend (m := 64) (0x0f0#12)).toNat) (sdData_val (vcur + vs6))) ((viov + sign_extend (m := 64) (0x000#12)).toNat) (sdData_val vbase)) ((viov + sign_extend (m := 64) (0x008#12)).toNat) (sdData_val vs6)) ((vsp + sign_extend (m := 64) (0x0e8#12)).toNat) (swData (sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0))) := hmem21.trans hmE20
  have hload21 : SvfprintfSliceLoaded σ21.mem := hmem21 ▸ hload20
  have hfp21 : FlushPinsLoaded σ21.mem := hmem21 ▸ hfp20
  have hap21 : ArmPinsLoaded σ21.mem := hmem21 ▸ hap20

  -- === 0x800078e8: addi s7,s7,16 — iov cursor += 16 ===
  obtain ⟨σ22, i22, hs22, hi22, hG22, hmem22, hobs22⟩ :=
    site_800078e8_pv σ21 i21 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x800078e8#64) vmi21 viov
      hG21 hpc21 hmi21 hx23_21 hload21 rfl hi21
  have hstep22 : Step ⟨σ21,i21,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ22,i22,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs22
  have hpc22 : σ22.regs.get? Register.PC = some (0x800078ec#64) := by
    have := obs_alu_pc hobs22
    rwa [show BitVec.addInt (0x800078e8#64 : BitVec 64) 4 = (0x800078ec#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi22, hmi22⟩ := obs_alu_minstret hobs22
  have hx23_22 : σ22.regs.get? Register.x23 = some (viov + sign_extend (m := 64) (0x010#12)) :=
    obs_alu_rd hobs22 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx2_22 : σ22.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs22 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_21
  have hx6_22 : σ22.regs.get? Register.x6 = some vt1 :=
    obs_alu_other hobs22 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_21
  have hx8_22 : σ22.regs.get? Register.x8 = some v8 :=
    obs_alu_other hobs22 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_21
  have hx16_22 : σ22.regs.get? Register.x16 = some vlen :=
    obs_alu_other hobs22 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_21
  have hx20_22 : σ22.regs.get? Register.x20 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb v20 31 0) - (Sail.BitVec.extractLsb vs6 31 0))) :=
    obs_alu_other hobs22 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_21
  have hx22_22 : σ22.regs.get? Register.x22 = some vs6 :=
    obs_alu_other hobs22 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_21
  have hx26_22 : σ22.regs.get? Register.x26 = some vbase :=
    obs_alu_other hobs22 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_21
  have hx28_22 : σ22.regs.get? Register.x28 = some vt3 :=
    obs_alu_other hobs22 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_21
  have hx12_22 : σ22.regs.get? Register.x12 = some (vcur + vs6) :=
    obs_alu_other hobs22 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_21
  have hx5_22 : σ22.regs.get? Register.x5 = some (0#64) :=
    obs_alu_other hobs22 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_21
  have hx14_22 : σ22.regs.get? Register.x14 = some (0x7#64) :=
    obs_alu_other hobs22 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_21
  have hx15_22 : σ22.regs.get? Register.x15 = some (sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0)) :=
    obs_alu_other hobs22 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_21
  have hmE22 : σ22.mem = writeMap4 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) ((vsp + sign_extend (m := 64) (0x0f0#12)).toNat) (sdData_val (vcur + vs6))) ((viov + sign_extend (m := 64) (0x000#12)).toNat) (sdData_val vbase)) ((viov + sign_extend (m := 64) (0x008#12)).toNat) (sdData_val vs6)) ((vsp + sign_extend (m := 64) (0x0e8#12)).toNat) (swData (sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0))) := hmem22.trans hmE21
  have hload22 : SvfprintfSliceLoaded σ22.mem := hmem22 ▸ hload21
  have hfp22 : FlushPinsLoaded σ22.mem := hmem22 ▸ hfp21
  have hap22 : ArmPinsLoaded σ22.mem := hmem22 ▸ hap21

  -- === 0x800078ec: andi t1,t1,4 — t1 := 0 ===
  obtain ⟨σ23, i23, hs23, hi23, hG23, hmem23, hobs23⟩ :=
    site_800078ec_pv σ22 i22 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x800078ec#64) vmi22 vt1
      hG22 hpc22 hmi22 hx6_22 hload22 rfl hi22
  have hstep23 : Step ⟨σ22,i22,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ23,i23,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs23
  have hpc23 : σ23.regs.get? Register.PC = some (0x800078f0#64) := by
    have := obs_alu_pc hobs23
    rwa [show BitVec.addInt (0x800078ec#64 : BitVec 64) 4 = (0x800078f0#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi23, hmi23⟩ := obs_alu_minstret hobs23
  have hx6_23 : σ23.regs.get? Register.x6 = some (vt1 &&& sign_extend (m := 64) (0x004#12)) :=
    obs_alu_rd hobs23 (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [hflag4z] at hx6_23
  have hx2_23 : σ23.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs23 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_22
  have hx8_23 : σ23.regs.get? Register.x8 = some v8 :=
    obs_alu_other hobs23 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_22
  have hx16_23 : σ23.regs.get? Register.x16 = some vlen :=
    obs_alu_other hobs23 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_22
  have hx20_23 : σ23.regs.get? Register.x20 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb v20 31 0) - (Sail.BitVec.extractLsb vs6 31 0))) :=
    obs_alu_other hobs23 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_22
  have hx22_23 : σ23.regs.get? Register.x22 = some vs6 :=
    obs_alu_other hobs23 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_22
  have hx23_23 : σ23.regs.get? Register.x23 = some (viov + sign_extend (m := 64) (0x010#12)) :=
    obs_alu_other hobs23 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_22
  have hx26_23 : σ23.regs.get? Register.x26 = some vbase :=
    obs_alu_other hobs23 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_22
  have hx28_23 : σ23.regs.get? Register.x28 = some vt3 :=
    obs_alu_other hobs23 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_22
  have hx12_23 : σ23.regs.get? Register.x12 = some (vcur + vs6) :=
    obs_alu_other hobs23 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_22
  have hx5_23 : σ23.regs.get? Register.x5 = some (0#64) :=
    obs_alu_other hobs23 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_22
  have hx14_23 : σ23.regs.get? Register.x14 = some (0x7#64) :=
    obs_alu_other hobs23 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_22
  have hx15_23 : σ23.regs.get? Register.x15 = some (sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0)) :=
    obs_alu_other hobs23 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_22
  have hmE23 : σ23.mem = writeMap4 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) ((vsp + sign_extend (m := 64) (0x0f0#12)).toNat) (sdData_val (vcur + vs6))) ((viov + sign_extend (m := 64) (0x000#12)).toNat) (sdData_val vbase)) ((viov + sign_extend (m := 64) (0x008#12)).toNat) (sdData_val vs6)) ((vsp + sign_extend (m := 64) (0x0e8#12)).toNat) (swData (sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0))) := hmem23.trans hmE22
  have hload23 : SvfprintfSliceLoaded σ23.mem := hmem23 ▸ hload22
  have hfp23 : FlushPinsLoaded σ23.mem := hmem23 ▸ hfp22
  have hap23 : ArmPinsLoaded σ23.mem := hmem23 ▸ hap22

  -- === 0x800078f0: beqz t1 TAKEN ===
  obtain ⟨σ24, i24, hs24, hi24, hG24, hmem24, hobs24⟩ :=
    site_800078f0_taken_pv σ23 i23 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x800078f0#64) vmi23 (0#64)
      hG23 hpc23 hmi23 hx6_23 hload23 rfl (by decide) hi23
  have hstep24 : Step ⟨σ23,i23,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ24,i24,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs24
  have hpc24 : σ24.regs.get? Register.PC = some (0x800078fc#64) := by
    have := obs_btaken_pc hobs24
    rwa [site_800078f0_taken_pv_tgt] at this
  obtain ⟨vmi24, hmi24⟩ := obs_btaken_minstret hobs24
  have hx2_24 : σ24.regs.get? Register.x2 = some vsp :=
    obs_btaken_other hobs24 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_23
  have hx6_24 : σ24.regs.get? Register.x6 = some (0#64) :=
    obs_btaken_other hobs24 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_23
  have hx8_24 : σ24.regs.get? Register.x8 = some v8 :=
    obs_btaken_other hobs24 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_23
  have hx16_24 : σ24.regs.get? Register.x16 = some vlen :=
    obs_btaken_other hobs24 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_23
  have hx20_24 : σ24.regs.get? Register.x20 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb v20 31 0) - (Sail.BitVec.extractLsb vs6 31 0))) :=
    obs_btaken_other hobs24 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_23
  have hx22_24 : σ24.regs.get? Register.x22 = some vs6 :=
    obs_btaken_other hobs24 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_23
  have hx23_24 : σ24.regs.get? Register.x23 = some (viov + sign_extend (m := 64) (0x010#12)) :=
    obs_btaken_other hobs24 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_23
  have hx26_24 : σ24.regs.get? Register.x26 = some vbase :=
    obs_btaken_other hobs24 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_23
  have hx28_24 : σ24.regs.get? Register.x28 = some vt3 :=
    obs_btaken_other hobs24 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_23
  have hx12_24 : σ24.regs.get? Register.x12 = some (vcur + vs6) :=
    obs_btaken_other hobs24 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_23
  have hx5_24 : σ24.regs.get? Register.x5 = some (0#64) :=
    obs_btaken_other hobs24 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_23
  have hx14_24 : σ24.regs.get? Register.x14 = some (0x7#64) :=
    obs_btaken_other hobs24 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_23
  have hx15_24 : σ24.regs.get? Register.x15 = some (sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0)) :=
    obs_btaken_other hobs24 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_23
  have hmE24 : σ24.mem = writeMap4 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) ((vsp + sign_extend (m := 64) (0x0f0#12)).toNat) (sdData_val (vcur + vs6))) ((viov + sign_extend (m := 64) (0x000#12)).toNat) (sdData_val vbase)) ((viov + sign_extend (m := 64) (0x008#12)).toNat) (sdData_val vs6)) ((vsp + sign_extend (m := 64) (0x0e8#12)).toNat) (swData (sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0))) := hmem24.trans hmE23
  have hload24 : SvfprintfSliceLoaded σ24.mem := hmem24 ▸ hload23
  have hfp24 : FlushPinsLoaded σ24.mem := hmem24 ▸ hfp23
  have hap24 : ArmPinsLoaded σ24.mem := hmem24 ▸ hap23

  -- === 0x800078fc: mv a5,t3 ===
  obtain ⟨σ25, i25, hs25, hi25, hG25, hmem25, hobs25⟩ :=
    site_800078fc_pv σ24 i24 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x800078fc#64) vmi24 vt3
      hG24 hpc24 hmi24 hx28_24 hload24 rfl hi24
  have hstep25 : Step ⟨σ24,i24,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ25,i25,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs25
  have hpc25 : σ25.regs.get? Register.PC = some (0x80007900#64) := by
    have := obs_alu_pc hobs25
    rwa [show BitVec.addInt (0x800078fc#64 : BitVec 64) 4 = (0x80007900#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi25, hmi25⟩ := obs_alu_minstret hobs25
  have hx15_25 : σ25.regs.get? Register.x15 = some (vt3 + sign_extend (m := 64) (0x000#12)) :=
    obs_alu_rd hobs25 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx2_25 : σ25.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs25 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_24
  have hx6_25 : σ25.regs.get? Register.x6 = some (0#64) :=
    obs_alu_other hobs25 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_24
  have hx8_25 : σ25.regs.get? Register.x8 = some v8 :=
    obs_alu_other hobs25 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_24
  have hx16_25 : σ25.regs.get? Register.x16 = some vlen :=
    obs_alu_other hobs25 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_24
  have hx20_25 : σ25.regs.get? Register.x20 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb v20 31 0) - (Sail.BitVec.extractLsb vs6 31 0))) :=
    obs_alu_other hobs25 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_24
  have hx22_25 : σ25.regs.get? Register.x22 = some vs6 :=
    obs_alu_other hobs25 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_24
  have hx23_25 : σ25.regs.get? Register.x23 = some (viov + sign_extend (m := 64) (0x010#12)) :=
    obs_alu_other hobs25 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_24
  have hx26_25 : σ25.regs.get? Register.x26 = some vbase :=
    obs_alu_other hobs25 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_24
  have hx28_25 : σ25.regs.get? Register.x28 = some vt3 :=
    obs_alu_other hobs25 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_24
  have hx12_25 : σ25.regs.get? Register.x12 = some (vcur + vs6) :=
    obs_alu_other hobs25 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_24
  have hx5_25 : σ25.regs.get? Register.x5 = some (0#64) :=
    obs_alu_other hobs25 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_24
  have hx14_25 : σ25.regs.get? Register.x14 = some (0x7#64) :=
    obs_alu_other hobs25 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_24
  have hmE25 : σ25.mem = writeMap4 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) ((vsp + sign_extend (m := 64) (0x0f0#12)).toNat) (sdData_val (vcur + vs6))) ((viov + sign_extend (m := 64) (0x000#12)).toNat) (sdData_val vbase)) ((viov + sign_extend (m := 64) (0x008#12)).toNat) (sdData_val vs6)) ((vsp + sign_extend (m := 64) (0x0e8#12)).toNat) (swData (sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0))) := hmem25.trans hmE24
  have hload25 : SvfprintfSliceLoaded σ25.mem := hmem25 ▸ hload24
  have hfp25 : FlushPinsLoaded σ25.mem := hmem25 ▸ hfp24
  have hap25 : ArmPinsLoaded σ25.mem := hmem25 ▸ hap24

  -- === 0x80007900: bge t3,a6 NOT taken ===
  obtain ⟨σ26, i26, hs26, hi26, hG26, hmem26, hobs26⟩ :=
    site_80007900_nottaken_pv σ25 i25 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x80007900#64) vmi25 vt3 vlen
      hG25 hpc25 hmi25 hx28_25 hx16_25 hload25 rfl hwlen hi25
  have hstep26 : Step ⟨σ25,i25,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ26,i26,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs26
  have hpc26 : σ26.regs.get? Register.PC = some (0x80007904#64) := by
    have := obs_bnottaken_pc hobs26
    rwa [show BitVec.addInt (0x80007900#64 : BitVec 64) 4 = (0x80007904#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi26, hmi26⟩ := obs_bnottaken_minstret hobs26
  have hx2_26 : σ26.regs.get? Register.x2 = some vsp :=
    obs_bnottaken_other hobs26 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_25
  have hx6_26 : σ26.regs.get? Register.x6 = some (0#64) :=
    obs_bnottaken_other hobs26 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_25
  have hx8_26 : σ26.regs.get? Register.x8 = some v8 :=
    obs_bnottaken_other hobs26 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_25
  have hx16_26 : σ26.regs.get? Register.x16 = some vlen :=
    obs_bnottaken_other hobs26 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_25
  have hx20_26 : σ26.regs.get? Register.x20 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb v20 31 0) - (Sail.BitVec.extractLsb vs6 31 0))) :=
    obs_bnottaken_other hobs26 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_25
  have hx22_26 : σ26.regs.get? Register.x22 = some vs6 :=
    obs_bnottaken_other hobs26 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_25
  have hx23_26 : σ26.regs.get? Register.x23 = some (viov + sign_extend (m := 64) (0x010#12)) :=
    obs_bnottaken_other hobs26 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_25
  have hx26_26 : σ26.regs.get? Register.x26 = some vbase :=
    obs_bnottaken_other hobs26 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_25
  have hx28_26 : σ26.regs.get? Register.x28 = some vt3 :=
    obs_bnottaken_other hobs26 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_25
  have hx12_26 : σ26.regs.get? Register.x12 = some (vcur + vs6) :=
    obs_bnottaken_other hobs26 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_25
  have hx5_26 : σ26.regs.get? Register.x5 = some (0#64) :=
    obs_bnottaken_other hobs26 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_25
  have hx14_26 : σ26.regs.get? Register.x14 = some (0x7#64) :=
    obs_bnottaken_other hobs26 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_25
  have hx15_26 : σ26.regs.get? Register.x15 = some (vt3 + sign_extend (m := 64) (0x000#12)) :=
    obs_bnottaken_other hobs26 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_25
  have hmE26 : σ26.mem = writeMap4 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) ((vsp + sign_extend (m := 64) (0x0f0#12)).toNat) (sdData_val (vcur + vs6))) ((viov + sign_extend (m := 64) (0x000#12)).toNat) (sdData_val vbase)) ((viov + sign_extend (m := 64) (0x008#12)).toNat) (sdData_val vs6)) ((vsp + sign_extend (m := 64) (0x0e8#12)).toNat) (swData (sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0))) := hmem26.trans hmE25
  have hload26 : SvfprintfSliceLoaded σ26.mem := hmem26 ▸ hload25
  have hfp26 : FlushPinsLoaded σ26.mem := hmem26 ▸ hfp25
  have hap26 : ArmPinsLoaded σ26.mem := hmem26 ▸ hap25

  -- === 0x80007904: mv a5,a6 — the selected length ===
  obtain ⟨σ27, i27, hs27, hi27, hG27, hmem27, hobs27⟩ :=
    site_80007904_pv σ26 i26 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x80007904#64) vmi26 vlen
      hG26 hpc26 hmi26 hx16_26 hload26 rfl hi26
  have hstep27 : Step ⟨σ26,i26,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ27,i27,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs27
  have hpc27 : σ27.regs.get? Register.PC = some (0x80007908#64) := by
    have := obs_alu_pc hobs27
    rwa [show BitVec.addInt (0x80007904#64 : BitVec 64) 4 = (0x80007908#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi27, hmi27⟩ := obs_alu_minstret hobs27
  have hx15_27 : σ27.regs.get? Register.x15 = some (vlen + sign_extend (m := 64) (0x000#12)) :=
    obs_alu_rd hobs27 (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [show (vlen + sign_extend (m := 64) (0x000#12) : BitVec 64) = vlen from by
    rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = (0#64) from by decide]
    exact BitVec.add_zero vlen] at hx15_27
  have hx2_27 : σ27.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs27 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_26
  have hx6_27 : σ27.regs.get? Register.x6 = some (0#64) :=
    obs_alu_other hobs27 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_26
  have hx8_27 : σ27.regs.get? Register.x8 = some v8 :=
    obs_alu_other hobs27 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_26
  have hx16_27 : σ27.regs.get? Register.x16 = some vlen :=
    obs_alu_other hobs27 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_26
  have hx20_27 : σ27.regs.get? Register.x20 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb v20 31 0) - (Sail.BitVec.extractLsb vs6 31 0))) :=
    obs_alu_other hobs27 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_26
  have hx22_27 : σ27.regs.get? Register.x22 = some vs6 :=
    obs_alu_other hobs27 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_26
  have hx23_27 : σ27.regs.get? Register.x23 = some (viov + sign_extend (m := 64) (0x010#12)) :=
    obs_alu_other hobs27 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_26
  have hx26_27 : σ27.regs.get? Register.x26 = some vbase :=
    obs_alu_other hobs27 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_26
  have hx28_27 : σ27.regs.get? Register.x28 = some vt3 :=
    obs_alu_other hobs27 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_26
  have hx12_27 : σ27.regs.get? Register.x12 = some (vcur + vs6) :=
    obs_alu_other hobs27 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_26
  have hx5_27 : σ27.regs.get? Register.x5 = some (0#64) :=
    obs_alu_other hobs27 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_26
  have hx14_27 : σ27.regs.get? Register.x14 = some (0x7#64) :=
    obs_alu_other hobs27 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_26
  have hmE27 : σ27.mem = writeMap4 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) ((vsp + sign_extend (m := 64) (0x0f0#12)).toNat) (sdData_val (vcur + vs6))) ((viov + sign_extend (m := 64) (0x000#12)).toNat) (sdData_val vbase)) ((viov + sign_extend (m := 64) (0x008#12)).toNat) (sdData_val vs6)) ((vsp + sign_extend (m := 64) (0x0e8#12)).toNat) (swData (sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0))) := hmem27.trans hmE26
  have hload27 : SvfprintfSliceLoaded σ27.mem := hmem27 ▸ hload26
  have hfp27 : FlushPinsLoaded σ27.mem := hmem27 ▸ hfp26
  have hap27 : ArmPinsLoaded σ27.mem := hmem27 ▸ hap26

  -- === the shared call tail 0x7908 → jal __ssprint_r (Spec17) ===
  -- SlotHolds sp+16 / sp+8 transported across the four writes (outermost first)
  have htot27 : SlotHolds vsp 0x010 vtot σ27.mem := by
    rw [hmE27]
    exact slotHolds_writeMap4_i2 vsp 0x010 vtot _ _ _ (by rw [hoff16, hoff232]; omega)
      (slotHolds_writeMap8 vsp 0x010 vtot _ _ _ (Or.inl (by rw [hoff16, hoffiov8]; omega))
        (slotHolds_writeMap8 vsp 0x010 vtot _ _ _ (Or.inl (by rw [hoff16, hoffiov0]; omega))
          (slotHolds_writeMap8 vsp 0x010 vtot _ _ _ (Or.inl (by rw [hoff16, hoff240]; omega)) htot)))
  have hstr27 : SlotHolds vsp 0x008 vstr σ27.mem := by
    rw [hmE27]
    exact slotHolds_writeMap4_i2 vsp 0x008 vstr _ _ _ (by rw [hoff8, hoff232]; omega)
      (slotHolds_writeMap8 vsp 0x008 vstr _ _ _ (Or.inl (by rw [hoff8, hoffiov8]; omega))
        (slotHolds_writeMap8 vsp 0x008 vstr _ _ _ (Or.inl (by rw [hoff8, hoffiov0]; omega))
          (slotHolds_writeMap8 vsp 0x008 vstr _ _ _ (Or.inl (by rw [hoff8, hoff240]; omega)) hstr)))
  obtain ⟨c', hs', hG', hpc', hx1', hx10', hx11', hx12', hx2', hx5', hx6', hx8',
    hx16', hx20', hx22', hx23', hx26', hx28', hmem', htick', hmi', hkeep'⟩ :=
    iov2Tail_spec vsp (0#64) (0#64) v8 (vcur + vs6) vlen
      (sign_extend (m := 64) ((Sail.BitVec.extractLsb v20 31 0) - (Sail.BitVec.extractLsb vs6 31 0))) vs6
      (viov + sign_extend (m := 64) (0x010#12)) vbase vt3 vlen vstr vtot
      ⟨σ27, i27, c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ hG27 hpc27 hx2_27 hx5_27 hx6_27 hx8_27
      hx12_27 hx15_27 hx16_27 hx20_27 hx22_27 hx23_27 hx26_27 hx28_27
      hload27 hfp27 htot27 hstr27 hvc2 hspwin hsphi hspalign hi27
  -- final memory shape
  have hmemF : c'.σ.mem = writeMap8
      (writeMap4
        (writeMap8
          (writeMap8
            (writeMap8 c.σ.mem
              ((vsp + sign_extend (m := 64) (0x0f0#12)).toNat) (sdData_val (vcur + vs6)))
            ((viov + sign_extend (m := 64) (0x000#12)).toNat) (sdData_val vbase))
          ((viov + sign_extend (m := 64) (0x008#12)).toNat) (sdData_val vs6))
        ((vsp + sign_extend (m := 64) (0x0e8#12)).toNat)
          (swData (sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0))))
      ((vsp + sign_extend (m := 64) (0x010#12)).toNat)
        (sdData_val (sign_extend (m := 64)
          (Sail.BitVec.extractLsb vlen 31 0 + Sail.BitVec.extractLsb vtot 31 0))) := by
    rw [hmem']
    show writeMap8 σ27.mem _ _ = _
    rw [hmE27]
  -- KeepRegs over the 27 emitted steps, then the tail's
  have hkeep27 : KeepRegs midRegs5 c.σ σ27 := by
    have h0 := keep_rfl midRegs5 c.σ
    have h1 := keep_alu hobs1 (by decide) h0
    have h2 := keep_alu hobs2 (by decide) h1
    have h3 := keep_alu hobs3 (by decide) h2
    have h4 := keep_btaken hobs4 (by decide) h3
    have h5 := keep_alu hobs5 (by decide) h4
    have h6 := keep_bnottaken hobs6 (by decide) h5
    have h7 := keep_alu hobs7 (by decide) h6
    have h8 := keep_bnottaken hobs8 (by decide) h7
    have h9 := keep_alu hobs9 (by decide) h8
    have h10 := keep_btaken hobs10 (by decide) h9
    have h11 := keep_alu hobs11 (by decide) h10
    have h12 := keep_bnottaken hobs12 (by decide) h11
    have h13 := keep_alu hobs13 (by decide) h12
    have h14 := keep_alu hobs14 (by decide) h13
    have h15 := keep_store hobs15 (by decide) h14
    have h16 := keep_alu hobs16 (by decide) h15
    have h17 := keep_store hobs17 (by decide) h16
    have h18 := keep_store hobs18 (by decide) h17
    have h19 := keep_alu hobs19 (by decide) h18
    have h20 := keep_store hobs20 (by decide) h19
    have h21 := keep_bnottaken hobs21 (by decide) h20
    have h22 := keep_alu hobs22 (by decide) h21
    have h23 := keep_alu hobs23 (by decide) h22
    have h24 := keep_btaken hobs24 (by decide) h23
    have h25 := keep_alu hobs25 (by decide) h24
    have h26 := keep_bnottaken hobs26 (by decide) h25
    exact keep_alu hobs27 (by decide) h26
  have hkeepF : KeepRegs midRegs5 c.σ c'.σ := keep_trans hkeep27 hkeep'
  -- assemble the Steps chain: c → σ27 → c'
  have hchain : Steps c ⟨σ27, i27, c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ :=
    (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans ((Steps.single hstep4).trans ((Steps.single hstep5).trans ((Steps.single hstep6).trans ((Steps.single hstep7).trans ((Steps.single hstep8).trans ((Steps.single hstep9).trans ((Steps.single hstep10).trans ((Steps.single hstep11).trans ((Steps.single hstep12).trans ((Steps.single hstep13).trans ((Steps.single hstep14).trans ((Steps.single hstep15).trans ((Steps.single hstep16).trans ((Steps.single hstep17).trans ((Steps.single hstep18).trans ((Steps.single hstep19).trans ((Steps.single hstep20).trans ((Steps.single hstep21).trans ((Steps.single hstep22).trans ((Steps.single hstep23).trans ((Steps.single hstep24).trans ((Steps.single hstep25).trans ((Steps.single hstep26).trans (Steps.single hstep27))))))))))))))))))))))))))
  exact ⟨c', hchain.trans hs', hG', hpc', hx1', hx10', hx11', hx12', hx2', hx5',
    hx6', hx8', hx16', hx20', hx22', hx23', hx26', hx28', hmemF, htick', hmi', hkeepF⟩

end Vsa.Sim
