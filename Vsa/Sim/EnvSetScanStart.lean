import Vsa.Sim.EnvSetRecursive
import Vsa.Sim.EnvGetSpec7

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem env_set_parent_scan_start
    (g : (R : Register) → Option (RegisterType R))
    (env name out r sp : BitVec 64) (parentAddr : Vsa.While.Addr)
    (f : Vsa.While.Frame) (nameStr : String) (pn : Nat)
      (out0 : Array String)  (c : Config)
    (hHead : SetParentHeadSt g env name out r sp parentAddr f N φf φc out0 m0 c)
    (hNames : EnvSetScan.ScanNames m0 pn name nameStr f)
    (hPnRead : read64 m0 (env.toNat + 8) = some pn)
    (hLenPos : 0 < f.vars.length)
    (hLenSmall : f.vars.length < 2^31)
    (hPnSmall : pn < 2^64)
    (hEnvSmall : φf parentAddr < 2^64)
    (henvLo : 0x80000000 ≤ env.toNat)
    (henvHi : env.toNat + 32 ≤ 0x100000000)
    (henvWin : tohostAddr + 8 ≤ env.toNat)
    (henvAlign : env.toNat % 8 = 0) :
    ∃ c' g', Steps c c' ∧
      EnvSetScan.ScanSt g' (0x80002d2c#64) env name out
        (BitVec.ofNat 64 f.vars.length) (BitVec.ofNat 64 pn) r sp 0
        f nameStr N φf φc m0 c' ∧
      c'.σ.sailOutput = c.σ.sailOutput := by
  have hEnvEq : env.toNat = φf parentAddr := by
    rw [hHead.parent_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hEnvSmall]
  have hreadLen : read32 m0 env.toNat = some f.vars.length := by
    rw [hEnvEq]
    exact hHead.frame.1
  obtain ⟨cb0, cb1, cb2, cb3, hcb0, hcb1, hcb2, hcb3, hcrec⟩ :=
    read32_bytes_eg7 m0 env.toNat f.vars.length hreadLen
  obtain ⟨vmi0, hmi0⟩ := hHead.minstret
  have hc40addr : (env + sign_extend (m := 64) (0x000#12)).toNat = env.toNat := by
    rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by decide,
      BitVec.add_zero]
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80002d0c_es c.σ c.tick c.steps (0x80002d0c#64) vmi0 env
      cb0 cb1 cb2 cb3 hHead.good hHead.pc hmi0 hHead.env4 hHead.loadedSet rfl
      (by rw [hc40addr]; exact henvLo) (by rw [hc40addr]; omega)
      (by rw [hc40addr]; right; omega)
      (by rw [hc40addr, hHead.mem]; exact hcb0)
      (by rw [hc40addr, hHead.mem]; exact hcb1)
      (by rw [hc40addr, hHead.mem]; exact hcb2)
      (by rw [hc40addr, hHead.mem]; exact hcb3) hHead.tick
  let c1 : Config := ⟨σ1, i1, c.steps + 1⟩
  have hstep1 : Step c c1 := by cases c; exact hs1
  have hmem1' : σ1.mem = m0 := by rw [hmem1]; exact hHead.mem
  have hpc1 : σ1.regs.get? Register.PC = some (0x80002d10#64 : BitVec 64) := by
    have h := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x80002d0c#64) 4 = (0x80002d10#64 : BitVec 64) from by decide] at h
  have hx18_1 : σ1.regs.get? Register.x18 = some (BitVec.ofNat 64 f.vars.length) := by
    have h := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext_count_eg7 cb0 cb1 cb2 cb3 f.vars.length hLenSmall hcrec] at h
  have hx20_1 := obs_alu_other' hobs1 Register.x20 (by decide) hHead.env4
  have hx19_1 := obs_alu_other' hobs1 Register.x19 (by decide) hHead.name3
  have hx21_1 := obs_alu_other' hobs1 Register.x21 (by decide) hHead.value5
  have hra_1 := obs_alu_other' hobs1 Register.x1 (by decide) hHead.ra
  have hsp_1 := obs_alu_other' hobs1 Register.x2 (by decide) hHead.sp2
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hblez : zopz0zKzJ_s (0#64) (BitVec.ofNat 64 f.vars.length) = false := by
    have hpos : 0 < (BitVec.ofNat 64 f.vars.length).toInt := by
      rw [BitVec.toInt_eq_toNat_of_lt (by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact_mod_cast hLenPos
    unfold zopz0zKzJ_s
    rw [decide_eq_false_iff_not]
    simp only [BitVec.toInt_zero, ge_iff_le, Int.not_le]
    exact hpos
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80002d10_nottaken_es σ1 i1 (c.steps + 1) (0x80002d10#64) vmi1
      (BitVec.ofNat 64 f.vars.length) hG1 hpc1 hmi1 hx18_1
      (by rw [hmem1']; exact hHead.mem ▸ hHead.loadedSet) rfl hblez hi1
  let c2 : Config := ⟨σ2, i2, c.steps + 2⟩
  have hstep2 : Step c1 c2 := by exact hs2
  have hmem2' : σ2.mem = m0 := by rw [hmem2]; exact hmem1'
  have hpc2 : σ2.regs.get? Register.PC = some (0x80002d14#64 : BitVec 64) := by
    have h := obs_bnottaken_pc hobs2
    rwa [show BitVec.addInt (0x80002d10#64) 4 = (0x80002d14#64 : BitVec 64) from by decide] at h
  have hx18_2 := obs_bnottaken_other' hobs2 Register.x18 (by decide) hx18_1
  have hx20_2 := obs_bnottaken_other' hobs2 Register.x20 (by decide) hx20_1
  have hx19_2 := obs_bnottaken_other' hobs2 Register.x19 (by decide) hx19_1
  have hx21_2 := obs_bnottaken_other' hobs2 Register.x21 (by decide) hx21_1
  have hra_2 := obs_bnottaken_other' hobs2 Register.x1 (by decide) hra_1
  have hsp_2 := obs_bnottaken_other' hobs2 Register.x2 (by decide) hsp_1
  obtain ⟨vmi2, hmi2⟩ := obs_bnottaken_minstret hobs2
  obtain ⟨nb0, nb1, nb2, nb3, nb4, nb5, nb6, nb7,
    hnb0, hnb1, hnb2, hnb3, hnb4, hnb5, hnb6, hnb7⟩ :=
    ld64_bytes m0 (env.toNat + 8) pn hPnRead
  have hc48addr : (env + sign_extend (m := 64) (0x008#12)).toNat = env.toNat + 8 :=
    off_pos_eg6 env (0x008#12) 8 (by decide) (by omega)
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80002d14_es σ2 i2 (c.steps + 2) (0x80002d14#64) vmi2 env
      nb0 nb1 nb2 nb3 nb4 nb5 nb6 nb7 hG2 hpc2 hmi2 hx20_2
      (by rw [hmem2']; exact hHead.mem ▸ hHead.loadedSet) rfl
      (by rw [hc48addr]; omega) (by rw [hc48addr]; omega)
      (by rw [hc48addr]; right; omega)
      (by rw [hc48addr, hmem2']; exact hnb0) (by rw [hc48addr, hmem2']; exact hnb1)
      (by rw [hc48addr, hmem2']; exact hnb2) (by rw [hc48addr, hmem2']; exact hnb3)
      (by rw [hc48addr, hmem2']; exact hnb4) (by rw [hc48addr, hmem2']; exact hnb5)
      (by rw [hc48addr, hmem2']; exact hnb6) (by rw [hc48addr, hmem2']; exact hnb7) hi2
  let c3 : Config := ⟨σ3, i3, c.steps + 3⟩
  have hstep3 : Step c2 c3 := by exact hs3
  have hmem3' : σ3.mem = m0 := by rw [hmem3]; exact hmem2'
  have hpc3 : σ3.regs.get? Register.PC = some (0x80002d18#64 : BitVec 64) := by
    have h := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x80002d14#64) 4 = (0x80002d18#64 : BitVec 64) from by decide] at h
  have hx9_3 : σ3.regs.get? Register.x9 = some (BitVec.ofNat 64 pn) := by
    have h := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [ld_value_eq_read64 m0 (env.toNat + 8) pn nb0 nb1 nb2 nb3 nb4 nb5 nb6 nb7
      hPnRead hnb0 hnb1 hnb2 hnb3 hnb4 hnb5 hnb6 hnb7] at h
  have hx18_3 := obs_alu_other' hobs3 Register.x18 (by decide) hx18_2
  have hx20_3 := obs_alu_other' hobs3 Register.x20 (by decide) hx20_2
  have hx19_3 := obs_alu_other' hobs3 Register.x19 (by decide) hx19_2
  have hx21_3 := obs_alu_other' hobs3 Register.x21 (by decide) hx21_2
  have hra_3 := obs_alu_other' hobs3 Register.x1 (by decide) hra_2
  have hsp_3 := obs_alu_other' hobs3 Register.x2 (by decide) hsp_2
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80002d18_es σ3 i3 (c.steps + 3) (0x80002d18#64) vmi3 hG3 hpc3 hmi3
      (by rw [hmem3']; exact hHead.mem ▸ hHead.loadedSet) rfl hi3
  let c4 : Config := ⟨σ4, i4, c.steps + 4⟩
  have hstep4 : Step c3 c4 := by exact hs4
  have hmem4' : σ4.mem = m0 := by rw [hmem4]; exact hmem3'
  have hpc4 : σ4.regs.get? Register.PC = some (0x80002d1c#64 : BitVec 64) := by
    have h := obs_alu_pc hobs4
    rwa [show BitVec.addInt (0x80002d18#64) 4 = (0x80002d1c#64 : BitVec 64) from by decide] at h
  have hx8_4 : σ4.regs.get? Register.x8 = some (0#64 : BitVec 64) := by
    have h := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
    have hz : (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      decide
    simpa [hz] using h
  have hx9_4 := obs_alu_other' hobs4 Register.x9 (by decide) hx9_3
  have hx18_4 := obs_alu_other' hobs4 Register.x18 (by decide) hx18_3
  have hx20_4 := obs_alu_other' hobs4 Register.x20 (by decide) hx20_3
  have hx19_4 := obs_alu_other' hobs4 Register.x19 (by decide) hx19_3
  have hx21_4 := obs_alu_other' hobs4 Register.x21 (by decide) hx21_3
  have hra_4 := obs_alu_other' hobs4 Register.x1 (by decide) hra_3
  have hsp_4 := obs_alu_other' hobs4 Register.x2 (by decide) hsp_3
  obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80002d1c_es σ4 i4 (c.steps + 4) (0x80002d1c#64) vmi4 hG4 hpc4 hmi4
      (by rw [hmem4']; exact hHead.mem ▸ hHead.loadedSet) rfl (by decide) hi4
  let c5 : Config := ⟨σ5, i5, c.steps + 5⟩
  have hstep5 : Step c4 c5 := by exact hs5
  have hmem5' : σ5.mem = m0 := by rw [hmem5]; exact hmem4'
  have hpc5 : σ5.regs.get? Register.PC = some (0x80002d2c#64 : BitVec 64) := by
    have h := obs_jump_x0_pc_eg hobs5
    rwa [show (0x80002d1c#64 : BitVec 64) + sign_extend (m := 64) (0x000010#21) =
      (0x80002d2c#64 : BitVec 64) from by decide] at h
  have hx8_5 := obs_jx0_other_eg7 hobs5 Register.x8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hx8_4
  have hx9_5 := obs_jx0_other_eg7 hobs5 Register.x9 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hx9_4
  have hx18_5 := obs_jx0_other_eg7 hobs5 Register.x18 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hx18_4
  have hx20_5 := obs_jx0_other_eg7 hobs5 Register.x20 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hx20_4
  have hx19_5 := obs_jx0_other_eg7 hobs5 Register.x19 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hx19_4
  have hx21_5 := obs_jx0_other_eg7 hobs5 Register.x21 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hx21_4
  have hra_5 := obs_jx0_other_eg7 hobs5 Register.x1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hra_4
  have hsp_5 := obs_jx0_other_eg7 hobs5 Register.x2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hsp_4
  obtain ⟨vmi5, hmi5⟩ := obs_jx0_minstret_eg7 hobs5
  refine ⟨c5, (fun R => c5.σ.regs.get? R),
    ((((Steps.single hstep1).trans (Steps.single hstep2)).trans (Steps.single hstep3)).trans
      (Steps.single hstep4)).trans (Steps.single hstep5), ?_, ?_⟩
  refine
    { good := hG5, loadedG := ?_, loadedS := ?_, mem := hmem5', pc := hpc5,
      env4 := hx20_5, name3 := hx19_5, out5 := hx21_5, count2 := hx18_5,
      cursor1 := by simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hPnSmall] using hx9_5,
      idx0 := hx8_5, ra := hra_5, sp2 := hsp_5, minstret := ⟨vmi5, hmi5⟩,
      tick := hi5, frame := by rw [hEnvEq]; exact hHead.frame,
      names := by simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hPnSmall] using hNames,
      count_eq := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)],
      ile := Nat.zero_le _, ghost := fun _ _ => rfl }
  · rw [hmem5']; exact hHead.mem ▸ hHead.loadedSet
  · rw [hmem5']; exact hHead.mem ▸ hHead.loadedStrcmp
  · rw [hobs5.out, sailOutput_sigmaPost_jump_x0,
      hobs4.out, sailOutput_sigmaPost_alu,
      hobs3.out, sailOutput_sigmaPost_alu,
      hobs2.out, sailOutput_sigmaPost_branch_nottaken,
      hobs1.out, sailOutput_sigmaPost_alu]

/-- Empty parent frame: the count load and taken `blez` edge immediately
produce the full miss carrier for the next parent transition. -/
theorem env_set_parent_empty
    (g : (R : Register) → Option (RegisterType R))
    (env name out r sp : BitVec 64) (parentAddr : Vsa.While.Addr)
    (f : Vsa.While.Frame) (nameStr : String) (pn : Nat)
      (out0 : Array String)  (c : Config)
    (hHead : SetParentHeadSt g env name out r sp parentAddr f N φf φc out0 m0 c)
    (hNames : EnvSetScan.ScanNames m0 pn name nameStr f)
    (hEmpty : f.vars.length = 0)
    (hPnSmall : pn < 2^64)
    (hEnvSmall : φf parentAddr < 2^64)
    (henvLo : 0x80000000 ≤ env.toNat)
    (henvHi : env.toNat + 32 ≤ 0x100000000)
    (henvWin : tohostAddr + 8 ≤ env.toNat)
    (henvAlign : env.toNat % 8 = 0) :
    ∃ c' g', Steps c c' ∧
      EnvSetScan.ScanMissSt g' env name out (0#64) (BitVec.ofNat 64 pn) r sp
        f nameStr N φf φc m0 c' ∧
      c'.σ.sailOutput = c.σ.sailOutput := by
  have hEnvEq : env.toNat = φf parentAddr := by
    rw [hHead.parent_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hEnvSmall]
  have hreadLen : read32 m0 env.toNat = some 0 := by
    rw [hEnvEq, ← hEmpty]
    exact hHead.frame.1
  obtain ⟨cb0, cb1, cb2, cb3, hcb0, hcb1, hcb2, hcb3, hcrec⟩ :=
    read32_bytes_eg7 m0 env.toNat 0 hreadLen
  obtain ⟨vmi0, hmi0⟩ := hHead.minstret
  have hc40addr : (env + sign_extend (m := 64) (0x000#12)).toNat = env.toNat := by
    rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by decide,
      BitVec.add_zero]
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80002d0c_es c.σ c.tick c.steps (0x80002d0c#64) vmi0 env
      cb0 cb1 cb2 cb3 hHead.good hHead.pc hmi0 hHead.env4 hHead.loadedSet rfl
      (by rw [hc40addr]; exact henvLo) (by rw [hc40addr]; omega)
      (by rw [hc40addr]; right; omega)
      (by rw [hc40addr, hHead.mem]; exact hcb0)
      (by rw [hc40addr, hHead.mem]; exact hcb1)
      (by rw [hc40addr, hHead.mem]; exact hcb2)
      (by rw [hc40addr, hHead.mem]; exact hcb3) hHead.tick
  let c1 : Config := ⟨σ1, i1, c.steps + 1⟩
  have hstep1 : Step c c1 := by cases c; exact hs1
  have hmem1' : σ1.mem = m0 := by rw [hmem1]; exact hHead.mem
  have hpc1 : σ1.regs.get? Register.PC = some (0x80002d10#64 : BitVec 64) := by
    have h := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x80002d0c#64) 4 = (0x80002d10#64 : BitVec 64) from by decide] at h
  have hx18_1 : σ1.regs.get? Register.x18 = some (0#64 : BitVec 64) := by
    have h := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext_count_eg7 cb0 cb1 cb2 cb3 0 (by omega) hcrec] at h
  have hx20_1 := obs_alu_other' hobs1 Register.x20 (by decide) hHead.env4
  have hx19_1 := obs_alu_other' hobs1 Register.x19 (by decide) hHead.name3
  have hx21_1 := obs_alu_other' hobs1 Register.x21 (by decide) hHead.value5
  have hra_1 := obs_alu_other' hobs1 Register.x1 (by decide) hHead.ra
  have hsp_1 := obs_alu_other' hobs1 Register.x2 (by decide) hHead.sp2
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hblez : zopz0zKzJ_s (0#64) (0#64) = true := by decide
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80002d10_taken_es σ1 i1 (c.steps + 1) (0x80002d10#64) vmi1
      (0#64) hG1 hpc1 hmi1 hx18_1
      (by rw [hmem1']; exact hHead.mem ▸ hHead.loadedSet) rfl hblez hi1
  let c2 : Config := ⟨σ2, i2, c.steps + 2⟩
  have hstep2 : Step c1 c2 := hs2
  have hmem2' : σ2.mem = m0 := by rw [hmem2]; exact hmem1'
  have hpc2 : σ2.regs.get? Register.PC = some (0x80002d90#64 : BitVec 64) := by
    have h := obs_btaken_pc hobs2
    rwa [show (0x80002d10#64 : BitVec 64) + sign_extend (m := 64) (0x0080#13) =
      (0x80002d90#64 : BitVec 64) from by decide] at h
  have hx18_2 := obs_btaken_other' hobs2 Register.x18 (by decide) hx18_1
  have hx20_2 := obs_btaken_other' hobs2 Register.x20 (by decide) hx20_1
  have hx19_2 := obs_btaken_other' hobs2 Register.x19 (by decide) hx19_1
  have hx21_2 := obs_btaken_other' hobs2 Register.x21 (by decide) hx21_1
  have hra_2 := obs_btaken_other' hobs2 Register.x1 (by decide) hra_1
  have hsp_2 := obs_btaken_other' hobs2 Register.x2 (by decide) hsp_1
  obtain ⟨vmi2, hmi2⟩ := obs_btaken_minstret hobs2
  refine ⟨c2, (fun R => c2.σ.regs.get? R),
    (Steps.single hstep1).trans (Steps.single hstep2), ?_, ?_⟩
  refine
    { good := hG2, loadedG := ?_, loadedS := ?_, mem := hmem2', pc := hpc2,
      env4 := hx20_2, name3 := hx19_2, out5 := hx21_2, count2 := hx18_2,
      ra := hra_2, sp2 := hsp_2, minstret := ⟨vmi2, hmi2⟩, tick := hi2,
      frame := by rw [hEnvEq]; exact hHead.frame,
      names := by simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hPnSmall] using hNames,
      count_eq := by simp [hEmpty], ghost := fun _ _ => rfl }
  · rw [hmem2']; exact hHead.mem ▸ hHead.loadedSet
  · rw [hmem2']; exact hHead.mem ▸ hHead.loadedStrcmp
  · rw [hobs2.out, sailOutput_sigmaPost_branch_taken,
      hobs1.out, sailOutput_sigmaPost_alu]


#print axioms env_set_parent_scan_start
#print axioms env_set_parent_empty

end Vsa.Sim
