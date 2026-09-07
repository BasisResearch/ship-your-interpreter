import Vsa.Sim.EnvGetSpec4
import Vsa.Sim.EnvSetSites
import Vsa.Sim.StoreInvariant

/-!
# Parent transition for `env_set`

The successful assignment path may miss several frames before updating the
first matching slot.  These carriers retain the exact machine state across
the `env->parent` backedge.  The memory is unchanged on a miss.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- State after the current frame's name scan has found no match. -/
structure SetScanMissSt (g : (R : Register) → Option (RegisterType R))
    (env name valuePtr count namesPtr r sp : BitVec 64)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs)
    (φf φc : Vsa.While.Addr → Nat) (out0 : Array String)
    (m0 : Mem) (c : Config) : Prop where
  good : GoodState c.σ
  loadedSet : Env_setLoaded c.σ.mem
  loadedStrcmp : StrcmpLoaded c.σ.mem
  mem : c.σ.mem = m0
  pc : c.σ.regs.get? Register.PC = some (0x80002d90#64 : BitVec 64)
  env4 : c.σ.regs.get? Register.x20 = some env
  name3 : c.σ.regs.get? Register.x19 = some name
  value5 : c.σ.regs.get? Register.x21 = some valuePtr
  count2 : c.σ.regs.get? Register.x18 = some count
  ra : c.σ.regs.get? Register.x1 = some r
  sp2 : c.σ.regs.get? Register.x2 = some sp
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  output : c.σ.sailOutput = out0
  frame : FrameRepr m0 N φf φc env.toNat f
  names : ScanNames m0 namesPtr.toNat name nameStr f
  count_eq : count.toNat = f.vars.length
  frame_miss : FrameMiss f.vars nameStr
  ghost : ∀ R : Register, AbiPreserved R = true → c.σ.regs.get? R = g R

/-- State at the next parent frame's count load. -/
structure SetParentHeadSt (g : (R : Register) → Option (RegisterType R))
    (parent name valuePtr r sp : BitVec 64) (parentAddr : Vsa.While.Addr)
    (parentFrame : Vsa.While.Frame) (N : NativeAddrs)
    (φf φc : Vsa.While.Addr → Nat) (out0 : Array String)
    (m0 : Mem) (c : Config) : Prop where
  good : GoodState c.σ
  loadedSet : Env_setLoaded c.σ.mem
  loadedStrcmp : StrcmpLoaded c.σ.mem
  mem : c.σ.mem = m0
  pc : c.σ.regs.get? Register.PC = some (0x80002d0c#64 : BitVec 64)
  env4 : c.σ.regs.get? Register.x20 = some parent
  parent_eq : parent = BitVec.ofNat 64 (φf parentAddr)
  name3 : c.σ.regs.get? Register.x19 = some name
  value5 : c.σ.regs.get? Register.x21 = some valuePtr
  ra : c.σ.regs.get? Register.x1 = some r
  sp2 : c.σ.regs.get? Register.x2 = some sp
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  output : c.σ.sailOutput = out0
  frame : FrameRepr m0 N φf φc (φf parentAddr) parentFrame
  ghost : ∀ R : Register, AbiPreserved R = true → c.σ.regs.get? R = g R

/-- A semantic parent-chain step and the two machine instructions agree. -/
theorem env_set_parent_step
    (g : (R : Register) → Option (RegisterType R))
    (env name valuePtr count namesPtr r sp : BitVec 64)
    (f parentFrame : Vsa.While.Frame) (nameStr : String)
    (parentAddr : Vsa.While.Addr) (N : NativeAddrs)
    (φf φc : Vsa.While.Addr → Nat) (out0 : Array String)
    (m0 : Mem) (c : Config)
    (hMiss : SetScanMissSt g env name valuePtr count namesPtr r sp
      f nameStr N φf φc out0 m0 c)
    (hParent : f.parent = some parentAddr)
    (hParentFrame : FrameRepr m0 N φf φc (φf parentAddr) parentFrame)
    (henvLo : 0x80000000 ≤ env.toNat)
    (henvHi : env.toNat + 32 ≤ 0x100000000)
    (henvWin : env.toNat + 32 ≤ tohostAddr ∨ tohostAddr + 8 ≤ env.toNat)
    (henvAlign : env.toNat % 8 = 0)
    (hParentSmall : φf parentAddr < 2^64) :
    ∃ c' g', Steps c c' ∧
      SetParentHeadSt g' (BitVec.ofNat 64 (φf parentAddr)) name valuePtr r sp
        parentAddr parentFrame N φf φc out0 m0 c' := by
  obtain ⟨_, _, _, hparentRead⟩ := hMiss.frame
  rw [hParent] at hparentRead
  obtain ⟨hread, hparentNe⟩ := hparentRead
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7,
    hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, _⟩ :=
    read64_bytes_eg4 m0 (env.toNat + 24) (φf parentAddr) hread
  have hadd : (env + sign_extend (m := 64) (0x018#12)).toNat = env.toNat + 24 := by
    rw [BitVec.toNat_add]
    have hs : (sign_extend (m := 64) (0x018#12) : BitVec 64).toNat = 24 := by decide
    rw [hs, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨vmi, hmi⟩ := hMiss.minstret
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80002d90_es c.σ c.tick c.steps (0x80002d90#64) vmi env
      b0 b1 b2 b3 b4 b5 b6 b7 hMiss.good hMiss.pc hmi hMiss.env4 hMiss.loadedSet rfl
      (by rw [hadd]; omega) (by rw [hadd]; omega)
      (by rw [hadd]; rcases henvWin with h | h <;> omega)
      (by rw [hadd, hMiss.mem]; exact hb0) (by rw [hadd, hMiss.mem]; exact hb1)
      (by rw [hadd, hMiss.mem]; exact hb2) (by rw [hadd, hMiss.mem]; exact hb3)
      (by rw [hadd, hMiss.mem]; exact hb4) (by rw [hadd, hMiss.mem]; exact hb5)
      (by rw [hadd, hMiss.mem]; exact hb6) (by rw [hadd, hMiss.mem]; exact hb7) hMiss.tick
  let c1 : Config := ⟨σ1, i1, c.steps + 1⟩
  have hstep1 : Step c c1 := by cases c; exact hs1
  have hmem1' : σ1.mem = m0 := by rw [hmem1]; exact hMiss.mem
  have hpc1 : σ1.regs.get? Register.PC = some (0x80002d94#64 : BitVec 64) := by
    have h := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x80002d90#64) 4 = (0x80002d94#64 : BitVec 64) from by decide] at h
  have hval : (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)) : BitVec 64) = BitVec.ofNat 64 (φf parentAddr) :=
    ld_value_eq_read64 m0 (env.toNat + 24) (φf parentAddr)
      b0 b1 b2 b3 b4 b5 b6 b7 hread hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
  have hx20_1 : σ1.regs.get? Register.x20 = some (BitVec.ofNat 64 (φf parentAddr)) := by
    have h := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hval] at h
  have hx19_1 := obs_alu_other' hobs1 Register.x19 (by decide) hMiss.name3
  have hx21_1 := obs_alu_other' hobs1 Register.x21 (by decide) hMiss.value5
  have hra_1 := obs_alu_other' hobs1 Register.x1 (by decide) hMiss.ra
  have hsp_1 := obs_alu_other' hobs1 Register.x2 (by decide) hMiss.sp2
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hnonzero : (BitVec.ofNat 64 (φf parentAddr) != (0#64 : BitVec 64)) = true := by
    rw [bne_iff_ne]
    intro hz
    have hzNat := congrArg BitVec.toNat hz
    simp only [BitVec.toNat_ofNat] at hzNat
    rw [Nat.mod_eq_of_lt hParentSmall] at hzNat
    exact hparentNe hzNat
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80002d94_taken_es σ1 i1 (c.steps + 1) (0x80002d94#64) vmi1
      (BitVec.ofNat 64 (φf parentAddr)) hG1 hpc1 hmi1 hx20_1
      (by rw [hmem1']; exact hMiss.mem ▸ hMiss.loadedSet) rfl hnonzero hi1
  let c2 : Config := ⟨σ2, i2, c.steps + 1 + 1⟩
  have hstep2 : Step c1 c2 := hs2
  have hpc2 : σ2.regs.get? Register.PC = some (0x80002d0c#64 : BitVec 64) := by
    have h := obs_btaken_pc hobs2
    rwa [site_80002d94_taken_es_tgt] at h
  have hmem2' : σ2.mem = m0 := by rw [hmem2]; exact hmem1'
  have hx20_2 := obs_btaken_other' hobs2 Register.x20 (by decide) hx20_1
  have hx19_2 := obs_btaken_other' hobs2 Register.x19 (by decide) hx19_1
  have hx21_2 := obs_btaken_other' hobs2 Register.x21 (by decide) hx21_1
  have hra_2 := obs_btaken_other' hobs2 Register.x1 (by decide) hra_1
  have hsp_2 := obs_btaken_other' hobs2 Register.x2 (by decide) hsp_1
  obtain ⟨vmi2, hmi2⟩ := obs_btaken_minstret hobs2
  have hout2 : σ2.sailOutput = out0 := by
    rw [hobs2.out, sailOutput_sigmaPost_branch_taken,
      hobs1.out, sailOutput_sigmaPost_alu, hMiss.output]
  refine ⟨c2, (fun R => c2.σ.regs.get? R),
    (Steps.single hstep1).trans (Steps.single hstep2), ?_⟩
  refine
    { good := hG2, loadedSet := ?_, loadedStrcmp := ?_, mem := hmem2', pc := hpc2,
      env4 := hx20_2, parent_eq := rfl, name3 := hx19_2, value5 := hx21_2,
      ra := hra_2, sp2 := hsp_2, minstret := ⟨vmi2, hmi2⟩, tick := hi2,
      output := hout2, frame := hParentFrame, ghost := fun _ _ => rfl }
  · rw [hmem2']; exact hMiss.mem ▸ hMiss.loadedSet
  · rw [hmem2']; exact hMiss.mem ▸ hMiss.loadedStrcmp

#print axioms env_set_parent_step

end Vsa.Sim
