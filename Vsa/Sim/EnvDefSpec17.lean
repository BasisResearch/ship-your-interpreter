import Vsa.Sim.EnvDefSpec16
import Vsa.Sim.EnvDefSpec5
import Vsa.Sim.EnvDefSpec6
import Vsa.Sim.EnvDefSpec7
import Vsa.Sim.EnvDefSpec8
import Vsa.Sim.EnvDefSpec9
import Vsa.Sim.EnvDefSpec10
import Vsa.Sim.EnvDefSpec11
import Vsa.Sim.EnvDefSpec12
import Vsa.Sim.EnvDefSpec13
import Vsa.Sim.EnvDefSpec14

/-! # `env_define` complete straight-line prologue -/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (Config Step Steps)
open Vsa.MemRepr
open Vsa.Sim.Code (Env_defineLoaded StrcmpLoaded)

namespace Vsa.Sim

/-- Execute the thirteen straight-line prologue instructions from entry through the
`blez s3` guard at `0x80002a90`. -/
theorem env_define_prologue
    (sp env name pv r v18 v20 v21 v8 v9 v22 savedS3 vmi : BitVec 64)
    (pn hit count : Nat) (c : Config)
    (hRG : EnvDefRegions sp.toNat env.toNat pv.toNat pn hit count)
    (hG : GoodState c.σ) (hloaded : Env_defineLoaded c.σ.mem)
    (hstrloaded : StrcmpLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x80002a5c#64 : BitVec 64))
    (hentry : EnvDefineEntry c.σ sp env name pv r v18 v20 v21 v8 v9 v22)
    (hs3 : c.σ.regs.get? Register.x19 = some savedS3)
    (hmi : c.σ.regs.get? Register.minstret = some vmi)
    (hread : read32 c.σ.mem env.toNat = some count)
    (htick : c.tick < 2) :
    ∃ c' vmi', Steps c c' ∧
      c'.σ.regs.get? Register.PC = some (0x80002a90#64 : BitVec 64) ∧
      EnvDefinePrologueReady c'.σ sp env name pv ∧
      c'.σ.regs.get? Register.x19 = some (BitVec.ofNat 64 count) ∧
      c'.σ.regs.get? Register.minstret = some vmi' ∧
      GoodState c'.σ ∧ Env_defineLoaded c'.σ.mem ∧ StrcmpLoaded c'.σ.mem ∧
      c'.tick < 2 := by
  obtain ⟨c1, vmi1, hs1, hpc1, hcarryRead1, hs3_1, hmi1, hG1,
      hloaded1, hstrloaded1, htick1⟩ :=
    env_define_frame_alloc sp env name pv r v18 v20 v21 v8 v9 v22 savedS3 vmi count c
      hG hloaded hstrloaded hpc hentry hs3 hmi hread htick
  obtain ⟨c2, vmi2, hs2, hpc2, hcarry2, _hs3_2, hmi2, hG2,
      hloaded2, hstrloaded2, hread2, htick2⟩ :=
    env_define_spill_s3 env name pv r sp v18 v20 v21 v8 v9 v22 savedS3 vmi1
      pn hit count c1 hRG hG1 hloaded1 hstrloaded1 hpc1 hcarryRead1.1 hs3_1 hmi1
      hcarryRead1.2 htick1
  obtain ⟨c3, vmi3, hs3step, hpc3, hcount3, hcarry3, hmi3, hG3,
      hloaded3, hstrloaded3, htick3⟩ :=
    env_define_count_load env name pv r sp v18 v20 v21 v8 v9 v22 vmi2
      pn hit count c2 hRG hG2 hloaded2 hstrloaded2 hpc2 hcarry2 hmi2 hread2 htick2
  obtain ⟨c4, vmi4, hs4, hpc4, hcarry4, hcount4, hmi4, hG4,
      hloaded4, hstrloaded4, htick4⟩ :=
    env_define_spill_s2 env name pv r sp v18 v20 v21 v8 v9 v22
      (BitVec.ofNat 64 count) vmi3 pn hit count c3 hRG hG3 hloaded3 hstrloaded3
      hpc3 hcarry3 hcount3 hmi3 htick3
  obtain ⟨c5, vmi5, hs5, hpc5, hcarry5, hcount5, hmi5, hG5,
      hloaded5, hstrloaded5, htick5⟩ :=
    env_define_spill_s4 env name pv r sp v18 v20 v21 v8 v9 v22
      (BitVec.ofNat 64 count) vmi4 pn hit count c4 hRG hG4 hloaded4 hstrloaded4
      hpc4 hcarry4 hcount4 hmi4 htick4
  obtain ⟨c6, vmi6, hs6, hpc6, hcarry6, hcount6, hmi6, hG6,
      hloaded6, hstrloaded6, htick6⟩ :=
    env_define_spill_s5 env name pv r sp v18 v20 v21 v8 v9 v22
      (BitVec.ofNat 64 count) vmi5 pn hit count c5 hRG hG5 hloaded5 hstrloaded5
      hpc5 hcarry5 hcount5 hmi5 htick5
  obtain ⟨c7, vmi7, hs7, hpc7, hcarry7, hcount7, hmi7, hG7,
      hloaded7, hstrloaded7, htick7⟩ :=
    env_define_spill_ra env name pv r sp v18 v20 v21 v8 v9 v22
      (BitVec.ofNat 64 count) vmi6 pn hit count c6 hRG hG6 hloaded6 hstrloaded6
      hpc6 hcarry6 hcount6 hmi6 htick6
  obtain ⟨c8, vmi8, hs8, hpc8, hcarry8, hcount8, hmi8, hG8,
      hloaded8, hstrloaded8, htick8⟩ :=
    env_define_spill_s0 env name pv r sp v18 v20 v21 v8 v9 v22
      (BitVec.ofNat 64 count) vmi7 pn hit count c7 hRG hG7 hloaded7 hstrloaded7
      hpc7 hcarry7 hcount7 hmi7 htick7
  obtain ⟨c9, vmi9, hs9, hpc9, hcarry9, hcount9, hmi9, hG9,
      hloaded9, hstrloaded9, htick9⟩ :=
    env_define_spill_s1 env name pv r sp v18 v20 v21 v8 v9 v22
      (BitVec.ofNat 64 count) vmi8 pn hit count c8 hRG hG8 hloaded8 hstrloaded8
      hpc8 hcarry8 hcount8 hmi8 htick8
  obtain ⟨c10, vmi10, hs10, hpc10, hcarry10, hcount10, hmi10, hG10,
      hloaded10, hstrloaded10, htick10⟩ :=
    env_define_spill_s6 env name pv r sp v18 v20 v21 v8 v9 v22
      (BitVec.ofNat 64 count) vmi9 pn hit count c9 hRG hG9 hloaded9 hstrloaded9
      hpc9 hcarry9 hcount9 hmi9 htick9
  obtain ⟨c11, vmi11, hs11, hpc11, hmove1, hcount11, hmi11, hG11,
      hloaded11, hstrloaded11, htick11⟩ :=
    env_define_move_s4 env name pv r sp v18 v20 v21 v8 v9 v22
      (BitVec.ofNat 64 count) vmi10 c10 hG10 hloaded10 hstrloaded10 hpc10 hcarry10
      hcount10 hmi10 htick10
  obtain ⟨c12, vmi12, hs12, hpc12, hmove2, hcount12, hmi12, hG12,
      hloaded12, hstrloaded12, htick12⟩ :=
    env_define_move_s2 sp env name pv (BitVec.ofNat 64 count) vmi11 c11
      hG11 hloaded11 hstrloaded11 hpc11 hmove1 hcount11 hmi11 htick11
  obtain ⟨c13, vmi13, hs13, hpc13, hready13, hcount13, hmi13, hG13,
      hloaded13, hstrloaded13, htick13⟩ :=
    env_define_move_s5 sp env name pv (BitVec.ofNat 64 count) vmi12 c12
      hG12 hloaded12 hstrloaded12 hpc12 hmove2 hcount12 hmi12 htick12
  have hsteps : Steps c c13 :=
    (Steps.single hs1).trans (Steps.single hs2) |>.trans (Steps.single hs3step)
      |>.trans (Steps.single hs4) |>.trans (Steps.single hs5)
      |>.trans (Steps.single hs6) |>.trans (Steps.single hs7)
      |>.trans (Steps.single hs8) |>.trans (Steps.single hs9)
      |>.trans (Steps.single hs10) |>.trans (Steps.single hs11)
      |>.trans (Steps.single hs12) |>.trans (Steps.single hs13)
  exact ⟨c13, vmi13, hsteps, hpc13, hready13, hcount13, hmi13, hG13,
    hloaded13, hstrloaded13, htick13⟩

end Vsa.Sim
