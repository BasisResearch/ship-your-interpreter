import Vsa.Sim.Skeleton
import Vsa.Sim.Retire
import Vsa.Sim.StepAddi
import Vsa.Sim.ExecuteAlu
import Vsa.Sim.Frame

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

abbrev sigma3_alu (σ : MState) (pc : BitVec 64) (rd_reg : Register)
    (v : RegisterType rd_reg) : MState :=
  {(afterNextPC (afterPrelude σ) pc) with
    regs := (afterNextPC (afterPrelude σ) pc).regs.insert rd_reg v}

theorem try_step_alu
    (σ : MState) (u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (ast : instruction) (rd_reg : Register) (v : RegisterType rd_reg)
    (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ) = .ok ast (afterPrelude σ))
    (hexec : (execute ast).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc rd_reg v))
    (hrd_npc : (rd_reg == Register.nextPC) = false)
    (hrd_mi : (rd_reg == Register.minstret_increment) = false)
    (hrd_ms : (rd_reg == Register.minstret) = false)
    (hrd_hart : (rd_reg == Register.hart_state) = false)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0) :
    (try_step u true).run σ
      = .ok false
          {(({(sigma3_alu σ pc rd_reg v) with regs := (sigma3_alu σ pc rd_reg v).regs.insert Register.PC (BitVec.addInt pc 4)}) : MState) with
            regs := (({(sigma3_alu σ pc rd_reg v) with regs := (sigma3_alu σ pc rd_reg v).regs.insert Register.PC (BitVec.addInt pc 4)}) : MState).regs.insert Register.minstret (BitVec.addInt vminstret 1)} := by
  exact try_step_retire (Fetched.of_bytes hG hpc hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec) hexec
    ⟨by reg_reads [hrd_hart, hG.hart_state], by reg_reads [hrd_npc], by reg_reads [hrd_mi],
     by reg_reads [hrd_ms, hminstret]⟩

abbrev sigmaPost_alu (σ : MState) (pc vminstret : BitVec 64) (rd_reg : Register)
    (v : RegisterType rd_reg) : MState :=
  {(({(sigma3_alu σ pc rd_reg v) with regs := (sigma3_alu σ pc rd_reg v).regs.insert Register.PC (BitVec.addInt pc 4)}) : MState) with
    regs := (({(sigma3_alu σ pc rd_reg v) with regs := (sigma3_alu σ pc rd_reg v).regs.insert Register.PC (BitVec.addInt pc 4)}) : MState).regs.insert Register.minstret (BitVec.addInt vminstret 1)}

theorem get?_sigmaPost_alu (σ : MState) (pc vminstret : BitVec 64) (rd_reg : Register)
    (v : RegisterType rd_reg) (R : Register)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h3 : (rd_reg == R) = false) (h4 : (Register.nextPC == R) = false)
    (h5 : (Register.minstret_increment == R) = false) :
    (sigmaPost_alu σ pc vminstret rd_reg v).regs.get? R = σ.regs.get? R := by
  reg_reads [h1, h2, h3, h4, h5]

theorem goodstate_sigmaPost_alu (σ : MState) (pc vminstret : BitVec 64) (rd_reg : Register)
    (hrd : NonPinned rd_reg) (v : RegisterType rd_reg)
    (hG : GoodState σ) : GoodState (sigmaPost_alu σ pc vminstret rd_reg v) :=
  ((((hG.insert_nonpinned (by decide) _).insert_nonpinned (by decide) _).insert_nonpinned
    (r := rd_reg) hrd v).retirePost _ _)

theorem stepOnce_alu_notick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (ast : instruction) (rd_reg : Register) (v : RegisterType rd_reg)
    (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ) = .ok ast (afterPrelude σ))
    (hexec : (execute ast).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc rd_reg v))
    (hrd_npc : (rd_reg == Register.nextPC) = false)
    (hrd_mi : (rd_reg == Register.minstret_increment) = false)
    (hrd_ms : (rd_reg == Register.minstret) = false)
    (hrd_hart : (rd_reg == Register.hart_state) = false)
    (hrd : NonPinned rd_reg)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (htick : i + 1 ≠ 2) :
    (stepOnce i u).run σ = .ok (.inr (i + 1, u + 1)) (sigmaPost_alu σ pc vminstret rd_reg v) :=
  stepOnce_retire_notick (try_step_alu σ u pc vminstret w ast rd_reg v b0 b1 b2 b3
      hG hpc hminstret hword hnotrvc hdec hexec hrd_npc hrd_mi hrd_ms hrd_hart hb0 hb1 hb2 hb3 hlo hhi halign)
    hG (goodstate_sigmaPost_alu σ pc vminstret rd_reg hrd v hG) htick

noncomputable abbrev sigmaTick_alu
    (σ : MState) (pc vminstret : BitVec 64) (rd_reg : Register) (v : RegisterType rd_reg)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64) : MState :=
  {(sigmaPost_alu σ pc vminstret rd_reg v) with
    regs := (((((sigmaPost_alu σ pc vminstret rd_reg v).regs.insert Register.mcycle (BitVec.addInt vmcycle 1)).insert Register.mtime (BitVec.addInt vmtime 1)).insert Register.mip (Sail.BitVec.updateSubrange vmip 7 7 (bool_to_bit (zopz0zIzJ_u vmtimecmp (BitVec.addInt vmtime 1))))))}

theorem stepOnce_alu_tick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (ast : instruction) (rd_reg : Register) (v : RegisterType rd_reg)
    (b0 b1 b2 b3 : BitVec 8)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmip : (sigmaPost_alu σ pc vminstret rd_reg v).regs.get? Register.mip = some vmip)
    (hmtime : (sigmaPost_alu σ pc vminstret rd_reg v).regs.get? Register.mtime = some vmtime)
    (hmtimecmp : (sigmaPost_alu σ pc vminstret rd_reg v).regs.get? Register.mtimecmp = some vmtimecmp)
    (hmcycle : (sigmaPost_alu σ pc vminstret rd_reg v).regs.get? Register.mcycle = some vmcycle)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ) = .ok ast (afterPrelude σ))
    (hexec : (execute ast).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc rd_reg v))
    (hrd_npc : (rd_reg == Register.nextPC) = false)
    (hrd_mi : (rd_reg == Register.minstret_increment) = false)
    (hrd_ms : (rd_reg == Register.minstret) = false)
    (hrd_hart : (rd_reg == Register.hart_state) = false)
    (hrd : NonPinned rd_reg)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (htick : i + 1 = 2) :
    (stepOnce i u).run σ
      = .ok (.inr (0, u + 1)) (sigmaTick_alu σ pc vminstret rd_reg v vmip vmtime vmtimecmp vmcycle) :=
  stepOnce_retire_tick (try_step_alu σ u pc vminstret w ast rd_reg v b0 b1 b2 b3
      hG hpc hminstret hword hnotrvc hdec hexec hrd_npc hrd_mi hrd_ms hrd_hart hb0 hb1 hb2 hb3 hlo hhi halign)
    hG (goodstate_sigmaPost_alu σ pc vminstret rd_reg hrd v hG) hmip hmtime hmtimecmp hmcycle htick

theorem step_alu_notick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (ast : instruction) (rd_reg : Register) (v : RegisterType rd_reg)
    (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ) = .ok ast (afterPrelude σ))
    (hexec : (execute ast).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc rd_reg v))
    (hrd_npc : (rd_reg == Register.nextPC) = false)
    (hrd_mi : (rd_reg == Register.minstret_increment) = false)
    (hrd_ms : (rd_reg == Register.minstret) = false)
    (hrd_hart : (rd_reg == Register.hart_state) = false)
    (hrd : NonPinned rd_reg)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (htick : i + 1 ≠ 2) :
    Vsa.Machine.Step ⟨σ, i, u⟩ ⟨sigmaPost_alu σ pc vminstret rd_reg v, i + 1, u + 1⟩
    ∧ GoodState (sigmaPost_alu σ pc vminstret rd_reg v) :=
  step_retire_notick (try_step_alu σ u pc vminstret w ast rd_reg v b0 b1 b2 b3
      hG hpc hminstret hword hnotrvc hdec hexec hrd_npc hrd_mi hrd_ms hrd_hart hb0 hb1 hb2 hb3 hlo hhi halign)
    hG (goodstate_sigmaPost_alu σ pc vminstret rd_reg hrd v hG) htick

theorem step_alu_tick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (ast : instruction) (rd_reg : Register) (v : RegisterType rd_reg)
    (b0 b1 b2 b3 : BitVec 8)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmip : (sigmaPost_alu σ pc vminstret rd_reg v).regs.get? Register.mip = some vmip)
    (hmtime : (sigmaPost_alu σ pc vminstret rd_reg v).regs.get? Register.mtime = some vmtime)
    (hmtimecmp : (sigmaPost_alu σ pc vminstret rd_reg v).regs.get? Register.mtimecmp = some vmtimecmp)
    (hmcycle : (sigmaPost_alu σ pc vminstret rd_reg v).regs.get? Register.mcycle = some vmcycle)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ) = .ok ast (afterPrelude σ))
    (hexec : (execute ast).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc rd_reg v))
    (hrd_npc : (rd_reg == Register.nextPC) = false)
    (hrd_mi : (rd_reg == Register.minstret_increment) = false)
    (hrd_ms : (rd_reg == Register.minstret) = false)
    (hrd_hart : (rd_reg == Register.hart_state) = false)
    (hrd : NonPinned rd_reg)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (htick : i + 1 = 2) :
    Vsa.Machine.Step ⟨σ, i, u⟩
      ⟨sigmaTick_alu σ pc vminstret rd_reg v vmip vmtime vmtimecmp vmcycle, 0, u + 1⟩
    ∧ GoodState (sigmaTick_alu σ pc vminstret rd_reg v vmip vmtime vmtimecmp vmcycle) :=
  step_retire_tick (try_step_alu σ u pc vminstret w ast rd_reg v b0 b1 b2 b3
      hG hpc hminstret hword hnotrvc hdec hexec hrd_npc hrd_mi hrd_ms hrd_hart hb0 hb1 hb2 hb3 hlo hhi halign)
    hG (goodstate_sigmaPost_alu σ pc vminstret rd_reg hrd v hG) hmip hmtime hmtimecmp hmcycle htick

end Vsa.Sim
