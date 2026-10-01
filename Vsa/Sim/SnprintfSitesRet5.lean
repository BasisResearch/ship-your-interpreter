import Vsa.Sim.RegPins
import Vsa.Sim.DecodeNF
import Vsa.Sim.Code.Strcpy
import Vsa.Sim.RamReadPins
import Vsa.Sim.StrlenMagic
import Vsa.Sim.ValueSites

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem get?_sigmaTick_jalr (σ : MState) (pc vminstret tgt : BitVec 64)
    (rd_reg : Register) (link : RegisterType rd_reg)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64) (R : Register)
    (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false) :
    (sigmaTick_jalr σ pc vminstret tgt rd_reg link vmip vmtime vmtimecmp vmcycle).regs.get? R
      = (sigmaPost_jalr σ pc vminstret tgt rd_reg link).regs.get? R := by
  show (((((sigmaPost_jalr σ pc vminstret tgt rd_reg link).regs.insert Register.mcycle _).insert
      Register.mtime _).insert Register.mip _)).get? R = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hmi, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hmt, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hmc, dif_neg, reduceCtorEq, not_false_eq_true]

theorem stepObs_jalr
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vrs1 : BitVec 64)
    (w : BitVec 32) (imm : BitVec 12) (rs1 rd : regidx) (rd_reg : Register)
    (link : RegisterType rd_reg) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.JALR (imm, rs1, rd)) (afterPrelude σ))
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vrs1 (afterNextPC (afterPrelude σ) pc))
    (htgt : (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1).toNat % 4 = 0)
    (hrd_npc : (rd_reg == Register.nextPC) = false)
    (hrd_mi : (rd_reg == Register.minstret_increment) = false)
    (hrd_ms : (rd_reg == Register.minstret) = false)
    (hrd_hart : (rd_reg == Register.hart_state) = false)
    (hrd : NonPinned rd_reg)
    (hwr : (wX_bits rd (BitVec.addInt pc 4)).run
        {(afterNextPC (afterPrelude σ) pc) with
          regs := (afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC
            (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)}
        = .ok () (sigma3_jalr σ pc (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg link))
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jalr σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)
          rd_reg link) := by
  by_cases htick : i + 1 = 2
  · have hGp := goodstate_sigmaPost_jalr σ pc vminstret
      (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg hrd link hG
    obtain ⟨vmip, hmip⟩ := hGp.mip
    obtain ⟨vmtime, hmtime⟩ := hGp.mtime
    obtain ⟨vmtimecmp, hmtimecmp⟩ := hGp.mtimecmp
    obtain ⟨vmcycle, hmcycle⟩ := hGp.mcycle
    obtain ⟨hstep, hGt⟩ := step_jalr_tick σ i u pc vminstret vrs1 w imm rs1 rd rd_reg link
      b0 b1 b2 b3 vmip vmtime vmtimecmp vmcycle
      hG hpc hminstret hmip hmtime hmtimecmp hmcycle
      hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec hrs1 htgt
      hrd_npc hrd_mi hrd_ms hrd_hart hrd hwr htick
    refine ⟨_, 0, hstep, by decide, hGt, rfl, ?_, rfl⟩
    intro R hmc hmt hmi
    exact get?_sigmaTick_jalr σ pc vminstret _ rd_reg link vmip vmtime vmtimecmp vmcycle
      R hmc hmt hmi
  · obtain ⟨hstep, hGt⟩ := step_jalr_notick σ i u pc vminstret vrs1 w imm rs1 rd rd_reg link
      b0 b1 b2 b3 hG hpc hminstret hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec hrs1 htgt
      hrd_npc hrd_mi hrd_ms hrd_hart hrd hwr htick
    exact ⟨_, i + 1, hstep, by omega, hGt, rfl, ReadsLikePost.rfl _⟩

theorem post_jalr_pc (σ : MState) (pc vminstret tgt : BitVec 64)
    (rd_reg : Register) (link : RegisterType rd_reg) :
    (sigmaPost_jalr σ pc vminstret tgt rd_reg link).regs.get? Register.PC = some tgt := by
  show ((((sigma3_jalr σ pc tgt rd_reg link).regs.insert Register.PC tgt).insert
    Register.minstret (BitVec.addInt vminstret 1))).get? Register.PC = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.minstret == Register.PC) = false from by decide, dif_neg,
    reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert_self]

theorem post_jalr_rd (σ : MState) (pc vminstret tgt : BitVec 64)
    (rd_reg : Register) (link : RegisterType rd_reg)
    (h1 : (Register.minstret == rd_reg) = false) (h2 : (Register.PC == rd_reg) = false) :
    (sigmaPost_jalr σ pc vminstret tgt rd_reg link).regs.get? rd_reg = some link := by
  show ((((sigma3_jalr σ pc tgt rd_reg link).regs.insert Register.PC tgt).insert
    Register.minstret (BitVec.addInt vminstret 1))).get? rd_reg = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [h1, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [h2, dif_neg, reduceCtorEq, not_false_eq_true]
  show (((afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC tgt).insert
    rd_reg link).get? rd_reg = _
  rw [Std.ExtDHashMap.get?_insert_self]

theorem post_jalr_other (σ : MState) (pc vminstret tgt : BitVec 64)
    (rd_reg : Register) (link : RegisterType rd_reg) (R : Register)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h3 : (rd_reg == R) = false) (h4 : (Register.nextPC == R) = false)
    (h5 : (Register.minstret_increment == R) = false) :
    (sigmaPost_jalr σ pc vminstret tgt rd_reg link).regs.get? R = σ.regs.get? R :=
  get?_sigmaPost_jalr σ pc vminstret tgt rd_reg link R h1 h2 h3 h4 h5

theorem obs_jalr_pc {σ' σ : MState} {pc vm tgt : BitVec 64}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jalr σ pc vm tgt rd_reg link)) :
    σ'.regs.get? Register.PC = some tgt :=
  readback σ' _ hobs Register.PC (by decide) (by decide) (by decide)
    (post_jalr_pc σ pc vm tgt rd_reg link)

theorem obs_jalr_rd {σ' σ : MState} {pc vm tgt : BitVec 64}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jalr σ pc vm tgt rd_reg link))
    (hmc : (Register.mcycle == rd_reg) = false) (hmt : (Register.mtime == rd_reg) = false)
    (hmi : (Register.mip == rd_reg) = false)
    (h1 : (Register.minstret == rd_reg) = false) (h2 : (Register.PC == rd_reg) = false) :
    σ'.regs.get? rd_reg = some link :=
  readback σ' _ hobs rd_reg hmc hmt hmi (post_jalr_rd σ pc vm tgt rd_reg link h1 h2)

theorem obs_jalr_minstret {σ' σ : MState} {pc vm tgt : BitVec 64}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jalr σ pc vm tgt rd_reg link)) :
    ∃ w, σ'.regs.get? Register.minstret = some w := by
  refine ⟨BitVec.addInt vm 1, readback σ' _ hobs Register.minstret (w := BitVec.addInt vm 1)
    (by decide) (by decide) (by decide) ?_⟩
  show ((((sigma3_jalr σ pc tgt rd_reg link).regs.insert Register.PC tgt).insert
    Register.minstret (BitVec.addInt vm 1))).get? Register.minstret = _
  rw [Std.ExtDHashMap.get?_insert_self]

end Vsa.Sim
