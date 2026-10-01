import Vsa.Sim.DivSites2
import Vsa.Sim.DecodeNF

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem site3_80004734
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Vsa.Sim.Code.__moddi3Loaded σ.mem)
    (hpcv : pc = (0x80004734#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jal σ pc vminstret (0x1fff78#21) Register.x1 (BitVec.addInt pc 4)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__moddi3_at_80004734 hmem
  exact (stepObs_exec _ vminstret (Fetched.of_word (0xf79ff0ef#32) hG hpc hb0 hb1 hb2 hb3)
    (execute_jal_char (0x1fff78#21) (regidx.Regidx 0x01#5) _ (0x80004734#64) _ _ _ (by reg_reads []) (by reg_reads [hpc])
      (by reg_reads [hG.misa]) (by decide) (wX_bits_gpr _ (BitVec.addInt (0x80004734#64) 4) 1 (by decide) (by decide)))
    (((RetireReads.prelude hG hminstret _).jump _).write _)
    (((hG.prelude _).insert_nonpinned (by decide) _).insert_nonpinned (by decide) _) hi :)

theorem site3_8000474c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Vsa.Sim.Code.__moddi3Loaded σ.mem)
    (hpcv : pc = (0x8000474c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jal σ pc vminstret (0x1fff60#21) Register.x1 (BitVec.addInt pc 4)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__moddi3_at_8000474c hmem
  exact (stepObs_exec _ vminstret (Fetched.of_word (0xf61ff0ef#32) hG hpc hb0 hb1 hb2 hb3)
    (execute_jal_char (0x1fff60#21) (regidx.Regidx 0x01#5) _ (0x8000474c#64) _ _ _ (by reg_reads []) (by reg_reads [hpc])
      (by reg_reads [hG.misa]) (by decide) (wX_bits_gpr _ (BitVec.addInt (0x8000474c#64) 4) 1 (by decide) (by decide)))
    (((RetireReads.prelude hG hminstret _).jump _).write _)
    (((hG.prelude _).insert_nonpinned (by decide) _).insert_nonpinned (by decide) _) hi :)

theorem site3_8000471c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Vsa.Sim.Code.__umoddi3Loaded σ.mem)
    (hpcv : pc = (0x8000471c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jal σ pc vminstret (0x1fff90#21) Register.x1 (BitVec.addInt pc 4)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__umoddi3_at_8000471c hmem
  exact (stepObs_exec _ vminstret (Fetched.of_word (0xf91ff0ef#32) hG hpc hb0 hb1 hb2 hb3)
    (execute_jal_char (0x1fff90#21) (regidx.Regidx 0x01#5) _ (0x8000471c#64) _ _ _ (by reg_reads []) (by reg_reads [hpc])
      (by reg_reads [hG.misa]) (by decide) (wX_bits_gpr _ (BitVec.addInt (0x8000471c#64) 4) 1 (by decide) (by decide)))
    (((RetireReads.prelude hG hminstret _).jump _).write _)
    (((hG.prelude _).insert_nonpinned (by decide) _).insert_nonpinned (by decide) _) hi :)

end Vsa.Sim
