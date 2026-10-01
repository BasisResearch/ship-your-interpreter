import Vsa.Sim.ObsAvoid
import Vsa.Sim.DecodeNF

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc
open Vsa.While (Frame)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem post_jal_pc_env (σ : MState) (pc vminstret : BitVec 64) (imm : BitVec 21)
    (rd_reg : Register) (link : RegisterType rd_reg) :
    (sigmaPost_jal σ pc vminstret imm rd_reg link).regs.get? Register.PC
      = some (pc + sign_extend (m := 64) imm) := by
  show ((((sigma3_jal σ pc imm rd_reg link).regs.insert Register.PC (pc + sign_extend (m := 64) imm)).insert
    Register.minstret (BitVec.addInt vminstret 1))).get? Register.PC = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.minstret == Register.PC) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert_self]

theorem post_jal_rd_env (σ : MState) (pc vminstret : BitVec 64) (imm : BitVec 21)
    (rd_reg : Register) (link : RegisterType rd_reg)
    (h1 : (Register.minstret == rd_reg) = false) (h2 : (Register.PC == rd_reg) = false) :
    (sigmaPost_jal σ pc vminstret imm rd_reg link).regs.get? rd_reg = some link := by
  show ((((sigma3_jal σ pc imm rd_reg link).regs.insert Register.PC (pc + sign_extend (m := 64) imm)).insert
    Register.minstret (BitVec.addInt vminstret 1))).get? rd_reg = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [h1, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [h2, dif_neg, reduceCtorEq, not_false_eq_true]
  show (((afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC
    (pc + sign_extend (m := 64) imm)).insert rd_reg link).get? rd_reg = _
  rw [Std.ExtDHashMap.get?_insert_self]

theorem obs_jal_pc_env {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link)) :
    σ'.regs.get? Register.PC = some (pc + sign_extend (m := 64) imm) :=
  readback σ' _ hobs Register.PC (by decide) (by decide) (by decide) (post_jal_pc_env σ pc vm imm rd_reg link)

theorem obs_jal_rd_env {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link))
    (hmc : (Register.mcycle == rd_reg) = false) (hmt : (Register.mtime == rd_reg) = false)
    (hmi : (Register.mip == rd_reg) = false)
    (h1 : (Register.minstret == rd_reg) = false) (h2 : (Register.PC == rd_reg) = false) :
    σ'.regs.get? rd_reg = some link :=
  readback σ' _ hobs rd_reg hmc hmt hmi (post_jal_rd_env σ pc vm imm rd_reg link h1 h2)

theorem obs_jal_other_env {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link)) (R : Register) {w : RegisterType R}
    (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h3 : (rd_reg == R) = false) (h4 : (Register.nextPC == R) = false)
    (h5 : (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w :=
  readback σ' _ hobs R hmc hmt hmi
    ((get?_sigmaPost_jal σ pc vm imm rd_reg link R h1 h2 h3 h4 h5).trans hσ)

theorem obs_jal_minstret_env {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link)) :
    ∃ w, σ'.regs.get? Register.minstret = some w := by
  refine ⟨BitVec.addInt vm 1, readback σ' _ hobs Register.minstret (w := BitVec.addInt vm 1)
    (by decide) (by decide) (by decide) ?_⟩
  show ((((sigma3_jal σ pc imm rd_reg link).regs.insert Register.PC (pc + sign_extend (m := 64) imm)).insert
    Register.minstret (BitVec.addInt vm 1))).get? Register.minstret = _
  rw [Std.ExtDHashMap.get?_insert_self]

theorem off0_addr (base : BitVec 64) : (base + sign_extend (m := 64) (0x000#12)).toNat = base.toNat := by
  rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide,
    BitVec.add_zero]

theorem off8_addr (base : BitVec 64) (h : base.toNat + 8 < 2^64) :
    (base + sign_extend (m := 64) (0x008#12)).toNat = base.toNat + 8 := by
  have hs : (sign_extend (m := 64) (0x008#12) : BitVec 64).toNat = 8 := by decide
  rw [BitVec.toNat_add, hs]; omega

theorem sp_sub16 (sp : BitVec 64) :
    (sp + sign_extend (m := 64) (0xff0#12)) = sp - 16#64 := by
  have hs : (sign_extend (m := 64) (0xff0#12) : BitVec 64) = -(16#64) := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [hs]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_sub]
  have hn : (-(16#64) : BitVec 64).toNat = 2^64 - 16 := by decide
  have h16 : (16#64 : BitVec 64).toNat = 16 := by decide
  rw [hn, h16]; have := sp.isLt; omega

theorem sp_sub16_toNat (sp : BitVec 64) (h : 16 ≤ sp.toNat) :
    (sp - 16#64).toNat = sp.toNat - 16 := by
  have h16 : (16#64 : BitVec 64).toNat = 16 := by decide
  rw [BitVec.toNat_sub, h16]
  have := sp.isLt
  omega

theorem read64_writeMap8_disjoint (mem : Std.ExtHashMap Nat (BitVec 8)) (a a8 : Nat)
    (d : BitVec (8 * 8)) (hdis : a + 8 ≤ a8 ∨ a8 + 8 ≤ a) :
    read64 (writeMap8 mem a8 d) a = read64 mem a := by
  have g0 := getElem_writeMap8_disjoint mem a8 a d (by omega)
  have g1 := getElem_writeMap8_disjoint mem a8 (a + 1) d (by omega)
  have g2 := getElem_writeMap8_disjoint mem a8 (a + 2) d (by omega)
  have g3 := getElem_writeMap8_disjoint mem a8 (a + 3) d (by omega)
  have g4 := getElem_writeMap8_disjoint mem a8 (a + 4) d (by omega)
  have g5 := getElem_writeMap8_disjoint mem a8 (a + 5) d (by omega)
  have g6 := getElem_writeMap8_disjoint mem a8 (a + 6) d (by omega)
  have g7 := getElem_writeMap8_disjoint mem a8 (a + 7) d (by omega)
  simp only [read64, readLE, g0, g1, g2, g3, g4, g5, g6, g7]

theorem addi0_env (v : BitVec 64) : v + sign_extend (m := 64) (0x000#12) = v := by
  rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide,
    BitVec.add_zero]

end Vsa.Sim
