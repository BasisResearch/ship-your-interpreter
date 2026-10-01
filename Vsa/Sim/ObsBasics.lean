import Vsa.Sim.StepObs
import Vsa.Sim.StepAlu
import Vsa.Sim.StepBranch
import Vsa.Sim.StepJump

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)

namespace Vsa.Sim

private theorem key_nat (A d r : Nat) : A * (2 * d + r) = A * 2 * d + r * A := by
  rw [Nat.mul_add, Nat.mul_comm r A, ← Nat.mul_assoc]

private theorem mml (a b m : Nat) : (a % m) * b % m = a * b % m := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

private theorem amod (a b m : Nat) : (a % m + b % m) % m = (a + b) % m := by
  rw [← Nat.add_mod]

private theorem invmul_nat (A a1n : Nat) :
    A * a1n % 2^64 = (A * 2 % 2^64 * (a1n / 2) % 2^64 + a1n % 2 * A % 2^64) % 2^64 := by
  have key : A * 2 * (a1n / 2) + a1n % 2 * A = A * a1n := by
    rw [← key_nat A (a1n / 2) (a1n % 2), Nat.div_add_mod a1n 2]
  rw [mml (A*2) (a1n/2) (2^64), amod, key]

theorem invmul_bv (a2 a1 : BitVec 64) :
    a2 * a1 = (a2 <<< (1:Nat)) * (a1 >>> (1:Nat)) + (a1 &&& 1#64) * a2 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_shiftLeft,
    BitVec.toNat_ushiftRight, BitVec.toNat_and]
  have hand : (a1.toNat &&& (1#64).toNat) = a1.toNat % 2 := by
    have : (1#64).toNat = 1 := by decide
    rw [this, Nat.and_one_is_mod]
  rw [hand, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have hpow : (2:Nat)^1 = 2 := by decide
  rw [hpow]
  exact invmul_nat a2.toNat a1.toNat

theorem shr_lt (a1 : BitVec 64) (h : a1 ≠ 0#64) : (a1 >>> (1:Nat)).toNat < a1.toNat := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hpos : 0 < a1.toNat := by
    rcases Nat.eq_zero_or_pos a1.toNat with h0 | h0
    · exact absurd (by apply BitVec.eq_of_toNat_eq; simpa using h0) h
    · exact h0
  have hpow : (2:Nat)^1 = 2 := by decide
  rw [hpow]; omega

theorem sext_one : (sign_extend (0x001#12) : BitVec 64) = (1#64 : BitVec 64) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem sext_zero : (sign_extend (0x000#12) : BitVec 64) = (0#64 : BitVec 64) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem shamt_one : Sail.BitVec.extractLsb (0x01#6) 5 0 = (1#6 : BitVec 6) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem shr_shamt (v : BitVec 64) : shift_bits_right v (Sail.BitVec.extractLsb (0x01#6) 5 0) = v >>> (1:Nat) := by
  show v >>> (Sail.BitVec.extractLsb (0x01#6) 5 0) = _
  rw [shamt_one]; rfl

theorem shl_shamt (v : BitVec 64) : shift_bits_left v (Sail.BitVec.extractLsb (0x01#6) 5 0) = v <<< (1:Nat) := by
  show v <<< (Sail.BitVec.extractLsb (0x01#6) 5 0) = _
  rw [shamt_one]; rfl

theorem readback (σ' spost : MState) (h : ReadsLikePost σ' spost) (R : Register) {w : RegisterType R}
    (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false)
    (hw : spost.regs.get? R = some w) : σ'.regs.get? R = some w := by
  rw [h.1 R hmc hmt hmi]; exact hw

theorem post_alu_pc (σ : MState) (pc vminstret : BitVec 64) (rd_reg : Register)
    (v : RegisterType rd_reg) :
    (sigmaPost_alu σ pc vminstret rd_reg v).regs.get? Register.PC = some (BitVec.addInt pc 4) := by
  show ((((sigma3_alu σ pc rd_reg v).regs.insert Register.PC (BitVec.addInt pc 4)).insert
    Register.minstret (BitVec.addInt vminstret 1))).get? Register.PC = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.minstret == Register.PC) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert_self]

theorem post_alu_rd (σ : MState) (pc vminstret : BitVec 64) (rd_reg : Register)
    (v : RegisterType rd_reg)
    (hrd_ms : (Register.minstret == rd_reg) = false) (hrd_pc : (Register.PC == rd_reg) = false) :
    (sigmaPost_alu σ pc vminstret rd_reg v).regs.get? rd_reg = some v := by
  show ((((sigma3_alu σ pc rd_reg v).regs.insert Register.PC (BitVec.addInt pc 4)).insert
    Register.minstret (BitVec.addInt vminstret 1))).get? rd_reg = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hrd_ms, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hrd_pc, dif_neg, reduceCtorEq, not_false_eq_true]
  show ((afterNextPC (afterPrelude σ) pc).regs.insert rd_reg v).get? rd_reg = _
  rw [Std.ExtDHashMap.get?_insert_self]

theorem post_alu_other (σ : MState) (pc vminstret : BitVec 64) (rd_reg : Register)
    (v : RegisterType rd_reg) (R : Register)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h3 : (rd_reg == R) = false) (h4 : (Register.nextPC == R) = false)
    (h5 : (Register.minstret_increment == R) = false) :
    (sigmaPost_alu σ pc vminstret rd_reg v).regs.get? R = σ.regs.get? R :=
  get?_sigmaPost_alu σ pc vminstret rd_reg v R h1 h2 h3 h4 h5

theorem post_branch_taken_pc (σ : MState) (pc vminstret : BitVec 64) (imm : BitVec 13) :
    (sigmaPost_branch_taken σ pc vminstret imm).regs.get? Register.PC
      = some (pc + sign_extend (m := 64) imm) := by
  show ((((sigma3_branch_taken σ pc imm).regs.insert Register.PC (pc + sign_extend (m := 64) imm)).insert
    Register.minstret (BitVec.addInt vminstret 1))).get? Register.PC = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.minstret == Register.PC) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert_self]

theorem post_branch_taken_other (σ : MState) (pc vminstret : BitVec 64) (imm : BitVec 13) (R : Register)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h4 : (Register.nextPC == R) = false) (h5 : (Register.minstret_increment == R) = false) :
    (sigmaPost_branch_taken σ pc vminstret imm).regs.get? R = σ.regs.get? R :=
  get?_sigmaPost_branch_taken σ pc vminstret imm R h1 h2 h4 h5

theorem post_branch_nottaken_pc (σ : MState) (pc vminstret : BitVec 64) :
    (sigmaPost_branch_nottaken σ pc vminstret).regs.get? Register.PC = some (BitVec.addInt pc 4) := by
  show ((((sigma3_branch_nottaken σ pc).regs.insert Register.PC (BitVec.addInt pc 4)).insert
    Register.minstret (BitVec.addInt vminstret 1))).get? Register.PC = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.minstret == Register.PC) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert_self]

theorem post_branch_nottaken_other (σ : MState) (pc vminstret : BitVec 64) (R : Register)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h4 : (Register.nextPC == R) = false) (h5 : (Register.minstret_increment == R) = false) :
    (sigmaPost_branch_nottaken σ pc vminstret).regs.get? R = σ.regs.get? R :=
  get?_sigmaPost_branch_nottaken σ pc vminstret R h1 h2 h4 h5

theorem post_jump_x0_pc (σ : MState) (pc vminstret tgt : BitVec 64) :
    (sigmaPost_jump_x0 σ pc vminstret tgt).regs.get? Register.PC = some tgt := by
  show ((((sigma3_jump_x0 σ pc tgt).regs.insert Register.PC tgt).insert
    Register.minstret (BitVec.addInt vminstret 1))).get? Register.PC = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.minstret == Register.PC) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert_self]

theorem post_jump_x0_other (σ : MState) (pc vminstret tgt : BitVec 64) (R : Register)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h4 : (Register.nextPC == R) = false) (h5 : (Register.minstret_increment == R) = false) :
    (sigmaPost_jump_x0 σ pc vminstret tgt).regs.get? R = σ.regs.get? R :=
  get?_sigmaPost_jump_x0 σ pc vminstret tgt R h1 h2 h4 h5
theorem obs_alu_pc {σ' σ : MState} {pc vm : BitVec 64} {rd : Register} {v : RegisterType rd}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm rd v)) :
    σ'.regs.get? Register.PC = some (BitVec.addInt pc 4) :=
  readback σ' _ hobs Register.PC (by decide) (by decide) (by decide) (post_alu_pc σ pc vm rd v)

theorem obs_alu_rd {σ' σ : MState} {pc vm : BitVec 64} {rd : Register} {v : RegisterType rd}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm rd v))
    (hmc : (Register.mcycle == rd) = false) (hmt : (Register.mtime == rd) = false)
    (hmi : (Register.mip == rd) = false)
    (hrd_ms : (Register.minstret == rd) = false) (hrd_pc : (Register.PC == rd) = false) :
    σ'.regs.get? rd = some v :=
  readback σ' _ hobs rd hmc hmt hmi (post_alu_rd σ pc vm rd v hrd_ms hrd_pc)

theorem obs_alu_other {σ' σ : MState} {pc vm : BitVec 64} {rd : Register} {v : RegisterType rd}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm rd v)) (R : Register) {w : RegisterType R}
    (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h3 : (rd == R) = false) (h4 : (Register.nextPC == R) = false)
    (h5 : (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w :=
  readback σ' _ hobs R hmc hmt hmi ((post_alu_other σ pc vm rd v R h1 h2 h3 h4 h5).trans hσ)

theorem obs_alu_minstret {σ' σ : MState} {pc vm : BitVec 64} {rd : Register} {v : RegisterType rd}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm rd v)) :
    ∃ w, σ'.regs.get? Register.minstret = some w := by
  refine ⟨BitVec.addInt vm 1, readback σ' _ hobs Register.minstret (w := BitVec.addInt vm 1)
    (by decide) (by decide) (by decide) ?_⟩
  show ((((sigma3_alu σ pc rd v).regs.insert Register.PC (BitVec.addInt pc 4)).insert
    Register.minstret (BitVec.addInt vm 1))).get? Register.minstret = _
  rw [Std.ExtDHashMap.get?_insert_self]
theorem obs_btaken_other {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 13}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_taken σ pc vm imm)) (R : Register) {w : RegisterType R}
    (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h4 : (Register.nextPC == R) = false) (h5 : (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w :=
  readback σ' _ hobs R hmc hmt hmi ((post_branch_taken_other σ pc vm imm R h1 h2 h4 h5).trans hσ)

theorem obs_btaken_pc {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 13}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_taken σ pc vm imm)) :
    σ'.regs.get? Register.PC = some (pc + sign_extend (m := 64) imm) :=
  readback σ' _ hobs Register.PC (by decide) (by decide) (by decide) (post_branch_taken_pc σ pc vm imm)

theorem obs_btaken_minstret {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 13}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_taken σ pc vm imm)) :
    ∃ w, σ'.regs.get? Register.minstret = some w := by
  refine ⟨BitVec.addInt vm 1, readback σ' _ hobs Register.minstret (w := BitVec.addInt vm 1)
    (by decide) (by decide) (by decide) ?_⟩
  show ((((sigma3_branch_taken σ pc imm).regs.insert Register.PC (pc + sign_extend (m := 64) imm)).insert
    Register.minstret (BitVec.addInt vm 1))).get? Register.minstret = _
  rw [Std.ExtDHashMap.get?_insert_self]

theorem obs_bnottaken_other {σ' σ : MState} {pc vm : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm)) (R : Register) {w : RegisterType R}
    (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h4 : (Register.nextPC == R) = false) (h5 : (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w :=
  readback σ' _ hobs R hmc hmt hmi ((post_branch_nottaken_other σ pc vm R h1 h2 h4 h5).trans hσ)

theorem obs_bnottaken_pc {σ' σ : MState} {pc vm : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm)) :
    σ'.regs.get? Register.PC = some (BitVec.addInt pc 4) :=
  readback σ' _ hobs Register.PC (by decide) (by decide) (by decide) (post_branch_nottaken_pc σ pc vm)

theorem obs_bnottaken_minstret {σ' σ : MState} {pc vm : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm)) :
    ∃ w, σ'.regs.get? Register.minstret = some w := by
  refine ⟨BitVec.addInt vm 1, readback σ' _ hobs Register.minstret (w := BitVec.addInt vm 1)
    (by decide) (by decide) (by decide) ?_⟩
  show ((((sigma3_branch_nottaken σ pc).regs.insert Register.PC (BitVec.addInt pc 4)).insert
    Register.minstret (BitVec.addInt vm 1))).get? Register.minstret = _
  rw [Std.ExtDHashMap.get?_insert_self]
theorem obs_jr_other {σ' σ : MState} {pc vm tgt : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vm tgt)) (R : Register) {w : RegisterType R}
    (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h4 : (Register.nextPC == R) = false) (h5 : (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w :=
  readback σ' _ hobs R hmc hmt hmi ((post_jump_x0_other σ pc vm tgt R h1 h2 h4 h5).trans hσ)

theorem obs_jr_pc {σ' σ : MState} {pc vm tgt : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vm tgt)) :
    σ'.regs.get? Register.PC = some tgt :=
  readback σ' _ hobs Register.PC (by decide) (by decide) (by decide) (post_jump_x0_pc σ pc vm tgt)

theorem obs_jr_minstret {σ' σ : MState} {pc vm tgt : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vm tgt)) :
    ∃ w, σ'.regs.get? Register.minstret = some w := by
  refine ⟨BitVec.addInt vm 1, readback σ' _ hobs Register.minstret (w := BitVec.addInt vm 1)
    (by decide) (by decide) (by decide) ?_⟩
  show ((((sigma3_jump_x0 σ pc tgt).regs.insert Register.PC tgt).insert
    Register.minstret (BitVec.addInt vm 1))).get? Register.minstret = _
  rw [Std.ExtDHashMap.get?_insert_self]

theorem and_clear_bit0 (x : Nat) (hlt : x < 2^64) (hev : x % 2 = 0) :
    x &&& (2^64 - 2) = x := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  have hmaskeq : (2^64 - 2) = 2 * (2^63 - 1) := by decide
  rw [hmaskeq]
  match i with
  | 0 =>
    have hx0 : x.testBit 0 = false := by rw [Nat.testBit_zero, hev]; rfl
    rw [hx0, Bool.false_and]
  | j + 1 =>
    rw [Nat.testBit_succ (2 * (2^63-1)) j]
    have hdiv : (2 * (2^63 - 1)) / 2 = 2^63 - 1 := by omega
    rw [hdiv]
    by_cases hj : j < 63
    · rw [Nat.testBit_two_pow_sub_one]; simp only [hj, decide_true, Bool.and_true]
    · have hxf : x.testBit (j+1) = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by omega)))
      rw [hxf, Bool.false_and]

theorem ret_tgt (r : BitVec 64) (halign : r.toNat % 4 = 0) :
    Sail.BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1 = r := by
  rw [sext_zero, BitVec.add_zero]
  show Sail.BitVec.updateSubrange' r 0 1 (0#1) = r
  have hmask : (~~~(((BitVec.allOnes 1).zeroExtend 64) <<< 0) : BitVec 64) = 0xFFFFFFFFFFFFFFFE#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  have hy : (((0#1 : BitVec 1).zeroExtend 64) <<< 0 : BitVec 64) = 0#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  simp only [Sail.BitVec.updateSubrange', hmask, hy, BitVec.or_zero]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  have hmv : (0xFFFFFFFFFFFFFFFE#64 : BitVec 64).toNat = 2^64 - 2 := by decide
  rw [hmv, Nat.and_comm]
  exact and_clear_bit0 r.toNat r.isLt (by omega)

end Vsa.Sim
