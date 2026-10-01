import Vsa.Sim.Muldi3Sites
import Vsa.Sim.ObsBasics
import Vsa.Triple

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (__muldi3Loaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim


abbrev NotWrittenM (R : Register) : Prop :=
  (Register.x10 == R) = false ∧ (Register.x11 == R) = false ∧
  (Register.x12 == R) = false ∧ (Register.x13 == R) = false ∧
  (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
  (Register.minstret == R) = false ∧ (Register.minstret_increment == R) = false ∧
  (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
  (Register.mip == R) = false

theorem NotWrittenM.x10 {R : Register} (h : NotWrittenM R) : (Register.x10 == R) = false := h.1
theorem NotWrittenM.x11 {R : Register} (h : NotWrittenM R) : (Register.x11 == R) = false := h.2.1
theorem NotWrittenM.x12 {R : Register} (h : NotWrittenM R) : (Register.x12 == R) = false := h.2.2.1
theorem NotWrittenM.x13 {R : Register} (h : NotWrittenM R) : (Register.x13 == R) = false := h.2.2.2.1

theorem frame_alu_m {σ' σ : MState} {pc vm : BitVec 64} {rd : Register} {v : RegisterType rd}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm rd v)) (R : Register)
    (hrd : (rd == R) = false) (hR : NotWrittenM R) :
    σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_alu σ pc vm rd v R hmi hpc hrd hnpc hmii

theorem frame_btaken_m {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 13}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_taken σ pc vm imm)) (R : Register)
    (hR : NotWrittenM R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_branch_taken σ pc vm imm R hmi hpc hnpc hmii

theorem frame_bnottaken_m {σ' σ : MState} {pc vm : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm)) (R : Register)
    (hR : NotWrittenM R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_branch_nottaken σ pc vm R hmi hpc hnpc hmii

theorem frame_jr_m {σ' σ : MState} {pc vm tgt : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vm tgt)) (R : Register)
    (hR : NotWrittenM R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_jump_x0 σ pc vm tgt R hmi hpc hnpc hmii

structure St (g : (R : Register) → Option (RegisterType R))
    (pc a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (c : Config) : Prop where
  good : GoodState c.σ
  loaded : __muldi3Loaded c.σ.mem
  mem : c.σ.mem = m0
  sailOut : c.σ.sailOutput = o
  pc : c.σ.regs.get? Register.PC = some pc
  a0 : c.σ.regs.get? Register.x10 = some a0
  a1 : c.σ.regs.get? Register.x11 = some a1
  a2 : c.σ.regs.get? Register.x12 = some a2
  a3 : c.σ.regs.get? Register.x13 = some a3
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  hframe : ∀ R : Register, NotWrittenM R → c.σ.regs.get? R = g R


private theorem addi0 (v : BitVec 64) : v + sign_extend (m := 64) (0x000#12) = v := by
  rw [sext_zero]; exact BitVec.add_zero v

private theorem andi1 (v : BitVec 64) : v &&& sign_extend (m := 64) (0x001#12) = v &&& 1#64 := by
  rw [sext_one]

theorem tr_40_44 (g : (R : Register) → Option (RegisterType R))
    (x y r a2old a3old : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (St g (0x80004640#64) x y a2old a3old r m0 o) (St g (0x80004644#64) x y x a3old r m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80004640 c.σ c.tick c.steps (0x80004640#64) vmi x hSt.good hSt.pc hmi hSt.a0 hSt.loaded rfl hSt.tick
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut,
    obs_alu_pc hobs,
    obs_alu_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_alu_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    ?_,
    obs_alu_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3,
    obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_alu_minstret hobs, hi',
    fun R hR => (frame_alu_m hobs R hR.x12 hR).trans (hSt.hframe R hR)⟩

  have hrd := obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  rwa [addi0 x] at hrd

theorem tr_44_48 (g : (R : Register) → Option (RegisterType R))
    (x y r a2 a3old : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (St g (0x80004644#64) x y a2 a3old r m0 o) (St g (0x80004648#64) (0#64) y a2 a3old r m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80004644 c.σ c.tick c.steps (0x80004644#64) vmi hSt.good hSt.pc hmi hSt.loaded rfl hSt.tick
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut,
    obs_alu_pc hobs, ?_,
    obs_alu_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    obs_alu_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2,
    obs_alu_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3,
    obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_alu_minstret hobs, hi',
    fun R hR => (frame_alu_m hobs R hR.x10 hR).trans (hSt.hframe R hR)⟩
  have hrd := obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  rwa [addi0 (0#64)] at hrd

theorem tr_48_4c (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a2 a3old : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (St g (0x80004648#64) a0 y a2 a3old r m0 o) (St g (0x8000464c#64) a0 y a2 (y &&& 1#64) r m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80004648 c.σ c.tick c.steps (0x80004648#64) vmi y hSt.good hSt.pc hmi hSt.a1 hSt.loaded rfl hSt.tick
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut,
    obs_alu_pc hobs,
    obs_alu_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_alu_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    obs_alu_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2,
    ?_,
    obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_alu_minstret hobs, hi',
    fun R hR => (frame_alu_m hobs R hR.x13 hR).trans (hSt.hframe R hR)⟩
  have hrd := obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  rwa [andi1 y] at hrd

theorem tr_50_54 (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a2 a3 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (St g (0x80004650#64) a0 y a2 a3 r m0 o) (St g (0x80004654#64) (a0 + a2) y a2 a3 r m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80004650 c.σ c.tick c.steps (0x80004650#64) vmi a0 a2 hSt.good hSt.pc hmi hSt.a0 hSt.a2 hSt.loaded rfl hSt.tick
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut,
    obs_alu_pc hobs,
    obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide),
    obs_alu_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    obs_alu_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2,
    obs_alu_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3,
    obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_alu_minstret hobs, hi',
    fun R hR => (frame_alu_m hobs R hR.x10 hR).trans (hSt.hframe R hR)⟩

theorem tr_54_58 (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a1 a2 a3 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (St g (0x80004654#64) a0 a1 a2 a3 r m0 o) (St g (0x80004658#64) a0 (a1 >>> (1:Nat)) a2 a3 r m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80004654 c.σ c.tick c.steps (0x80004654#64) vmi a1 hSt.good hSt.pc hmi hSt.a1 hSt.loaded rfl hSt.tick
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut,
    obs_alu_pc hobs,
    obs_alu_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    ?_,
    obs_alu_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2,
    obs_alu_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3,
    obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_alu_minstret hobs, hi',
    fun R hR => (frame_alu_m hobs R hR.x11 hR).trans (hSt.hframe R hR)⟩
  have hrd := obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  rwa [shr_shamt a1] at hrd

theorem tr_58_5c (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a1 a2 a3 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (St g (0x80004658#64) a0 a1 a2 a3 r m0 o) (St g (0x8000465c#64) a0 a1 (a2 <<< (1:Nat)) a3 r m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80004658 c.σ c.tick c.steps (0x80004658#64) vmi a2 hSt.good hSt.pc hmi hSt.a2 hSt.loaded rfl hSt.tick
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut,
    obs_alu_pc hobs,
    obs_alu_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_alu_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    ?_,
    obs_alu_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3,
    obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_alu_minstret hobs, hi',
    fun R hR => (frame_alu_m hobs R hR.x12 hR).trans (hSt.hframe R hR)⟩
  have hrd := obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  rwa [shl_shamt a2] at hrd


theorem tr_4c_54 (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a2 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hodd : ((y &&& 1#64) == (0#64)) = true) :
    Triple (St g (0x8000464c#64) a0 y a2 (y &&& 1#64) r m0 o) (St g (0x80004654#64) a0 y a2 (y &&& 1#64) r m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_8000464c_taken c.σ c.tick c.steps (0x8000464c#64) vmi (y &&& 1#64)
      hSt.good hSt.pc hmi hSt.a3 hSt.loaded rfl hodd hSt.tick
  have hpceq : (0x8000464c#64 : BitVec 64) + sign_extend (m := 64) (0x0008#13) = (0x80004654#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut, ?_,
    obs_btaken_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_btaken_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    obs_btaken_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2,
    obs_btaken_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3,
    obs_btaken_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_btaken_minstret hobs, hi',
    fun R hR => (frame_btaken_m hobs R hR).trans (hSt.hframe R hR)⟩
  rw [obs_btaken_pc hobs, hpceq]

theorem tr_4c_50 (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a2 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hodd : ((y &&& 1#64) == (0#64)) = false) :
    Triple (St g (0x8000464c#64) a0 y a2 (y &&& 1#64) r m0 o) (St g (0x80004650#64) a0 y a2 (y &&& 1#64) r m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_8000464c_nottaken c.σ c.tick c.steps (0x8000464c#64) vmi (y &&& 1#64)
      hSt.good hSt.pc hmi hSt.a3 hSt.loaded rfl hodd hSt.tick
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut,
    obs_bnottaken_pc hobs,
    obs_bnottaken_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_bnottaken_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    obs_bnottaken_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2,
    obs_bnottaken_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3,
    obs_bnottaken_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_bnottaken_minstret hobs, hi',
    fun R hR => (frame_bnottaken_m hobs R hR).trans (hSt.hframe R hR)⟩

theorem tr_5c_48 (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a2 a3 a1 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hne : (a1 != (0#64)) = true) :
    Triple (St g (0x8000465c#64) a0 a1 a2 a3 r m0 o) (St g (0x80004648#64) a0 a1 a2 a3 r m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_8000465c_taken c.σ c.tick c.steps (0x8000465c#64) vmi a1
      hSt.good hSt.pc hmi hSt.a1 hSt.loaded rfl hne hSt.tick
  have hpceq : (0x8000465c#64 : BitVec 64) + sign_extend (m := 64) (0x1fec#13) = (0x80004648#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut, ?_,
    obs_btaken_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_btaken_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    obs_btaken_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2,
    obs_btaken_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3,
    obs_btaken_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_btaken_minstret hobs, hi',
    fun R hR => (frame_btaken_m hobs R hR).trans (hSt.hframe R hR)⟩
  rw [obs_btaken_pc hobs, hpceq]

theorem tr_5c_60 (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a2 a3 a1 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hne : (a1 != (0#64)) = false) :
    Triple (St g (0x8000465c#64) a0 a1 a2 a3 r m0 o) (St g (0x80004660#64) a0 a1 a2 a3 r m0 o) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_8000465c_nottaken c.σ c.tick c.steps (0x8000465c#64) vmi a1
      hSt.good hSt.pc hmi hSt.a1 hSt.loaded rfl hne hSt.tick
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.loaded, by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut,
    obs_bnottaken_pc hobs,
    obs_bnottaken_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_bnottaken_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    obs_bnottaken_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2,
    obs_bnottaken_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3,
    obs_bnottaken_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    obs_bnottaken_minstret hobs, hi',
    fun R hR => (frame_bnottaken_m hobs R hR).trans (hSt.hframe R hR)⟩


theorem tr_60_ret (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a1 a2 a3 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (halign : r.toNat % 4 = 0) :
    Triple (St g (0x80004660#64) a0 a1 a2 a3 r m0 o)
           (fun c => GoodState c.σ ∧ c.σ.mem = m0 ∧ c.σ.sailOutput = o ∧
             c.σ.regs.get? Register.PC = some r ∧
             c.σ.regs.get? Register.x10 = some a0 ∧ c.σ.regs.get? Register.x11 = some a1 ∧
             c.σ.regs.get? Register.x12 = some a2 ∧ c.σ.regs.get? Register.x1 = some r ∧
             c.tick < 2 ∧ (∀ R : Register, NotWrittenM R → c.σ.regs.get? R = g R)) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  have htgt : (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
    rw [ret_tgt r halign]; exact halign
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80004660 c.σ c.tick c.steps (0x80004660#64) vmi r
      hSt.good hSt.pc hmi hSt.ra hSt.loaded rfl htgt hSt.tick
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hSt.mem,
    by rw [hobs.out]; exact hSt.sailOut, ?_,
    obs_jr_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
    obs_jr_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
    obs_jr_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2,
    obs_jr_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
    hi',
    fun R hR => (frame_jr_m hobs R hR).trans (hSt.hframe R hR)⟩
  rw [obs_jr_pc hobs, ret_tgt r halign]

def AtHead (g : (R : Register) → Option (RegisterType R)) (x y r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  ∃ a0 a1 a2 a3, St g (0x80004648#64) a0 a1 a2 a3 r m0 o c ∧ a0 + a2 * a1 = x * y

def AtDone (g : (R : Register) → Option (RegisterType R)) (x y r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  ∃ a1 a2 a3, St g (0x80004660#64) (x * y) a1 a2 a3 r m0 o c

def LoopI (g : (R : Register) → Option (RegisterType R)) (x y r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  AtHead g x y r m0 o c ∨ AtDone g x y r m0 o c

def LoopB (g : (R : Register) → Option (RegisterType R)) (x y r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  ∃ a0 a1 a2 a3, St g (0x80004648#64) a0 a1 a2 a3 r m0 o c ∧ a0 + a2 * a1 = x * y ∧ a1 ≠ 0#64

def LoopMu (c : Config) : Nat :=
  ((c.σ.regs.get? Register.x11).getD (0#64)).toNat

theorem and1_cases (a1 : BitVec 64) : a1 &&& 1#64 = 0#64 ∨ a1 &&& 1#64 = 1#64 := by
  have hval : (a1 &&& 1#64).toNat = a1.toNat % 2 := by
    rw [BitVec.toNat_and]; have h1 : (1#64).toNat = 1 := by decide
    rw [h1, Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one a1.toNat with h0 | h1
  · left; apply BitVec.eq_of_toNat_eq; rw [hval, h0]; rfl
  · right; apply BitVec.eq_of_toNat_eq; rw [hval, h1]; rfl

theorem inv_even (a0 a1 a2 : BitVec 64) (hev : a1 &&& 1#64 = 0#64) :
    a0 + (a2 <<< (1:Nat)) * (a1 >>> (1:Nat)) = a0 + a2 * a1 := by
  rw [invmul_bv a2 a1, hev, BitVec.zero_mul, BitVec.add_zero]

theorem inv_odd (a0 a1 a2 : BitVec 64) (hod : a1 &&& 1#64 = 1#64) :
    (a0 + a2) + (a2 <<< (1:Nat)) * (a1 >>> (1:Nat)) = a0 + a2 * a1 := by
  rw [invmul_bv a2 a1, hod, BitVec.one_mul, BitVec.add_assoc, BitVec.add_comm a2 _,
    ← BitVec.add_assoc]

theorem iter_48_5c (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a1 a2 a3old : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hinv : a0 + a2 * a1 = x * y) :
    Triple (St g (0x80004648#64) a0 a1 a2 a3old r m0 o)
           (fun c => ∃ a0', St g (0x8000465c#64) a0' (a1 >>> (1:Nat)) (a2 <<< (1:Nat)) (a1 &&& 1#64) r m0 o c
             ∧ a0' + (a2 <<< (1:Nat)) * (a1 >>> (1:Nat)) = x * y) := by

  have h1 : Triple (St g (0x80004648#64) a0 a1 a2 a3old r m0 o)
      (St g (0x8000464c#64) a0 a1 a2 (a1 &&& 1#64) r m0 o) := tr_48_4c g x a1 r a0 a2 a3old m0 o
  rcases and1_cases a1 with hev | hod
  ·
    have hbeq : ((a1 &&& 1#64) == (0#64)) = true := by rw [hev]; rfl
    have h2 := tr_4c_54 g x a1 r a0 a2 m0 o hbeq
    have h3 := tr_54_58 g x y r a0 a1 a2 (a1 &&& 1#64) m0 o
    have h4 := tr_58_5c g x y r a0 (a1 >>> (1:Nat)) a2 (a1 &&& 1#64) m0 o
    have hchain : Triple (St g (0x80004648#64) a0 a1 a2 a3old r m0 o)
        (St g (0x8000465c#64) a0 (a1 >>> (1:Nat)) (a2 <<< (1:Nat)) (a1 &&& 1#64) r m0 o) :=
      (h1.seq h2).seq (h3.seq h4)
    exact hchain.conseq (fun _ h => h) (fun c hc =>
      ⟨a0, hc, by rw [inv_even a0 a1 a2 hev]; exact hinv⟩)
  ·
    have hbne : ((a1 &&& 1#64) == (0#64)) = false := by rw [hod]; rfl
    have h2 := tr_4c_50 g x a1 r a0 a2 m0 o hbne
    have h2' := tr_50_54 g x a1 r a0 a2 (a1 &&& 1#64) m0 o
    have h3 := tr_54_58 g x a1 r (a0 + a2) a1 a2 (a1 &&& 1#64) m0 o
    have h4 := tr_58_5c g x a1 r (a0 + a2) (a1 >>> (1:Nat)) a2 (a1 &&& 1#64) m0 o
    have hchain : Triple (St g (0x80004648#64) a0 a1 a2 a3old r m0 o)
        (St g (0x8000465c#64) (a0 + a2) (a1 >>> (1:Nat)) (a2 <<< (1:Nat)) (a1 &&& 1#64) r m0 o) :=
      ((h1.seq h2).seq h2').seq (h3.seq h4)
    exact hchain.conseq (fun _ h => h) (fun c hc =>
      ⟨a0 + a2, hc, by rw [inv_odd a0 a1 a2 hod]; exact hinv⟩)

theorem loop_body (g : (R : Register) → Option (RegisterType R)) (x y r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (n : Nat) :
    Triple (fun c => LoopI g x y r m0 o c ∧ LoopB g x y r m0 o c ∧ LoopMu c = n)
           (fun c => LoopI g x y r m0 o c ∧ LoopMu c < n) := by
  intro c hc
  obtain ⟨_, ⟨a0, a1, a2, a3, hSt, hinv, hne⟩, hmu⟩ := hc

  have hmu_eq : LoopMu c = a1.toNat := by
    simp only [LoopMu, hSt.a1, Option.getD_some]
  rw [hmu_eq] at hmu

  obtain ⟨c1, hs1, a0', h5c, hinv'⟩ := iter_48_5c g x y r a0 a1 a2 a3 m0 o hinv c hSt
  by_cases hnew : (a1 >>> (1:Nat)) = 0#64
  ·
    have hbne : ((a1 >>> (1:Nat)) != (0#64)) = false := by rw [hnew]; rfl
    obtain ⟨c2, hs2, hSt2⟩ := tr_5c_60 g x y r a0' (a2 <<< (1:Nat)) (a1 &&& 1#64) (a1 >>> (1:Nat)) m0 o hbne c1 h5c
    have ha0' : a0' = x * y := by
      have := hinv'
      rw [hnew, BitVec.mul_zero, BitVec.add_zero] at this
      exact this
    refine ⟨c2, hs1.trans hs2, Or.inr ⟨_, _, _, ha0' ▸ hSt2⟩, ?_⟩

    have hmc2 : LoopMu c2 = (a1 >>> (1:Nat)).toNat := by simp only [LoopMu, hSt2.a1, Option.getD_some]
    have hnpos : 0 < n := by
      rw [← hmu]
      have : 0 < a1.toNat := by
        rcases Nat.eq_zero_or_pos a1.toNat with h0 | h0
        · exact absurd (by apply BitVec.eq_of_toNat_eq; simpa using h0) hne
        · exact h0
      exact this
    rw [hmc2, hnew]
    show (0#64).toNat < n
    have h0 : (0#64 : BitVec 64).toNat = 0 := by decide
    rw [h0]; exact hnpos
  ·
    have hbne : ((a1 >>> (1:Nat)) != (0#64)) = true := by
      rw [bne_iff_ne]; exact hnew
    obtain ⟨c2, hs2, hSt2⟩ := tr_5c_48 g x y r a0' (a2 <<< (1:Nat)) (a1 &&& 1#64) (a1 >>> (1:Nat)) m0 o hbne c1 h5c
    refine ⟨c2, hs1.trans hs2, Or.inl ⟨a0', a1 >>> (1:Nat), a2 <<< (1:Nat), a1 &&& 1#64, hSt2, hinv'⟩, ?_⟩
    have hmu2 : LoopMu c2 = (a1 >>> (1:Nat)).toNat := by simp only [LoopMu, hSt2.a1, Option.getD_some]
    rw [hmu2, ← hmu]
    exact shr_lt a1 hne

theorem loop_to_done (g : (R : Register) → Option (RegisterType R)) (x y r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (LoopI g x y r m0 o) (AtDone g x y r m0 o) := by
  have hloop := Triple.loop (I := LoopI g x y r m0 o) (B := LoopB g x y r m0 o) LoopMu (loop_body g x y r m0 o)
  refine hloop.seq ?_
  intro c hc
  obtain ⟨hI, hnB⟩ := hc
  rcases hI with hHead | hDone
  ·
    obtain ⟨a0, a1, a2, a3, hSt, hinv⟩ := hHead
    have ha1 : a1 = 0#64 := by
      by_cases hne : a1 = 0#64
      · exact hne
      · exact absurd ⟨a0, a1, a2, a3, hSt, hinv, hne⟩ hnB

    obtain ⟨c1, hs1, a0', h5c, hinv'⟩ := iter_48_5c g x y r a0 a1 a2 a3 m0 o hinv c hSt
    have hnew : (a1 >>> (1:Nat)) = 0#64 := by rw [ha1]; rfl
    have hbne : ((a1 >>> (1:Nat)) != (0#64)) = false := by rw [hnew]; rfl
    obtain ⟨c2, hs2, hSt2⟩ := tr_5c_60 g x y r a0' (a2 <<< (1:Nat)) (a1 &&& 1#64) (a1 >>> (1:Nat)) m0 o hbne c1 h5c
    have ha0' : a0' = x * y := by
      have := hinv'; rw [hnew, BitVec.mul_zero, BitVec.add_zero] at this; exact this
    exact ⟨c2, hs1.trans hs2, _, _, _, ha0' ▸ hSt2⟩
  · exact ⟨c, .refl c, hDone⟩

def muldi3_pre (g : (R : Register) → Option (RegisterType R)) (x y r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  (∃ a2old a3old, St g (0x80004640#64) x y a2old a3old r m0 o c) ∧ r.toNat % 4 = 0

def muldi3_post (g : (R : Register) → Option (RegisterType R)) (x y r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.mem = m0 ∧ c.σ.sailOutput = o ∧ c.σ.regs.get? Register.PC = some r ∧
  c.σ.regs.get? Register.x10 = some (x * y) ∧ c.σ.regs.get? Register.x1 = some r ∧
  c.tick < 2 ∧ (∀ R : Register, NotWrittenM R → c.σ.regs.get? R = g R)

theorem muldi3_spec (g : (R : Register) → Option (RegisterType R)) (x y r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (muldi3_pre g x y r m0 o) (muldi3_post g x y r m0 o) := by

  have hpre : Triple (muldi3_pre g x y r m0 o) (fun c => LoopI g x y r m0 o c ∧ r.toNat % 4 = 0) := by
    intro c hc
    obtain ⟨⟨a2old, a3old, hEntry⟩, halign⟩ := hc

    obtain ⟨c1, hs1, hSt1⟩ := tr_40_44 g x y r a2old a3old m0 o c hEntry

    obtain ⟨c2, hs2, hSt2⟩ := tr_44_48 g x y r x a3old m0 o c1 hSt1
    refine ⟨c2, hs1.trans hs2, Or.inl ⟨0#64, y, x, a3old, hSt2, ?_⟩, halign⟩

    rw [BitVec.zero_add]

  have hbody : Triple (fun c => LoopI g x y r m0 o c ∧ r.toNat % 4 = 0)
      (fun c => AtDone g x y r m0 o c ∧ r.toNat % 4 = 0) := by
    intro c hc
    obtain ⟨hI, halign⟩ := hc
    obtain ⟨c', hs, hDone⟩ := loop_to_done g x y r m0 o c hI
    exact ⟨c', hs, hDone, halign⟩

  have hret : Triple (fun c => AtDone g x y r m0 o c ∧ r.toNat % 4 = 0) (muldi3_post g x y r m0 o) := by
    intro c hc
    obtain ⟨⟨a1, a2, a3, hSt⟩, halign⟩ := hc
    obtain ⟨c', hs, hG, hmem, hout, hpc, ha0, ha1, ha2, hra, htick, hframe⟩ := tr_60_ret g x y r (x*y) a1 a2 a3 m0 o halign c hSt
    exact ⟨c', hs, hG, hmem, hout, hpc, ha0, hra, htick, hframe⟩
  exact (hpre.seq hbody).seq hret

end Vsa.Sim
