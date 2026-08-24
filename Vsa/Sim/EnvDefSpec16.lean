import Vsa.Sim.EnvDefSpec15

/-! # `env_define` prologue: spill the incoming `s3` -/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (Config Step)
open Vsa.MemRepr
open Vsa.Sim.Code (Env_defineLoaded StrcmpLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- Site `0x80002a60`: spill `s3` while preserving the environment count read. -/
theorem env_define_spill_s3
    (env name pv r sp v18 v20 v21 v8 v9 v22 savedS3 vmi : BitVec 64)
    (pn hit count : Nat) (c : Config)
    (hRG : EnvDefRegions sp.toNat env.toNat pv.toNat pn hit count)
    (hG : GoodState c.σ) (hloaded : Env_defineLoaded c.σ.mem)
    (hstrloaded : StrcmpLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x80002a60#64 : BitVec 64))
    (hcarry : PrologueCarry c.σ sp env name pv r v18 v20 v21 v8 v9 v22)
    (hs3 : c.σ.regs.get? Register.x19 = some savedS3)
    (hmi : c.σ.regs.get? Register.minstret = some vmi)
    (hread : read32 c.σ.mem env.toNat = some count)
    (htick : c.tick < 2) :
    ∃ c' vmi', Step c c' ∧
      c'.σ.regs.get? Register.PC = some (0x80002a64#64 : BitVec 64) ∧
      PrologueCarry c'.σ sp env name pv r v18 v20 v21 v8 v9 v22 ∧
      c'.σ.regs.get? Register.x19 = some savedS3 ∧
      c'.σ.regs.get? Register.minstret = some vmi' ∧
      GoodState c'.σ ∧ Env_defineLoaded c'.σ.mem ∧ StrcmpLoaded c'.σ.mem ∧
      read32 c'.σ.mem env.toNat = some count ∧ c'.tick < 2 := by
  have hsp64 : (64 : Nat) ≤ sp.toNat := hRG.sp_ge
  have hspNat : (sp - 64#64).toNat = sp.toNat - 64 := sp_sub64_toNat sp hsp64
  have haddr : ((sp - 64#64) + sign_extend (m := 64) (0x018#12)).toNat =
      (sp - 64#64).toNat + 24 := by
    apply off_ed_18
    rw [hspNat]
    have := sp.isLt
    omega
  have hcodeDisjoint : (sp - 64#64).toNat + 24 + 8 ≤ 0x80002a5c ∨
      0x80002c10 ≤ (sp - 64#64).toNat + 24 := by
    rw [hspNat]
    have := hRG.frame_code_disjoint
    have := hRG.sp_ge
    omega
  have hstrcmpDisjoint : (sp - 64#64).toNat + 24 + 8 ≤ 0x80006ea0 ∨
      0x80006fcc ≤ (sp - 64#64).toNat + 24 := by
    rw [hspNat]
    have := hRG.frame_strcmp_disjoint
    have := hRG.sp_ge
    omega
  have hheaderDisjoint : env.toNat + 4 ≤ (sp - 64#64).toNat + 24 ∨
      (sp - 64#64).toNat + 24 + 8 ≤ env.toNat := by
    rw [hspNat]
    have := hRG.frame_header_disjoint
    have := hRG.sp_ge
    omega
  obtain ⟨σ', i', hstep, htick', hG', hmem', hobs⟩ :=
    site_80002a60_ed c.σ c.tick c.steps (0x80002a60#64) vmi
      (sp - 64#64) savedS3 hG hpc hmi hcarry.1 hs3 hloaded rfl
      (by rw [haddr, hspNat]; have := hRG.frame_lo; have := hRG.frame_win; omega)
      (by rw [haddr, hspNat]; have := hRG.frame_hi; omega)
      (by rw [haddr, hspNat]; have := hRG.frame_win; omega)
      (by rw [haddr, hspNat]; have := hRG.frame_align; omega)
      htick
  have hstep' : Step c ⟨σ', i', c.steps + 1⟩ := by cases c; exact hstep
  have hpc' := obs_store_pc hobs
  rw [show BitVec.addInt (0x80002a60#64 : BitVec 64) 4 =
    (0x80002a64#64 : BitVec 64) from by decide] at hpc'
  have hcarry' := prologueCarry_store hobs hcarry
  have hs3' := obs_store_other hobs Register.x19 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hs3
  obtain ⟨vmi', hmi'⟩ := obs_store_minstret hobs
  have hmem'' := normalize_env_define_store_mem hmem' haddr
  have hloaded' : Env_defineLoaded σ'.mem := by
    rw [hmem'']
    exact loaded_envdef_writeMap8 _ _ _ hcodeDisjoint hloaded
  have hstrloaded' : StrcmpLoaded σ'.mem := by
    rw [hmem'']
    exact loaded_strcmp_writeMap8 _ _ _ hstrcmpDisjoint hstrloaded
  have hread' : read32 σ'.mem env.toNat = some count := by
    rw [hmem'', read32_writeMap8_disjoint _ _ _ _ hheaderDisjoint]
    exact hread
  exact ⟨⟨σ', i', c.steps + 1⟩, vmi', hstep', hpc', hcarry', hs3', hmi',
    hG', hloaded', hstrloaded', hread', htick'⟩

end Vsa.Sim
