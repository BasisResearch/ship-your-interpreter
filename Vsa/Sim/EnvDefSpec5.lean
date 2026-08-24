import Vsa.Sim.EnvDefSpillCommon

/-!
# `env_define` prologue: count load

This module keeps the next prologue instruction separate from the two-site entry
fragment.  Small declarations keep incremental elaboration predictable.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step)
open Vsa.MemRepr
open Vsa.Sim.Code (Env_defineLoaded StrcmpLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- Site `0x80002a64`: load the nonnegative 32-bit environment count into `s3`. -/
theorem env_define_count_load
    (env name pv r sp v18 v20 v21 v8 v9 v22 vmi : BitVec 64)
    (pn hit count : Nat) (c : Config)
    (hRG : EnvDefRegions sp.toNat env.toNat pv.toNat pn hit count)
    (hG : GoodState c.σ) (hloaded : Env_defineLoaded c.σ.mem)
    (hstrloaded : StrcmpLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x80002a64#64 : BitVec 64))
    (hcarry : PrologueCarry c.σ sp env name pv r v18 v20 v21 v8 v9 v22)
    (hmi : c.σ.regs.get? Register.minstret = some vmi)
    (hread : read32 c.σ.mem env.toNat = some count)
    (htick : c.tick < 2) :
    ∃ c' vmi', Step c c' ∧
      c'.σ.regs.get? Register.PC = some (0x80002a68#64 : BitVec 64) ∧
      c'.σ.regs.get? Register.x19 = some (BitVec.ofNat 64 count) ∧
      PrologueCarry c'.σ sp env name pv r v18 v20 v21 v8 v9 v22 ∧
      c'.σ.regs.get? Register.minstret = some vmi' ∧
      GoodState c'.σ ∧ Env_defineLoaded c'.σ.mem ∧ StrcmpLoaded c'.σ.mem ∧
      c'.tick < 2 := by
  obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, hrec⟩ :=
    read32_bytes_ed c.σ.mem env.toNat count hread
  obtain ⟨σ', i', hstep, htick', hG', hmem', hobs⟩ :=
    site_80002a64_ed c.σ c.tick c.steps (0x80002a64#64) vmi env b0 b1 b2 b3
      hG hpc hmi hcarry.2.1 hloaded rfl
      (by rw [off_ed_00]; exact hRG.header_lo)
      (by rw [off_ed_00]; exact hRG.header_hi)
      (by rw [off_ed_00]; exact hRG.header_htif)
      (by rw [off_ed_00]; exact hRG.header_align)
      (by simpa only [off_ed_00] using hb0)
      (by simpa only [off_ed_00] using hb1)
      (by simpa only [off_ed_00] using hb2)
      (by simpa only [off_ed_00] using hb3)
      htick
  have hstep' : Step c ⟨σ', i', c.steps + 1⟩ := by cases c; exact hstep
  have hpc' : σ'.regs.get? Register.PC = some (0x80002a68#64 : BitVec 64) := by
    have h := obs_alu_pc hobs
    rwa [show BitVec.addInt (0x80002a64#64 : BitVec 64) 4 =
      (0x80002a68#64 : BitVec 64) from by decide] at h
  have hs3' : σ'.regs.get? Register.x19 = some (BitVec.ofNat 64 count) := by
    have h := obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext_count_ed b0 b1 b2 b3 count hRG.count_signed hrec] at h
  have hcarry' := prologueCarry_lw19 hobs hcarry
  obtain ⟨vmi', hmi'⟩ := obs_alu_minstret hobs
  have hloaded' : Env_defineLoaded σ'.mem := hmem' ▸ hloaded
  have hstrloaded' : StrcmpLoaded σ'.mem := hmem' ▸ hstrloaded
  exact ⟨⟨σ', i', c.steps + 1⟩, vmi', hstep', hpc', hs3', hcarry', hmi', hG',
    hloaded', hstrloaded', htick'⟩

/-- Site `0x80002a68`: spill `s2` at offset 32 while preserving the loaded count. -/
theorem env_define_spill_s2
    (env name pv r sp v18 v20 v21 v8 v9 v22 countv vmi : BitVec 64)
    (pn hit count : Nat) (c : Config)
    (hRG : EnvDefRegions sp.toNat env.toNat pv.toNat pn hit count)
    (hG : GoodState c.σ) (hloaded : Env_defineLoaded c.σ.mem)
    (hstrloaded : StrcmpLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x80002a68#64 : BitVec 64))
    (hcarry : PrologueCarry c.σ sp env name pv r v18 v20 v21 v8 v9 v22)
    (hs3 : c.σ.regs.get? Register.x19 = some countv)
    (hmi : c.σ.regs.get? Register.minstret = some vmi)
    (htick : c.tick < 2) :
    ∃ c' vmi', Step c c' ∧
      c'.σ.regs.get? Register.PC = some (0x80002a6c#64 : BitVec 64) ∧
      PrologueCarry c'.σ sp env name pv r v18 v20 v21 v8 v9 v22 ∧
      c'.σ.regs.get? Register.x19 = some countv ∧
      c'.σ.regs.get? Register.minstret = some vmi' ∧
      GoodState c'.σ ∧ Env_defineLoaded c'.σ.mem ∧ StrcmpLoaded c'.σ.mem ∧
      c'.tick < 2 := by
  have hsp64 : (64 : Nat) ≤ sp.toNat := hRG.sp_ge
  have hspNat : (sp - 64#64).toNat = sp.toNat - 64 := sp_sub64_toNat sp hsp64
  have haddr : ((sp - 64#64) + sign_extend (m := 64) (0x020#12)).toNat =
      (sp - 64#64).toNat + 32 := by
    apply off_ed_20
    rw [hspNat]
    have := sp.isLt
    omega
  have hcodeDisjoint : (sp - 64#64).toNat + 32 + 8 ≤ 0x80002a5c ∨
      0x80002c10 ≤ (sp - 64#64).toNat + 32 := by
    rw [hspNat]
    have := hRG.frame_code_disjoint
    have := hRG.sp_ge
    omega
  have hstrcmpDisjoint : (sp - 64#64).toNat + 32 + 8 ≤ 0x80006ea0 ∨
      0x80006fcc ≤ (sp - 64#64).toNat + 32 := by
    rw [hspNat]
    have := hRG.frame_strcmp_disjoint
    have := hRG.sp_ge
    omega
  obtain ⟨σ', i', hstep, htick', hG', hmem', hobs⟩ :=
    site_80002a68_ed c.σ c.tick c.steps (0x80002a68#64) vmi (sp - 64#64) v18
      hG hpc hmi hcarry.1 hcarry.2.2.2.2.2.1 hloaded rfl
      (by rw [haddr, hspNat]; have := hRG.frame_lo; have := hRG.frame_win; omega)
      (by rw [haddr, hspNat]; have := hRG.frame_hi; omega)
      (by rw [haddr, hspNat]; have := hRG.frame_win; omega)
      (by rw [haddr, hspNat]; have := hRG.frame_align; omega)
      htick
  have hstep' : Step c ⟨σ', i', c.steps + 1⟩ := by cases c; exact hstep
  have hmem'' := normalize_env_define_store_mem hmem' haddr
  exact finish_env_define_spill hstep' htick' hG' hobs hmem'' (by decide)
    hcarry hs3 hcodeDisjoint hstrcmpDisjoint hloaded hstrloaded

end Vsa.Sim
