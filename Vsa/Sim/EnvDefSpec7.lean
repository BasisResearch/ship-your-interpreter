import Vsa.Sim.EnvDefSpillCommon

/-!
# `env_define` prologue: spill `s5`

This module advances the prologue by one bounded store step.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (Config Step)
open Vsa.Sim.Code (Env_defineLoaded StrcmpLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- Site `0x80002a70`: spill `s5` at offset 8 while preserving the loaded count. -/
theorem env_define_spill_s5
    (env name pv r sp v18 v20 v21 v8 v9 v22 countv vmi : BitVec 64)
    (pn hit count : Nat) (c : Config)
    (hRG : EnvDefRegions sp.toNat env.toNat pv.toNat pn hit count)
    (hG : GoodState c.σ) (hloaded : Env_defineLoaded c.σ.mem)
    (hstrloaded : StrcmpLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x80002a70#64 : BitVec 64))
    (hcarry : PrologueCarry c.σ sp env name pv r v18 v20 v21 v8 v9 v22)
    (hs3 : c.σ.regs.get? Register.x19 = some countv)
    (hmi : c.σ.regs.get? Register.minstret = some vmi)
    (htick : c.tick < 2) :
    ∃ c' vmi', Step c c' ∧
      c'.σ.regs.get? Register.PC = some (0x80002a74#64 : BitVec 64) ∧
      PrologueCarry c'.σ sp env name pv r v18 v20 v21 v8 v9 v22 ∧
      c'.σ.regs.get? Register.x19 = some countv ∧
      c'.σ.regs.get? Register.minstret = some vmi' ∧
      GoodState c'.σ ∧ Env_defineLoaded c'.σ.mem ∧ StrcmpLoaded c'.σ.mem ∧
      c'.tick < 2 := by
  have hsp64 : (64 : Nat) ≤ sp.toNat := hRG.sp_ge
  have hspNat : (sp - 64#64).toNat = sp.toNat - 64 := sp_sub64_toNat sp hsp64
  have haddr : ((sp - 64#64) + sign_extend (m := 64) (0x008#12)).toNat =
      (sp - 64#64).toNat + 8 := by
    apply off_ed_08
    rw [hspNat]
    have := sp.isLt
    omega
  have hcodeDisjoint : (sp - 64#64).toNat + 8 + 8 ≤ 0x80002a5c ∨
      0x80002c10 ≤ (sp - 64#64).toNat + 8 := by
    rw [hspNat]
    have := hRG.frame_code_disjoint
    have := hRG.sp_ge
    omega
  have hstrcmpDisjoint : (sp - 64#64).toNat + 8 + 8 ≤ 0x80006ea0 ∨
      0x80006fcc ≤ (sp - 64#64).toNat + 8 := by
    rw [hspNat]
    have := hRG.frame_strcmp_disjoint
    have := hRG.sp_ge
    omega
  obtain ⟨σ', i', hstep, htick', hG', hmem', hobs⟩ :=
    site_80002a70_ed c.σ c.tick c.steps (0x80002a70#64) vmi (sp - 64#64) v21
      hG hpc hmi hcarry.1 hcarry.2.2.2.2.2.2.2.1 hloaded rfl
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
