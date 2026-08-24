import Vsa.Sim.EnvDefEntryCommon

/-! # `env_define` prologue: allocate the 64-byte frame -/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (Config Step)
open Vsa.MemRepr
open Vsa.Sim.Code (Env_defineLoaded StrcmpLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- Site `0x80002a5c`: allocate the frame and establish `PrologueCarry`. -/
theorem env_define_frame_alloc
    (sp env name pv r v18 v20 v21 v8 v9 v22 savedS3 vmi : BitVec 64)
    (count : Nat) (c : Config)
    (hG : GoodState c.σ) (hloaded : Env_defineLoaded c.σ.mem)
    (hstrloaded : StrcmpLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x80002a5c#64 : BitVec 64))
    (hentry : EnvDefineEntry c.σ sp env name pv r v18 v20 v21 v8 v9 v22)
    (hs3 : c.σ.regs.get? Register.x19 = some savedS3)
    (hmi : c.σ.regs.get? Register.minstret = some vmi)
    (hread : read32 c.σ.mem env.toNat = some count)
    (htick : c.tick < 2) :
    ∃ c' vmi', Step c c' ∧
      c'.σ.regs.get? Register.PC = some (0x80002a60#64 : BitVec 64) ∧
      (PrologueCarry c'.σ sp env name pv r v18 v20 v21 v8 v9 v22 ∧
        read32 c'.σ.mem env.toNat = some count) ∧
      c'.σ.regs.get? Register.x19 = some savedS3 ∧
      c'.σ.regs.get? Register.minstret = some vmi' ∧
      GoodState c'.σ ∧ Env_defineLoaded c'.σ.mem ∧ StrcmpLoaded c'.σ.mem ∧
      c'.tick < 2 := by
  obtain ⟨σ', i', hstep, htick', hG', hmem', hobs⟩ :=
    site_80002a5c_ed c.σ c.tick c.steps (0x80002a5c#64) vmi sp
      hG hpc hmi hentry.1 hloaded rfl htick
  have hstep' : Step c ⟨σ', i', c.steps + 1⟩ := by cases c; exact hstep
  rcases hentry with ⟨h2, h10, h11, h12, h1, h18, h20, h21, h8, h9, h22⟩
  have hpost : PrologueCarry σ' sp env name pv r v18 v20 v21 v8 v9 v22 := by
    refine ⟨?_,
      obs_alu_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) h10,
      obs_alu_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) h11,
      obs_alu_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) h12,
      obs_alu_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) h1,
      obs_alu_other hobs Register.x18 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) h18,
      obs_alu_other hobs Register.x20 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) h20,
      obs_alu_other hobs Register.x21 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) h21,
      obs_alu_other hobs Register.x8 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) h8,
      obs_alu_other hobs Register.x9 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) h9,
      obs_alu_other hobs Register.x22 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) h22⟩
    have hx2 := obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sp_sub64 sp] at hx2
  have hread' : read32 σ'.mem env.toNat = some count := by
    rw [hmem']
    exact hread
  exact finish_env_define_alu
    (P := fun σ => PrologueCarry σ sp env name pv r v18 v20 v21 v8 v9 v22 ∧
      read32 σ.mem env.toNat = some count)
    (pc' := (0x80002a60#64 : BitVec 64))
    hstep' htick' hG' hmem' hobs (by decide) (by decide) ⟨hpost, hread'⟩ hs3
      hloaded hstrloaded

end Vsa.Sim
