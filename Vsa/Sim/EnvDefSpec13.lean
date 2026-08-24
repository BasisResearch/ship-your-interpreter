import Vsa.Sim.EnvDefMoveCommon

/-! # `env_define` prologue: move `a1` to `s2` -/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (Config Step)
open Vsa.Sim.Code (Env_defineLoaded StrcmpLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- Site `0x80002a88`: move the name pointer from `a1` to `s2`. -/
theorem env_define_move_s2
    (sp env name pv countv vmi : BitVec 64) (c : Config)
    (hG : GoodState c.σ) (hloaded : Env_defineLoaded c.σ.mem)
    (hstrloaded : StrcmpLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x80002a88#64 : BitVec 64))
    (hcarry : PrologueMove1 c.σ sp env name pv)
    (hs3 : c.σ.regs.get? Register.x19 = some countv)
    (hmi : c.σ.regs.get? Register.minstret = some vmi)
    (htick : c.tick < 2) :
    ∃ c' vmi', Step c c' ∧
      c'.σ.regs.get? Register.PC = some (0x80002a8c#64 : BitVec 64) ∧
      PrologueMove2 c'.σ sp env name pv ∧
      c'.σ.regs.get? Register.x19 = some countv ∧
      c'.σ.regs.get? Register.minstret = some vmi' ∧
      GoodState c'.σ ∧ Env_defineLoaded c'.σ.mem ∧ StrcmpLoaded c'.σ.mem ∧
      c'.tick < 2 := by
  obtain ⟨σ', i', hstep, htick', hG', hmem', hobs⟩ :=
    site_80002a88_ed c.σ c.tick c.steps (0x80002a88#64) vmi name
      hG hpc hmi hcarry.2.2.1 hloaded rfl htick
  have hstep' : Step c ⟨σ', i', c.steps + 1⟩ := by cases c; exact hstep
  have hpost : PrologueMove2 σ' sp env name pv := by
    refine ⟨
      obs_alu_other hobs Register.x2 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) hcarry.1,
      obs_alu_other hobs Register.x20 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) hcarry.2.1,
      ?_,
      obs_alu_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) hcarry.2.2.2⟩
    have hx18 := obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
    have hzero : (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 := by decide
    simpa only [hzero, BitVec.add_zero] using hx18
  exact finish_env_define_alu
    (P := fun σ => PrologueMove2 σ sp env name pv)
    (pc' := (0x80002a8c#64 : BitVec 64))
    hstep' htick' hG' hmem' hobs (by decide) (by decide) hpost hs3 hloaded hstrloaded

end Vsa.Sim
