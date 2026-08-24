import Vsa.Sim.EnvDefSpillCommon

/-!
# `env_define` argument-move postprocessing

Compact carry predicates replace the spill-phase register bundle once the
callee-saved values have been written to the frame.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step)
open Vsa.Sim.Code (Env_defineLoaded StrcmpLoaded)

namespace Vsa.Sim

/-- State after `s4 := a0`, retaining the two source arguments still needed. -/
def PrologueMove1 (σ : MState) (sp env name pv : BitVec 64) : Prop :=
  σ.regs.get? Register.x2 = some (sp - 64#64) ∧
  σ.regs.get? Register.x20 = some env ∧
  σ.regs.get? Register.x11 = some name ∧
  σ.regs.get? Register.x12 = some pv

/-- State after `s2 := a1`, retaining the final source argument. -/
def PrologueMove2 (σ : MState) (sp env name pv : BitVec 64) : Prop :=
  σ.regs.get? Register.x2 = some (sp - 64#64) ∧
  σ.regs.get? Register.x20 = some env ∧
  σ.regs.get? Register.x18 = some name ∧
  σ.regs.get? Register.x12 = some pv

/-- Register state at the end of the `env_define` prologue. -/
def EnvDefinePrologueReady (σ : MState) (sp env name pv : BitVec 64) : Prop :=
  σ.regs.get? Register.x2 = some (sp - 64#64) ∧
  σ.regs.get? Register.x20 = some env ∧
  σ.regs.get? Register.x18 = some name ∧
  σ.regs.get? Register.x21 = some pv

/-- Common postprocessing for a prologue ALU step. -/
theorem finish_env_define_alu
    {P : MState → Prop} {c : Config} {σ' : MState} {i' : Nat}
    {pc pc' countv vmi : BitVec 64} {rd : Register} {value : RegisterType rd}
    (hstep : Step c ⟨σ', i', c.steps + 1⟩)
    (htick' : i' < 2) (hG' : GoodState σ') (hmem : σ'.mem = c.σ.mem)
    (hobs : ReadsLikePost σ' (sigmaPost_alu c.σ pc vmi rd value))
    (hnext : BitVec.addInt pc 4 = pc')
    (hrdCount : (rd == Register.x19) = false)
    (hpost : P σ')
    (hcount : c.σ.regs.get? Register.x19 = some countv)
    (hloaded : Env_defineLoaded c.σ.mem) (hstrloaded : StrcmpLoaded c.σ.mem) :
    ∃ c' vmi', Step c c' ∧
      c'.σ.regs.get? Register.PC = some pc' ∧ P c'.σ ∧
      c'.σ.regs.get? Register.x19 = some countv ∧
      c'.σ.regs.get? Register.minstret = some vmi' ∧
      GoodState c'.σ ∧ Env_defineLoaded c'.σ.mem ∧ StrcmpLoaded c'.σ.mem ∧
      c'.tick < 2 := by
  have hpc' := obs_alu_pc hobs
  rw [hnext] at hpc'
  have hcount' := obs_alu_other hobs Register.x19 (by decide) (by decide)
    (by decide) (by decide) (by decide) hrdCount (by decide) (by decide) hcount
  obtain ⟨vmi', hmi'⟩ := obs_alu_minstret hobs
  have hloaded' : Env_defineLoaded σ'.mem := hmem ▸ hloaded
  have hstrloaded' : StrcmpLoaded σ'.mem := hmem ▸ hstrloaded
  exact ⟨⟨σ', i', c.steps + 1⟩, vmi', hstep, hpc', hpost, hcount', hmi',
    hG', hloaded', hstrloaded', htick'⟩

end Vsa.Sim
