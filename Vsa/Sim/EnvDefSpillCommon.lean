import Vsa.Sim.EnvDefSpec4

/-!
# `env_define` spill postprocessing

Shared memory normalization and frame preservation for bounded prologue stores.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step)
open Vsa.MemRepr
open Vsa.Sim.Code (Env_defineLoaded StrcmpLoaded)

namespace Vsa.Sim

/-- Normalize a store-site memory result without rewriting its dependent observation. -/
theorem normalize_env_define_store_mem
    {σ σ' : MState} {pc value : BitVec 64} {rawAddr addr : Nat}
    (hmem : σ'.mem =
      writeMap8 (afterNextPC (afterPrelude σ) pc).mem rawAddr (sdData_val value))
    (haddr : rawAddr = addr) :
    σ'.mem = writeMap8 σ.mem addr (sdData_val value) := by
  calc
    σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) pc).mem rawAddr
        (sdData_val value) := hmem
    _ = writeMap8 σ.mem addr (sdData_val value) := by
      rw [mem_afterNextPC, haddr]

/-- Common postprocessing for every callee-saved spill in the prologue. -/
theorem finish_env_define_spill
    {c : Config} {σ' : MState} {i' : Nat} {mPost : Mem}
    {pc pc' value countv vmi : BitVec 64} {addr : Nat}
    {sp env name pv r v18 v20 v21 v8 v9 v22 : BitVec 64}
    (hstep : Step c ⟨σ', i', c.steps + 1⟩)
    (htick' : i' < 2) (hG' : GoodState σ')
    (hobs : ReadsLikePost σ' (sigmaPost_store c.σ pc vmi mPost))
    (hmem : σ'.mem = writeMap8 c.σ.mem addr (sdData_val value))
    (hnext : BitVec.addInt pc 4 = pc')
    (hcarry : PrologueCarry c.σ sp env name pv r v18 v20 v21 v8 v9 v22)
    (hcount : c.σ.regs.get? Register.x19 = some countv)
    (hcode : addr + 8 ≤ 0x80002a5c ∨ 0x80002c10 ≤ addr)
    (hstrcmpCode : addr + 8 ≤ 0x80006ea0 ∨ 0x80006fcc ≤ addr)
    (hloaded : Env_defineLoaded c.σ.mem) (hstrloaded : StrcmpLoaded c.σ.mem) :
    ∃ c' vmi', Step c c' ∧
      c'.σ.regs.get? Register.PC = some pc' ∧
      PrologueCarry c'.σ sp env name pv r v18 v20 v21 v8 v9 v22 ∧
      c'.σ.regs.get? Register.x19 = some countv ∧
      c'.σ.regs.get? Register.minstret = some vmi' ∧
      GoodState c'.σ ∧ Env_defineLoaded c'.σ.mem ∧ StrcmpLoaded c'.σ.mem ∧
      c'.tick < 2 := by
  have hpc' := obs_store_pc hobs
  rw [hnext] at hpc'
  have hcarry' := prologueCarry_store hobs hcarry
  have hcount' := obs_store_other hobs Register.x19 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hcount
  obtain ⟨vmi', hmi'⟩ := obs_store_minstret hobs
  have hloadedWrite := loaded_envdef_writeMap8 c.σ.mem addr
    (sdData_val value) hcode hloaded
  have hloaded' : Env_defineLoaded σ'.mem := by
    rw [hmem]
    exact hloadedWrite
  have hstrloadedWrite := loaded_strcmp_writeMap8 c.σ.mem addr
    (sdData_val value) hstrcmpCode hstrloaded
  have hstrloaded' : StrcmpLoaded σ'.mem := by
    rw [hmem]
    exact hstrloadedWrite
  exact ⟨⟨σ', i', c.steps + 1⟩, vmi', hstep, hpc', hcarry', hcount', hmi',
    hG', hloaded', hstrloaded', htick'⟩

end Vsa.Sim
