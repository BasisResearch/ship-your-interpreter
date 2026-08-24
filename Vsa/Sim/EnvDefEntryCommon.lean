import Vsa.Sim.EnvDefMoveCommon

/-! # `env_define` entry register state -/

open LeanRV64DExecutable Vsa
open Register
open Vsa.Machine (MState)

namespace Vsa.Sim

/-- Registers required at the entry of `env_define`, before frame allocation. -/
def EnvDefineEntry
    (σ : MState) (sp env name pv r v18 v20 v21 v8 v9 v22 : BitVec 64) : Prop :=
  σ.regs.get? Register.x2 = some sp ∧
  σ.regs.get? Register.x10 = some env ∧ σ.regs.get? Register.x11 = some name ∧
  σ.regs.get? Register.x12 = some pv ∧ σ.regs.get? Register.x1 = some r ∧
  σ.regs.get? Register.x18 = some v18 ∧ σ.regs.get? Register.x20 = some v20 ∧
  σ.regs.get? Register.x21 = some v21 ∧ σ.regs.get? Register.x8 = some v8 ∧
  σ.regs.get? Register.x9 = some v9 ∧ σ.regs.get? Register.x22 = some v22

end Vsa.Sim
