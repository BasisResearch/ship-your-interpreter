import Vsa.Sim.Skeleton

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem get?_afterPrelude (σ : MState) (R : Register)
    (hne : (Register.minstret_increment == R) = false) :
    (afterPrelude σ).regs.get? R = σ.regs.get? R := by
  show (σ.regs.insert Register.minstret_increment true).get? R = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hne, dif_neg, reduceCtorEq, not_false_eq_true]

theorem mem_afterPrelude (σ : MState) : (afterPrelude σ).mem = σ.mem := rfl

theorem get?_afterNextPC (σ : MState) (pc : BitVec 64) (R : Register)
    (hne1 : (Register.nextPC == R) = false)
    (hne2 : (Register.minstret_increment == R) = false) :
    (afterNextPC (afterPrelude σ) pc).regs.get? R = σ.regs.get? R := by
  show ((σ.regs.insert Register.minstret_increment true).insert Register.nextPC (BitVec.addInt pc 4)).get? R = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hne1, dif_neg, reduceCtorEq, not_false_eq_true]
  exact get?_afterPrelude σ R hne2

theorem mem_afterNextPC (σ : MState) (pc : BitVec 64) :
    (afterNextPC (afterPrelude σ) pc).mem = σ.mem := rfl

end Vsa.Sim
