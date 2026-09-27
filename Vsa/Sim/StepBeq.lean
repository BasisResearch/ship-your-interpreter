import Vsa.Sim.Skeleton
import Vsa.Sim.StepAddi

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem rX_bits_x5 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x5 = some v) :
    (rX_bits (regidx.Regidx 0x05#5)).run σ = .ok v σ := by
  simp only [rX_bits, rX, PreSail.readReg, bind, EStateM.bind, pure, EStateM.pure,
    EStateM.run, get, getThe, MonadStateOf.get, EStateM.get,
    regval_from_reg, Sail.BitVec.toNatInt,
    Int.ofNat_eq_natCast, Int.toNat_natCast, BitVec.reduceToNat, h]

theorem rX_bits_x6 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x6 = some v) :
    (rX_bits (regidx.Regidx 0x06#5)).run σ = .ok v σ := by
  simp only [rX_bits, rX, PreSail.readReg, bind, EStateM.bind, pure, EStateM.pure,
    EStateM.run, get, getThe, MonadStateOf.get, EStateM.get,
    regval_from_reg, Sail.BitVec.toNatInt,
    Int.ofNat_eq_natCast, Int.toNat_natCast, BitVec.reduceToNat, h]

end Vsa.Sim
