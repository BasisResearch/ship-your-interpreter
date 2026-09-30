import Vsa.Elf
import Vsa.Sim.RegAccess

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem rX_bits_zero (σ : SequentialState RegisterType trivialChoiceSource) :
    (rX_bits (regidx.Regidx 0x00#5)).run σ = .ok (0#64) σ := by
  simp only [rX_bits, rX, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    regval_from_reg, zero_reg, zeros, Sail.BitVec.toNatInt,
    Int.ofNat_eq_natCast, Int.toNat_natCast, BitVec.reduceToNat, BitVec.zero_eq]

end Vsa.Sim
