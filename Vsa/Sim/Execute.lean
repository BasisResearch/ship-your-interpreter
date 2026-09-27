import Vsa.Elf
import Vsa.Sim.StateNF

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

theorem rX_bits_x10 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x10 = some v) :
    (rX_bits (regidx.Regidx 0x0a#5)).run σ = .ok v σ := by
  simp only [rX_bits, rX, PreSail.readReg, bind, EStateM.bind, pure, EStateM.pure,
    EStateM.run, get, getThe, MonadStateOf.get, EStateM.get,
    regval_from_reg, Sail.BitVec.toNatInt,
    Int.ofNat_eq_natCast, Int.toNat_natCast, BitVec.reduceToNat, h]

theorem wX_bits_x10 (σ : SequentialState RegisterType trivialChoiceSource)
    (d : BitVec 64) :
    (wX_bits (regidx.Regidx 0x0a#5) d).run σ
      = .ok () {σ with regs := σ.regs.insert Register.x10 d} := by
  simp only [wX_bits, wX, PreSail.writeReg, bind, EStateM.bind, pure, EStateM.pure,
    EStateM.run, regval_into_reg, Sail.BitVec.toNatInt,
    Int.ofNat_eq_natCast, Int.toNat_natCast, BitVec.reduceToNat,
    bne_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true, if_true,
    xreg_write_callback, xreg_full_write_callback, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet,
    reg_name_forwards, get_config_use_abi_names, encdec_reg_forwards_matches,
    Functions.not, Bool.not_false, Bool.false_eq_true, reduceIte]

end Vsa.Sim
