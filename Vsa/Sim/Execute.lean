import Vsa.Elf
import Vsa.Sim.StateNF

/-!
# Layer 0, item 3 support — execute-clause characterization for ADDI

Symbolic characterization of the model's register read/write primitives and
the `ADDI` execute clause over an arbitrary symbolic `SequentialState`
(`PLAN-InterpSim.md` §Layer 0 item 3). These are the Layer-0 building blocks
that the `try_step` skeleton lemma composes over the decoded instruction.

The load-bearing move is reducing the 32-way `match r with` inside `rX`/`wX`
on a *concrete* register index. The index arrives as
`Regno (BitVec.toNatInt i)` with `i` a concrete `BitVec 5`; simplifying
`BitVec.toNatInt`/`Int.ofNat`/`Int.toNat` down to the `Nat` literal makes the
match select the single reachable arm.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- `x0` reads as the constant zero, touching no state. -/
theorem rX_bits_zero (σ : SequentialState RegisterType trivialChoiceSource) :
    (rX_bits (regidx.Regidx 0x00#5)).run σ = .ok (0#64) σ := by
  simp only [rX_bits, rX, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    regval_from_reg, zero_reg, zeros, Sail.BitVec.toNatInt,
    Int.ofNat_eq_natCast, Int.toNat_natCast, BitVec.reduceToNat, BitVec.zero_eq]

/-- `x10` reads the value pinned by hypothesis, touching no state. -/
theorem rX_bits_x10 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x10 = some v) :
    (rX_bits (regidx.Regidx 0x0a#5)).run σ = .ok v σ := by
  simp only [rX_bits, rX, PreSail.readReg, bind, EStateM.bind, pure, EStateM.pure,
    EStateM.run, get, getThe, MonadStateOf.get, EStateM.get,
    regval_from_reg, Sail.BitVec.toNatInt,
    Int.ofNat_eq_natCast, Int.toNat_natCast, BitVec.reduceToNat, h]

/-- `x10` write inserts into the register file; the write callback collapses to
a no-op without perturbing state (`reg_name_forwards` reduces to a pure,
state-preserving string that the following bind discards). -/
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

/-- Full `ADDI x10, x0, imm` execute clause: reads `x0` (constant zero), adds the
sign-extended immediate, writes `x10`, retires. The result state is the single
`x10` insert; the value is the model's literal `0#64 + sign_extend imm`. -/
theorem execute_addi_x0_x10 (σ : SequentialState RegisterType trivialChoiceSource)
    (imm : BitVec 12) :
    (execute (instruction.ITYPE
        (imm, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, iop.ADDI))).run σ
      = .ok RETIRE_SUCCESS
          {σ with regs :=
            σ.regs.insert Register.x10 (0#64 + sign_extend (m := 64) imm)} := by
  simp only [execute, execute_ITYPE,
    rX_bits, rX, PreSail.writeReg,
    wX_bits, wX, regval_from_reg, regval_into_reg,
    bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, Int.toNat_natCast, BitVec.reduceToNat,
    bne_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true, if_true,
    xreg_write_callback, xreg_full_write_callback, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet,
    reg_name_forwards, get_config_use_abi_names, encdec_reg_forwards_matches,
    Functions.not, Bool.not_false, Bool.false_eq_true, reduceIte, zero_reg, zeros,
    BitVec.zero_eq]

end Vsa.Sim
