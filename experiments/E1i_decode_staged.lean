import Vsa.Elf
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

example (σ : SequentialState RegisterType trivialChoiceSource)
    (hmisa : σ.regs.get? Register.misa =
      some ((_update_Misa_MXL (Mk_Misa (BitVec.zero 64))
        (architecture_bits_forwards Architecture.RV64)) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((Mk_Seccfg (BitVec.zero 64)) : RegisterType Register.mseccfg)) :
    (encdec_backwards 0x00000513#32).run σ =
      .ok (instruction.ITYPE (0x000#12, regidx.Regidx 0x00#5,
        regidx.Regidx 0x0a#5, iop.ADDI)) σ := by
  simp only [encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    throw, throwThe, MonadExceptOf.throw, EStateM.throw, get_xLPE, readReg]
  simp +decide [encdec_reg_backwards_matches, encdec_uop_backwards_matches,
    encdec_bop_backwards_matches, encdec_iop_backwards_matches,
    encdec_reg_backwards, encdec_uop_backwards, encdec_bop_backwards,
    encdec_iop_backwards, bind, EStateM.bind, pure, EStateM.pure,
    throw, throwThe, MonadExceptOf.throw, EStateM.throw]
  constructor
  · apply BitVec.eq_of_toNat_eq; decide
  · apply BitVec.eq_of_toNat_eq; decide
