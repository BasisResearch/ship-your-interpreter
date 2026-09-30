import Vsa.Sim.InitValues

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register

set_option maxHeartbeats 16000000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false

namespace Vsa.Sim.DecodeTable

theorem decode_00069463
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00069463#32).run σ =
      .ok (LeanRV64DExecutable.instruction.BTYPE (0x0008#13, LeanRV64DExecutable.regidx.Regidx 0x00#5, LeanRV64DExecutable.regidx.Regidx 0x0d#5, LeanRV64DExecutable.bop.BNE)) σ := by
  simp only [ext_decode, encdec_backwards, EStateM.run, bind, EStateM.bind,
    pure, EStateM.pure, PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
    currentlyEnabled, hartSupports, get_xLPE, Vsa.Sim.initMisa,
    _hmisa, hpriv, hsec]
  rfl

theorem decode_00069a63
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00069a63#32).run σ =
      .ok (LeanRV64DExecutable.instruction.BTYPE (0x0014#13, LeanRV64DExecutable.regidx.Regidx 0x00#5, LeanRV64DExecutable.regidx.Regidx 0x0d#5, LeanRV64DExecutable.bop.BNE)) σ := by
  simp only [ext_decode, encdec_backwards, EStateM.run, bind, EStateM.bind,
    pure, EStateM.pure, PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
    currentlyEnabled, hartSupports, get_xLPE, Vsa.Sim.initMisa,
    _hmisa, hpriv, hsec]
  rfl

theorem decode_0006b503
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x0006b503#32).run σ =
      .ok (LeanRV64DExecutable.instruction.LOAD (0x000#12, LeanRV64DExecutable.regidx.Regidx 0x0d#5, LeanRV64DExecutable.regidx.Regidx 0x0a#5, false, 8)) σ := by
  simp only [ext_decode, encdec_backwards, EStateM.run, bind, EStateM.bind,
    pure, EStateM.pure, PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
    currentlyEnabled, hartSupports, get_xLPE, Vsa.Sim.initMisa,
    _hmisa, hpriv, hsec]
  rfl

theorem decode_0006b583
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x0006b583#32).run σ =
      .ok (LeanRV64DExecutable.instruction.LOAD (0x000#12, LeanRV64DExecutable.regidx.Regidx 0x0d#5, LeanRV64DExecutable.regidx.Regidx 0x0b#5, false, 8)) σ := by
  simp only [ext_decode, encdec_backwards, EStateM.run, bind, EStateM.bind,
    pure, EStateM.pure, PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
    currentlyEnabled, hartSupports, get_xLPE, Vsa.Sim.initMisa,
    _hmisa, hpriv, hsec]
  rfl

theorem decode_0006b703
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x0006b703#32).run σ =
      .ok (LeanRV64DExecutable.instruction.LOAD (0x000#12, LeanRV64DExecutable.regidx.Regidx 0x0d#5, LeanRV64DExecutable.regidx.Regidx 0x0e#5, false, 8)) σ := by
  simp only [ext_decode, encdec_backwards, EStateM.run, bind, EStateM.bind,
    pure, EStateM.pure, PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
    currentlyEnabled, hartSupports, get_xLPE, Vsa.Sim.initMisa,
    _hmisa, hpriv, hsec]
  rfl

theorem decode_0006b803
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x0006b803#32).run σ =
      .ok (LeanRV64DExecutable.instruction.LOAD (0x000#12, LeanRV64DExecutable.regidx.Regidx 0x0d#5, LeanRV64DExecutable.regidx.Regidx 0x10#5, false, 8)) σ := by
  simp only [ext_decode, encdec_backwards, EStateM.run, bind, EStateM.bind,
    pure, EStateM.pure, PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
    currentlyEnabled, hartSupports, get_xLPE, Vsa.Sim.initMisa,
    _hmisa, hpriv, hsec]
  rfl

end Vsa.Sim.DecodeTable
