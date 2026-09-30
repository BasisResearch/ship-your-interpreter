import Vsa.Sim.InitValues

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register

set_option maxHeartbeats 16000000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false

namespace Vsa.Sim.DecodeTable

theorem decode_0dc12423
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x0dc12423#32).run σ =
      .ok (LeanRV64DExecutable.instruction.STORE (0x0c8#12, LeanRV64DExecutable.regidx.Regidx 0x1c#5, LeanRV64DExecutable.regidx.Regidx 0x02#5, 4)) σ := by
  simp only [ext_decode, encdec_backwards, EStateM.run, bind, EStateM.bind,
    pure, EStateM.pure, PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
    currentlyEnabled, hartSupports, get_xLPE, Vsa.Sim.initMisa,
    _hmisa, hpriv, hsec]
  rfl

theorem decode_0de5051b
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x0de5051b#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ADDIW (0x0de#12, LeanRV64DExecutable.regidx.Regidx 0x0a#5, LeanRV64DExecutable.regidx.Regidx 0x0a#5)) σ := by
  simp only [ext_decode, encdec_backwards, EStateM.run, bind, EStateM.bind,
    pure, EStateM.pure, PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
    currentlyEnabled, hartSupports, get_xLPE, Vsa.Sim.initMisa,
    _hmisa, hpriv, hsec]
  rfl

theorem decode_0de5859b
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x0de5859b#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ADDIW (0x0de#12, LeanRV64DExecutable.regidx.Regidx 0x0b#5, LeanRV64DExecutable.regidx.Regidx 0x0b#5)) σ := by
  simp only [ext_decode, encdec_backwards, EStateM.run, bind, EStateM.bind,
    pure, EStateM.pure, PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
    currentlyEnabled, hartSupports, get_xLPE, Vsa.Sim.initMisa,
    _hmisa, hpriv, hsec]
  rfl

theorem decode_0e010613
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x0e010613#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ITYPE (0x0e0#12, LeanRV64DExecutable.regidx.Regidx 0x02#5, LeanRV64DExecutable.regidx.Regidx 0x0c#5, LeanRV64DExecutable.iop.ADDI)) σ := by
  simp only [ext_decode, encdec_backwards, EStateM.run, bind, EStateM.bind,
    pure, EStateM.pure, PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
    currentlyEnabled, hartSupports, get_xLPE, Vsa.Sim.initMisa,
    _hmisa, hpriv, hsec]
  rfl

theorem decode_0e012423
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x0e012423#32).run σ =
      .ok (LeanRV64DExecutable.instruction.STORE (0x0e8#12, LeanRV64DExecutable.regidx.Regidx 0x00#5, LeanRV64DExecutable.regidx.Regidx 0x02#5, 4)) σ := by
  simp only [ext_decode, encdec_backwards, EStateM.run, bind, EStateM.bind,
    pure, EStateM.pure, PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
    currentlyEnabled, hartSupports, get_xLPE, Vsa.Sim.initMisa,
    _hmisa, hpriv, hsec]
  rfl

theorem decode_0e013823
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x0e013823#32).run σ =
      .ok (LeanRV64DExecutable.instruction.STORE (0x0f0#12, LeanRV64DExecutable.regidx.Regidx 0x00#5, LeanRV64DExecutable.regidx.Regidx 0x02#5, 8)) σ := by
  simp only [ext_decode, encdec_backwards, EStateM.run, bind, EStateM.bind,
    pure, EStateM.pure, PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
    currentlyEnabled, hartSupports, get_xLPE, Vsa.Sim.initMisa,
    _hmisa, hpriv, hsec]
  rfl

theorem decode_0e040513
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x0e040513#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ITYPE (0x0e0#12, LeanRV64DExecutable.regidx.Regidx 0x08#5, LeanRV64DExecutable.regidx.Regidx 0x0a#5, LeanRV64DExecutable.iop.ADDI)) σ := by
  simp only [ext_decode, encdec_backwards, EStateM.run, bind, EStateM.bind,
    pure, EStateM.pure, PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
    currentlyEnabled, hartSupports, get_xLPE, Vsa.Sim.initMisa,
    _hmisa, hpriv, hsec]
  rfl

end Vsa.Sim.DecodeTable
