import Vsa.Sim.InitValues

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register

set_option maxHeartbeats 16000000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false

namespace Vsa.Sim.DecodeTable

theorem decode_fff60693
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0xfff60693#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ITYPE (0xfff#12, LeanRV64DExecutable.regidx.Regidx 0x0c#5, LeanRV64DExecutable.regidx.Regidx 0x0d#5, LeanRV64DExecutable.iop.ADDI)) σ := by
  simp only [ext_decode, encdec_backwards, EStateM.run, bind, EStateM.bind,
    pure, EStateM.pure, PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
    currentlyEnabled, hartSupports, get_xLPE, Vsa.Sim.initMisa,
    _hmisa, hpriv, hsec]
  rfl

theorem decode_fff6081b
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0xfff6081b#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ADDIW (0xfff#12, LeanRV64DExecutable.regidx.Regidx 0x0c#5, LeanRV64DExecutable.regidx.Regidx 0x10#5)) σ := by
  simp only [ext_decode, encdec_backwards, EStateM.run, bind, EStateM.bind,
    pure, EStateM.pure, PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
    currentlyEnabled, hartSupports, get_xLPE, Vsa.Sim.initMisa,
    _hmisa, hpriv, hsec]
  rfl

theorem decode_fff68693
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0xfff68693#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ITYPE (0xfff#12, LeanRV64DExecutable.regidx.Regidx 0x0d#5, LeanRV64DExecutable.regidx.Regidx 0x0d#5, LeanRV64DExecutable.iop.ADDI)) σ := by
  simp only [ext_decode, encdec_backwards, EStateM.run, bind, EStateM.bind,
    pure, EStateM.pure, PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
    currentlyEnabled, hartSupports, get_xLPE, Vsa.Sim.initMisa,
    _hmisa, hpriv, hsec]
  rfl

theorem decode_fff6869b
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0xfff6869b#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ADDIW (0xfff#12, LeanRV64DExecutable.regidx.Regidx 0x0d#5, LeanRV64DExecutable.regidx.Regidx 0x0d#5)) σ := by
  simp only [ext_decode, encdec_backwards, EStateM.run, bind, EStateM.bind,
    pure, EStateM.pure, PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
    currentlyEnabled, hartSupports, get_xLPE, Vsa.Sim.initMisa,
    _hmisa, hpriv, hsec]
  rfl

theorem decode_fff70513
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0xfff70513#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ITYPE (0xfff#12, LeanRV64DExecutable.regidx.Regidx 0x0e#5, LeanRV64DExecutable.regidx.Regidx 0x0a#5, LeanRV64DExecutable.iop.ADDI)) σ := by
  simp only [ext_decode, encdec_backwards, EStateM.run, bind, EStateM.bind,
    pure, EStateM.pure, PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
    currentlyEnabled, hartSupports, get_xLPE, Vsa.Sim.initMisa,
    _hmisa, hpriv, hsec]
  rfl

theorem decode_fff7071b
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0xfff7071b#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ADDIW (0xfff#12, LeanRV64DExecutable.regidx.Regidx 0x0e#5, LeanRV64DExecutable.regidx.Regidx 0x0e#5)) σ := by
  simp only [ext_decode, encdec_backwards, EStateM.run, bind, EStateM.bind,
    pure, EStateM.pure, PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
    currentlyEnabled, hartSupports, get_xLPE, Vsa.Sim.initMisa,
    _hmisa, hpriv, hsec]
  rfl

end Vsa.Sim.DecodeTable
