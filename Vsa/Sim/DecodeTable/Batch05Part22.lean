import Vsa.Sim.InitValues

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register

set_option maxHeartbeats 16000000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false

namespace Vsa.Sim.DecodeTable

theorem decode_010e5463
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x010e5463#32).run σ =
      .ok (LeanRV64DExecutable.instruction.BTYPE (0x0008#13, LeanRV64DExecutable.regidx.Regidx 0x10#5, LeanRV64DExecutable.regidx.Regidx 0x1c#5, LeanRV64DExecutable.bop.BGE)) σ := by
  simp only [ext_decode, encdec_backwards, EStateM.run, bind, EStateM.bind,
    pure, EStateM.pure, PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
    currentlyEnabled, hartSupports, get_xLPE, Vsa.Sim.initMisa,
    _hmisa, hpriv, hsec]
  rfl

theorem decode_010e7313
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x010e7313#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ITYPE (0x010#12, LeanRV64DExecutable.regidx.Regidx 0x1c#5, LeanRV64DExecutable.regidx.Regidx 0x06#5, LeanRV64DExecutable.iop.ANDI)) σ := by
  simp only [ext_decode, encdec_backwards, EStateM.run, bind, EStateM.bind,
    pure, EStateM.pure, PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
    currentlyEnabled, hartSupports, get_xLPE, Vsa.Sim.initMisa,
    _hmisa, hpriv, hsec]
  rfl

theorem decode_010f3783
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x010f3783#32).run σ =
      .ok (LeanRV64DExecutable.instruction.LOAD (0x010#12, LeanRV64DExecutable.regidx.Regidx 0x1e#5, LeanRV64DExecutable.regidx.Regidx 0x0f#5, false, 8)) σ := by
  simp only [ext_decode, encdec_backwards, EStateM.run, bind, EStateM.bind,
    pure, EStateM.pure, PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
    currentlyEnabled, hartSupports, get_xLPE, Vsa.Sim.initMisa,
    _hmisa, hpriv, hsec]
  rfl

theorem decode_011020ef
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x011020ef#32).run σ =
      .ok (LeanRV64DExecutable.instruction.JAL (0x002810#21, LeanRV64DExecutable.regidx.Regidx 0x01#5)) σ := by
  simp only [ext_decode, encdec_backwards, EStateM.run, bind, EStateM.bind,
    pure, EStateM.pure, PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
    currentlyEnabled, hartSupports, get_xLPE, Vsa.Sim.initMisa,
    _hmisa, hpriv, hsec]
  rfl

theorem decode_01113423
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x01113423#32).run σ =
      .ok (LeanRV64DExecutable.instruction.STORE (0x008#12, LeanRV64DExecutable.regidx.Regidx 0x11#5, LeanRV64DExecutable.regidx.Regidx 0x02#5, 8)) σ := by
  simp only [ext_decode, encdec_backwards, EStateM.run, bind, EStateM.bind,
    pure, EStateM.pure, PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
    currentlyEnabled, hartSupports, get_xLPE, Vsa.Sim.initMisa,
    _hmisa, hpriv, hsec]
  rfl

theorem decode_01113c23
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x01113c23#32).run σ =
      .ok (LeanRV64DExecutable.instruction.STORE (0x018#12, LeanRV64DExecutable.regidx.Regidx 0x11#5, LeanRV64DExecutable.regidx.Regidx 0x02#5, 8)) σ := by
  simp only [ext_decode, encdec_backwards, EStateM.run, bind, EStateM.bind,
    pure, EStateM.pure, PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
    currentlyEnabled, hartSupports, get_xLPE, Vsa.Sim.initMisa,
    _hmisa, hpriv, hsec]
  rfl

end Vsa.Sim.DecodeTable
