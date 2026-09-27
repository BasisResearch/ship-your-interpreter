import Vsa.Sim.InitValues

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register

set_option maxHeartbeats 16000000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false

namespace Vsa.Sim.DecodeTable

theorem decode_01870733
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x01870733#32).run σ =
      .ok (LeanRV64DExecutable.instruction.RTYPE (LeanRV64DExecutable.regidx.Regidx 0x18#5, LeanRV64DExecutable.regidx.Regidx 0x0e#5, LeanRV64DExecutable.regidx.Regidx 0x0e#5, LeanRV64DExecutable.rop.ADD)) σ := by
  simp only [ext_decode, encdec_backwards, EStateM.run, bind, EStateM.bind,
    pure, EStateM.pure, PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
    currentlyEnabled, hartSupports, get_xLPE, Vsa.Sim.initMisa,
    _hmisa, hpriv, hsec]
  rfl

theorem decode_01872703
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x01872703#32).run σ =
      .ok (LeanRV64DExecutable.instruction.LOAD (0x018#12, LeanRV64DExecutable.regidx.Regidx 0x0e#5, LeanRV64DExecutable.regidx.Regidx 0x0e#5, false, 4)) σ := by
  simp only [ext_decode, encdec_backwards, EStateM.run, bind, EStateM.bind,
    pure, EStateM.pure, PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
    currentlyEnabled, hartSupports, get_xLPE, Vsa.Sim.initMisa,
    _hmisa, hpriv, hsec]
  rfl

theorem decode_01873303
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x01873303#32).run σ =
      .ok (LeanRV64DExecutable.instruction.LOAD (0x018#12, LeanRV64DExecutable.regidx.Regidx 0x0e#5, LeanRV64DExecutable.regidx.Regidx 0x06#5, false, 8)) σ := by
  simp only [ext_decode, encdec_backwards, EStateM.run, bind, EStateM.bind,
    pure, EStateM.pure, PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
    currentlyEnabled, hartSupports, get_xLPE, Vsa.Sim.initMisa,
    _hmisa, hpriv, hsec]
  rfl

theorem decode_01873783
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x01873783#32).run σ =
      .ok (LeanRV64DExecutable.instruction.LOAD (0x018#12, LeanRV64DExecutable.regidx.Regidx 0x0e#5, LeanRV64DExecutable.regidx.Regidx 0x0f#5, false, 8)) σ := by
  simp only [ext_decode, encdec_backwards, EStateM.run, bind, EStateM.bind,
    pure, EStateM.pure, PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
    currentlyEnabled, hartSupports, get_xLPE, Vsa.Sim.initMisa,
    _hmisa, hpriv, hsec]
  rfl

theorem decode_018787bb
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x018787bb#32).run σ =
      .ok (LeanRV64DExecutable.instruction.RTYPEW (LeanRV64DExecutable.regidx.Regidx 0x18#5, LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.ropw.ADDW)) σ := by
  simp only [ext_decode, encdec_backwards, EStateM.run, bind, EStateM.bind,
    pure, EStateM.pure, PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
    currentlyEnabled, hartSupports, get_xLPE, Vsa.Sim.initMisa,
    _hmisa, hpriv, hsec]
  rfl

theorem decode_0187b503
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x0187b503#32).run σ =
      .ok (LeanRV64DExecutable.instruction.LOAD (0x018#12, LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.regidx.Regidx 0x0a#5, false, 8)) σ := by
  simp only [ext_decode, encdec_backwards, EStateM.run, bind, EStateM.bind,
    pure, EStateM.pure, PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
    currentlyEnabled, hartSupports, get_xLPE, Vsa.Sim.initMisa,
    _hmisa, hpriv, hsec]
  rfl

theorem decode_0187b583
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x0187b583#32).run σ =
      .ok (LeanRV64DExecutable.instruction.LOAD (0x018#12, LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.regidx.Regidx 0x0b#5, false, 8)) σ := by
  simp only [ext_decode, encdec_backwards, EStateM.run, bind, EStateM.bind,
    pure, EStateM.pure, PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
    currentlyEnabled, hartSupports, get_xLPE, Vsa.Sim.initMisa,
    _hmisa, hpriv, hsec]
  rfl

theorem decode_0187b603
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x0187b603#32).run σ =
      .ok (LeanRV64DExecutable.instruction.LOAD (0x018#12, LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.regidx.Regidx 0x0c#5, false, 8)) σ := by
  simp only [ext_decode, encdec_backwards, EStateM.run, bind, EStateM.bind,
    pure, EStateM.pure, PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
    currentlyEnabled, hartSupports, get_xLPE, Vsa.Sim.initMisa,
    _hmisa, hpriv, hsec]
  rfl

end Vsa.Sim.DecodeTable
