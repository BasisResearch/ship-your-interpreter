import LeanRiscv
import Vsa.Sim.InitValues
import Vsa.Sim.DecodeTable.DecodeCommon

/-! Additive decode providers for the explicit output-alias trace.
ASTs were discovered using the actual decoder; each theorem below is checked
by the Lean kernel. No global decode table or index is modified. -/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register

namespace Vsa.Sim.OutputAliasDecode

theorem decode_72c0406f
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x72c0406f#32).run σ =
      .ok (LeanRV64DExecutable.instruction.JAL (0x00472c#21, LeanRV64DExecutable.regidx.Regidx 0x00#5)) σ := by
  simp only [ext_decode, encdec_backwards, EStateM.run, bind, EStateM.bind,
    pure, EStateM.pure, PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
    currentlyEnabled, hartSupports, get_xLPE, Vsa.Sim.initMisa,
    _hmisa, hpriv, hsec]
  rfl

end Vsa.Sim.OutputAliasDecode
