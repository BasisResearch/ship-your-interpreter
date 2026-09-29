import Vsa.Meta.SimpNF
import Vsa.Sim.InitValues

/-!
# The Sail decoder, partially evaluated once

`decodeN w σ` is the `simp` normal form of `(ext_decode w).run σ` with the three
registers the decoder reads (`misa`, `cur_privilege`, `mseccfg`) pinned to their
machine-mode values. `decodeW` turns it into the decode fact for any concrete
word: the instruction is found by `rfl`, which reduces `decodeN` along the branch
the word selects.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register

namespace Vsa.Sim

set_option linter.unusedVariables false in
#simp_nf decodeN (w : BitVec 32) (σ : SequentialState RegisterType trivialChoiceSource)
    (hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode w).run σ
  using [ext_decode, encdec_backwards, EStateM.run, bind, EStateM.bind,
    pure, EStateM.pure, PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
    currentlyEnabled, hartSupports, get_xLPE, Vsa.Sim.initMisa, hmisa, hpriv, hsec]

/-- The decode fact for a concrete word `w`: `i` is computed by `rfl`. -/
theorem decodeW {w : BitVec 32} {i : instruction}
    (σ : SequentialState RegisterType trivialChoiceSource)
    (hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg))
    (hnf : decodeN w σ = .ok i σ := by rfl) :
    (ext_decode w).run σ = .ok i σ :=
  (decodeN.eq w σ hmisa hpriv hsec).trans hnf

end Vsa.Sim
