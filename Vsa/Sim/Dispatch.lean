import Vsa.Elf
import Vsa.Sim.InitValues

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

theorem Vsa.Sim.dispatch_none
    (σ : SequentialState RegisterType trivialChoiceSource)
    (vmip : RegisterType Register.mip)
    (vmeip : RegisterType Register.sig_meip)
    (vseip : RegisterType Register.sig_seip)
    (vmideleg : RegisterType Register.mideleg)
    (vmstatus : RegisterType Register.mstatus)
    (hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hmie : σ.regs.get? Register.mie =
      some ((BitVec.zero 64) : RegisterType Register.mie))
    (hmip : σ.regs.get? Register.mip = some vmip)
    (hmeip : σ.regs.get? Register.sig_meip = some vmeip)
    (hseip : σ.regs.get? Register.sig_seip = some vseip)
    (hmideleg : σ.regs.get? Register.mideleg = some vmideleg)
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus) :
    (dispatchInterrupt Privilege.Machine).run σ = .ok none σ := by
  simp only [dispatchInterrupt, getPendingSet, read_mip, external_interrupts_pending]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    readReg, _get_Misa_S, Vsa.Sim.initMisa, findPendingInterrupt]

  have hz : (0#64 : BitVec 64) = zeros (n := 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  simp [hz, EStateM.pure, and_false]
