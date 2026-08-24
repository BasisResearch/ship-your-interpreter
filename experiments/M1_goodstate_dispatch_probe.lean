import Vsa.Sim.GoodState
import Vsa.Sim.Dispatch

/-! Probe: GoodState fields discharge dispatch_none's hypotheses
(this is the composition the try_step skeleton will perform). -/

open LeanRV64DExecutable Sail ConcurrencyInterfaceV1 Vsa Vsa.Sim

example (σ : Vsa.Machine.MState) (hG : GoodState σ) :
    (LeanRV64DExecutable.Functions.dispatchInterrupt Privilege.Machine).run σ = .ok none σ := by
  obtain ⟨vmip, hmip⟩ := hG.mip
  obtain ⟨vmeip, hmeip⟩ := hG.sig_meip
  obtain ⟨vseip, hseip⟩ := hG.sig_seip
  exact dispatch_none σ vmip vmeip vseip 0#64 initMstatus hG.misa hG.mie hmip hmeip hseip
    hG.mideleg hG.mstatus
