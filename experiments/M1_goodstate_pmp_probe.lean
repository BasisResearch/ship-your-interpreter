import Vsa.Sim.GoodState
import Vsa.Sim.Pmp

/-! Probe: GoodState fields discharge pmp_allows' hypotheses. -/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa Vsa.Sim

example (σ : Vsa.Machine.MState) (hG : GoodState σ) (a : physaddr) (w : Nat)
    (acc : MemoryAccessType mem_payload) :
    (pmpCheck a w acc Privilege.Machine).run σ = .ok none σ :=
  pmp_allows σ a w acc initPmpaddr hG.pmpcfg_n hG.pmpaddr_n
