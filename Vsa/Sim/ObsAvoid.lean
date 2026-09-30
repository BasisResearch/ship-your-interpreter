import Vsa.Sim.Muldi3Spec
import Vsa.Sim.StepJump
import Vsa.Sim.MemcpySpec
import Vsa.Sim.ValueSpec
import Vsa.Sim.ValueTruthySpec

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)

set_option maxHeartbeats 4000000

namespace Vsa.Sim

theorem obs_store_other' {σ' σ : MState} {pc vm : BitVec 64}
    {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m')) (R : Register) {w : RegisterType R}
    (hdis : (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
            (Register.mip == R) = false ∧ (Register.minstret == R) = false ∧
            (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
            (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w :=
  obs_store_other hobs R hdis.1 hdis.2.1 hdis.2.2.1 hdis.2.2.2.1 hdis.2.2.2.2.1
    hdis.2.2.2.2.2.1 hdis.2.2.2.2.2.2 hσ

end Vsa.Sim
