import Vsa.Sim.RegPins

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)

namespace Vsa.Sim

def KeepRegs (Rs : List Register) (σ0 σ' : MState) : Prop :=
  ∀ R ∈ Rs, ∀ w : RegisterType R, σ0.regs.get? R = some w → σ'.regs.get? R = some w

end Vsa.Sim
