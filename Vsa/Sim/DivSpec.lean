import Vsa.Sim.DivSites
import Vsa.Sim.Muldi3Spec
import Vsa.Triple

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

abbrev NotWritten (R : Register) : Prop :=
  (Register.x10 == R) = false ∧ (Register.x11 == R) = false ∧
  (Register.x12 == R) = false ∧ (Register.x13 == R) = false ∧
  (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
  (Register.minstret == R) = false ∧ (Register.minstret_increment == R) = false ∧
  (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
  (Register.mip == R) = false

abbrev Frame (g : (R : Register) → Option (RegisterType R)) (c : Config) : Prop :=
  ∀ R : Register, NotWritten R → c.σ.regs.get? R = g R

theorem NotWritten.x10 {R : Register} (h : NotWritten R) : (Register.x10 == R) = false := h.1
theorem NotWritten.x11 {R : Register} (h : NotWritten R) : (Register.x11 == R) = false := h.2.1
theorem NotWritten.x13 {R : Register} (h : NotWritten R) : (Register.x13 == R) = false := h.2.2.2.1

end Vsa.Sim
