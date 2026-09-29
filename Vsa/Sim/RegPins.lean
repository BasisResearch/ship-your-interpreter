import Vsa.Sim.MemcpySpec
import Vsa.Sim.DecodeNF
import Vsa.Sim.DivLoops

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)

namespace Vsa.Sim

abbrev Pin := (R : Register) × RegisterType R

def PinsHold (σ : MState) : List Pin → Prop
  | [] => True
  | p :: rest => σ.regs.get? p.1 = some p.2 ∧ PinsHold σ rest

@[simp] theorem pinsHold_nil (σ : MState) : PinsHold σ [] := trivial

@[simp] theorem pinsHold_cons (σ : MState) (p : Pin) (L : List Pin) :
    PinsHold σ (p :: L) ↔ (σ.regs.get? p.1 = some p.2 ∧ PinsHold σ L) := Iff.rfl

def noiseRegs : List Register :=
  [Register.minstret, Register.PC, Register.nextPC, Register.minstret_increment,
   Register.mcycle, Register.mtime, Register.mip]

theorem all_notin {S : List Register} {R : Register}
    (h : (S.all fun r => !(r == R)) = true) : ∀ r ∈ S, (r == R) = false := by
  intro r hr
  have := List.all_eq_true.mp h r hr
  simpa using this

end Vsa.Sim
