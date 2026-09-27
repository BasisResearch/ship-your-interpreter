import Vsa.Sim.MemcpySpec
import Vsa.Sim.DecodeTable.Batch01Part10
import Vsa.Sim.DecodeTable.Batch08Part12
import Vsa.Sim.DecodeTable.Batch15Part28
import Vsa.Sim.DecodeTable.Batch15Part32
import Vsa.Sim.DivLoops

/-!
# `RegPins` — list-driven register-frame transport

Every Layer-3 composition currently threads each tracked register through each
step by hand: one `obs_*_other … (by decide) ×8` line per register per site
(O(sites × registers) `have`s — the single largest boilerplate term in the spec
files).  This file collapses that to **one line per site**: bundle the tracked
registers as a `List Pin`, and transport the whole bundle with `pins_alu` /
`pins_store` / `pins_btaken` / `pins_bnottaken` / `pins_jr` / `pins_jal`.

Usage pattern inside a composition:

```lean
-- entry: pins from the precondition
have hp0 : PinsHold c.σ [⟨Register.x10, dst⟩, ⟨Register.x1, r⟩, ⟨Register.x2, vsp⟩] :=
  ⟨ha0, hra, hsp⟩
-- after an ALU step writing rd (rd ∉ pins):
have hp1 := pins_alu hobs1 (by rfl) hp0
-- after a store / branch / jr:
have hp2 := pins_store hobs2 (by rfl) hp1
-- extract when needed (positional):
-- hp2.1 : σ2.regs.get? Register.x10 = some dst
-- hp2.2.1 : σ2.regs.get? Register.x1 = some r
```

The `by rfl` closes the side condition `pinsAvoid S L = true` (`S` = the
step's write-set: `rd :: noiseRegs` for ALU/JAL, `noiseRegs` for the rest);
it reduces by kernel evaluation because only the *registers* of the pins are
inspected, never the (symbolic) values.  NB it must be `rfl`, not `decide`:
the pin list contains free variables (the values), which `decide` rejects
even though they are never consulted.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)

namespace Vsa.Sim

/-- One tracked register pin: a register and the value it must read. -/
abbrev Pin := (R : Register) × RegisterType R

/-- All pins hold in `σ`. -/
def PinsHold (σ : MState) : List Pin → Prop
  | [] => True
  | p :: rest => σ.regs.get? p.1 = some p.2 ∧ PinsHold σ rest

@[simp] theorem pinsHold_nil (σ : MState) : PinsHold σ [] := trivial

@[simp] theorem pinsHold_cons (σ : MState) (p : Pin) (L : List Pin) :
    PinsHold σ (p :: L) ↔ (σ.regs.get? p.1 = some p.2 ∧ PinsHold σ L) := Iff.rfl

/-- The per-step noise write-set common to every instruction class. -/
def noiseRegs : List Register :=
  [Register.minstret, Register.PC, Register.nextPC, Register.minstret_increment,
   Register.mcycle, Register.mtime, Register.mip]

theorem all_notin {S : List Register} {R : Register}
    (h : (S.all fun r => !(r == R)) = true) : ∀ r ∈ S, (r == R) = false := by
  intro r hr
  have := List.all_eq_true.mp h r hr
  simpa using this

end Vsa.Sim
