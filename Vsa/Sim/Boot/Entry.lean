import Vsa.Sim.Boot.Config
import Vsa.Densify.Transport

/-!
# The entry register file a boot witness needs (REVIEW2.md P8)

`Loaded interpRunLayout` inspects the register file through exactly four
facts: `GoodState` (the pinned control registers and the presence of the
counters), `PC = interp_run`, `htif_payload_writes = 0`, and the values of
`x1 … x31`. `EntryRegs σ g` names them, so a boot witness can be stated at
ANY configuration whose registers satisfy them — in particular at the state
the binary reaches, whose counters (`mtime`, `mcycle`, `minstret`, `mip`,
`htif_tohost`) differ from the model's setup values that `bootState` carries.
`bootState_entryRegs` is the instance at `bootState`; `EntryRegs.setMem`
transports the facts across a memory change (the zero fill).
-/

namespace Vsa.Sim.Boot

open LeanRV64DExecutable Sail ConcurrencyInterfaceV1 Vsa.Machine Vsa.Sim

/-- The register facts `Loaded` reads at `interp_run`'s entry, over the traced
general registers `g` (`x0` and unlisted indices read `0`). -/
structure EntryRegs (σ : MState) (g : Nat → BitVec 64) : Prop where
  good : GoodState σ
  pc : σ.regs.get? Register.PC = some (0x800043ec#64)
  payload : σ.regs.get? Register.htif_payload_writes = some (0#4)
  gpr : ∀ i, i < 31 → σ.regs.get? (gprReg (i + 1)) = some (gprRT (i + 1) (g (i + 1)))

/-- `GoodState` reads only the register file. -/
theorem _root_.Vsa.Sim.GoodState.setMem {σ : MState} (h : GoodState σ) (m : Vsa.MemRepr.Mem) :
    GoodState { σ with mem := m } := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _⟩ := h
  constructor <;> assumption

theorem EntryRegs.setMem {σ : MState} {g : Nat → BitVec 64} (E : EntryRegs σ g)
    (m : Vsa.MemRepr.Mem) : EntryRegs { σ with mem := m } g :=
  ⟨E.good.setMem m, E.pc, E.payload, E.gpr⟩

/-- The console output reads only the output field. -/
theorem output_setMem (σ : MState) (m : Vsa.MemRepr.Mem) :
    Vsa.Machine.output { σ with mem := m } = Vsa.Machine.output σ := rfl

/-- Every general register is present. -/
theorem EntryRegs.gprs {σ : MState} {g : Nat → BitVec 64} (E : EntryRegs σ g) :
    ∀ n, 1 ≤ n → n ≤ 31 → (gprGet σ n).isSome := by
  intro n h1 h31
  obtain ⟨i, rfl⟩ : ∃ i, n = i + 1 := ⟨n - 1, by omega⟩
  have hi : i < 31 := by omega
  have hg := E.gpr
  exact match i, hi with
  | 0, _ => by
    show (σ.regs.get? Register.x1).isSome = true
    rw [show σ.regs.get? Register.x1 = some (g 1) from hg 0 (by decide)]; rfl
  | 1, _ => by
    show (σ.regs.get? Register.x2).isSome = true
    rw [show σ.regs.get? Register.x2 = some (g 2) from hg 1 (by decide)]; rfl
  | 2, _ => by
    show (σ.regs.get? Register.x3).isSome = true
    rw [show σ.regs.get? Register.x3 = some (g 3) from hg 2 (by decide)]; rfl
  | 3, _ => by
    show (σ.regs.get? Register.x4).isSome = true
    rw [show σ.regs.get? Register.x4 = some (g 4) from hg 3 (by decide)]; rfl
  | 4, _ => by
    show (σ.regs.get? Register.x5).isSome = true
    rw [show σ.regs.get? Register.x5 = some (g 5) from hg 4 (by decide)]; rfl
  | 5, _ => by
    show (σ.regs.get? Register.x6).isSome = true
    rw [show σ.regs.get? Register.x6 = some (g 6) from hg 5 (by decide)]; rfl
  | 6, _ => by
    show (σ.regs.get? Register.x7).isSome = true
    rw [show σ.regs.get? Register.x7 = some (g 7) from hg 6 (by decide)]; rfl
  | 7, _ => by
    show (σ.regs.get? Register.x8).isSome = true
    rw [show σ.regs.get? Register.x8 = some (g 8) from hg 7 (by decide)]; rfl
  | 8, _ => by
    show (σ.regs.get? Register.x9).isSome = true
    rw [show σ.regs.get? Register.x9 = some (g 9) from hg 8 (by decide)]; rfl
  | 9, _ => by
    show (σ.regs.get? Register.x10).isSome = true
    rw [show σ.regs.get? Register.x10 = some (g 10) from hg 9 (by decide)]; rfl
  | 10, _ => by
    show (σ.regs.get? Register.x11).isSome = true
    rw [show σ.regs.get? Register.x11 = some (g 11) from hg 10 (by decide)]; rfl
  | 11, _ => by
    show (σ.regs.get? Register.x12).isSome = true
    rw [show σ.regs.get? Register.x12 = some (g 12) from hg 11 (by decide)]; rfl
  | 12, _ => by
    show (σ.regs.get? Register.x13).isSome = true
    rw [show σ.regs.get? Register.x13 = some (g 13) from hg 12 (by decide)]; rfl
  | 13, _ => by
    show (σ.regs.get? Register.x14).isSome = true
    rw [show σ.regs.get? Register.x14 = some (g 14) from hg 13 (by decide)]; rfl
  | 14, _ => by
    show (σ.regs.get? Register.x15).isSome = true
    rw [show σ.regs.get? Register.x15 = some (g 15) from hg 14 (by decide)]; rfl
  | 15, _ => by
    show (σ.regs.get? Register.x16).isSome = true
    rw [show σ.regs.get? Register.x16 = some (g 16) from hg 15 (by decide)]; rfl
  | 16, _ => by
    show (σ.regs.get? Register.x17).isSome = true
    rw [show σ.regs.get? Register.x17 = some (g 17) from hg 16 (by decide)]; rfl
  | 17, _ => by
    show (σ.regs.get? Register.x18).isSome = true
    rw [show σ.regs.get? Register.x18 = some (g 18) from hg 17 (by decide)]; rfl
  | 18, _ => by
    show (σ.regs.get? Register.x19).isSome = true
    rw [show σ.regs.get? Register.x19 = some (g 19) from hg 18 (by decide)]; rfl
  | 19, _ => by
    show (σ.regs.get? Register.x20).isSome = true
    rw [show σ.regs.get? Register.x20 = some (g 20) from hg 19 (by decide)]; rfl
  | 20, _ => by
    show (σ.regs.get? Register.x21).isSome = true
    rw [show σ.regs.get? Register.x21 = some (g 21) from hg 20 (by decide)]; rfl
  | 21, _ => by
    show (σ.regs.get? Register.x22).isSome = true
    rw [show σ.regs.get? Register.x22 = some (g 22) from hg 21 (by decide)]; rfl
  | 22, _ => by
    show (σ.regs.get? Register.x23).isSome = true
    rw [show σ.regs.get? Register.x23 = some (g 23) from hg 22 (by decide)]; rfl
  | 23, _ => by
    show (σ.regs.get? Register.x24).isSome = true
    rw [show σ.regs.get? Register.x24 = some (g 24) from hg 23 (by decide)]; rfl
  | 24, _ => by
    show (σ.regs.get? Register.x25).isSome = true
    rw [show σ.regs.get? Register.x25 = some (g 25) from hg 24 (by decide)]; rfl
  | 25, _ => by
    show (σ.regs.get? Register.x26).isSome = true
    rw [show σ.regs.get? Register.x26 = some (g 26) from hg 25 (by decide)]; rfl
  | 26, _ => by
    show (σ.regs.get? Register.x27).isSome = true
    rw [show σ.regs.get? Register.x27 = some (g 27) from hg 26 (by decide)]; rfl
  | 27, _ => by
    show (σ.regs.get? Register.x28).isSome = true
    rw [show σ.regs.get? Register.x28 = some (g 28) from hg 27 (by decide)]; rfl
  | 28, _ => by
    show (σ.regs.get? Register.x29).isSome = true
    rw [show σ.regs.get? Register.x29 = some (g 29) from hg 28 (by decide)]; rfl
  | 29, _ => by
    show (σ.regs.get? Register.x30).isSome = true
    rw [show σ.regs.get? Register.x30 = some (g 30) from hg 29 (by decide)]; rfl
  | 30, _ => by
    show (σ.regs.get? Register.x31).isSome = true
    rw [show σ.regs.get? Register.x31 = some (g 31) from hg 30 (by decide)]; rfl
  | _ + 31, h => absurd h (by omega)

/-- The witness register file (`Config.lean`) satisfies the entry facts. -/
theorem bootState_entryRegs (m : Vsa.MemRepr.Mem) (g : Nat → BitVec 64) :
    EntryRegs (bootState m g) g :=
  ⟨bootState_good m g, bootState_pc m g, bootState_htif_payload m g,
    fun i hi => bootRegs_gpr g i hi⟩

/-- The zero fill of a configuration, by its fields. -/
theorem fillZero_mk (σ : MState) (tick steps : Nat) :
    Vsa.Densify.fillZero ⟨σ, tick, steps⟩ = ⟨{ σ with mem := Vsa.Densify.fillZeroMem σ.mem }, tick, steps⟩ :=
  rfl

end Vsa.Sim.Boot
