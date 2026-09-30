import Vsa.Sim.Boot.Store
import Vsa.Densify

namespace Vsa.Sim.Boot

open Vsa.MemRepr Vsa.Densify

theorem fillZero_bootConfig (m : Mem) (g : Nat → BitVec 64) (steps : Nat) :
    fillZero (bootConfig m g steps) = bootConfig (fillZeroMem m) g steps := rfl

theorem PartialView.fill {m : Mem} {v : Nat → Option (BitVec 8)} (h : PartialView m v) :
    PartialView (fillZeroMem m) v :=
  fun k b hk => fillZeroMem_some (h k b hk)

theorem fillZeroMem_stack (m : Mem) :
    ∀ k, LayoutInstance.stackSL.lo ≤ k → k < LayoutInstance.stackSL.hi →
      ∃ b : BitVec 8, (fillZeroMem m)[k]? = some b := by
  intro k hlo hhi
  have hl : LayoutInstance.stackSL.lo = 0x87800000 := rfl
  have hh : LayoutInstance.stackSL.hi = 0x88000000 := rfl
  rw [hl] at hlo; rw [hh] at hhi
  exact ⟨_, fillZeroMem_ram m (by unfold ramBase; omega) (by unfold ramBase ramSize; omega)⟩

end Vsa.Sim.Boot
