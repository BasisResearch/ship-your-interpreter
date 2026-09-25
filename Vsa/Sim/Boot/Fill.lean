import Vsa.Sim.Boot.Store
import Vsa.Densify

/-!
# The zero fill of a boot state (REVIEW.md P3, lane B2)

`endToEnd_refinement` takes `Loaded interpRunLayout p (fillZero c)` and
concludes about `c`. The fill only changes the memory, so the fill of a boot
configuration is the boot configuration over the filled memory; every byte
the entry view returns survives the fill; and every stack byte is present in
it.
-/

namespace Vsa.Sim.Boot

open Vsa.MemRepr Vsa.Densify

theorem fillZero_bootConfig (m : Mem) (g : Nat → BitVec 64) (steps : Nat) :
    fillZero (bootConfig m g steps) = bootConfig (fillZeroMem m) g steps := rfl

theorem PartialView.fill {m : Mem} {v : Nat → Option (BitVec 8)} (h : PartialView m v) :
    PartialView (fillZeroMem m) v :=
  fun k b hk => fillZeroMem_some (h k b hk)

/-- Every stack byte of a filled memory is present. -/
theorem fillZeroMem_stack (m : Mem) :
    ∀ k, LayoutInstance.stackSL.lo ≤ k → k < LayoutInstance.stackSL.hi →
      ∃ b : BitVec 8, (fillZeroMem m)[k]? = some b := by
  intro k hlo hhi
  have hl : LayoutInstance.stackSL.lo = 0x87800000 := rfl
  have hh : LayoutInstance.stackSL.hi = 0x88000000 := rfl
  rw [hl] at hlo; rw [hh] at hhi
  exact ⟨_, fillZeroMem_ram m (by unfold ramBase; omega) (by unfold ramBase ramSize; omega)⟩

end Vsa.Sim.Boot
