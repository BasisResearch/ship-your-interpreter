import Vsa.Sim.SharedReadGeometry
import Vsa.Sim.RuntimeOwnership

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

namespace Vsa.Sim
open RuntimeOwnership

/-- The ELF initializer's print-name pointer refutes above-image payload geometry. -/
theorem native_print_above_image_impossible
    {m : Mem} {shared : Nat → Prop} {SL : StackLayout} {slot : Nat}
    (ho : ValueOwned m shared slot (.native .print))
    (hp : read64 m (slot + 8) = some 0x80019538)
    (hg : SharedGeom shared SL) : False := by
  obtain ⟨p, hread, hs⟩ := ho
  have heq : p = 0x80019538 := Option.some.inj (hread.symm.trans hp)
  subst p
  have hbyte := hs.bytes 0 (Nat.zero_le _)
  have := hg.ram _ hbyte
  omega

/-- Literal bytes, including NUL, used by the real three native initial values. -/
def nativeNamesByte (k : Nat) : Prop :=
  (0x80019538 ≤ k ∧ k ≤ 0x8001953d) ∨
  (0x80019540 ≤ k ∧ k ≤ 0x80019547) ∨
  (0x80019548 ≤ k ∧ k ≤ 0x8001954e)

theorem native_names_read_geometry {SL : StackLayout}
    (hstack : tohostAddr + 16 ≤ SL.lo) : SharedReadGeom nativeNamesByte SL where
  ram := fun k hk => by unfold nativeNamesByte at hk; omega
  code := fun k hk => by unfold nativeNamesByte at hk; omega
  htif := fun k hk => by
    unfold nativeNamesByte at hk
    have ht : tohostAddr = 0x8001ad00 := rfl
    omega
  stack := fun k hk => by
    unfold nativeNamesByte at hk
    have ht : tohostAddr = 0x8001ad00 := rfl
    omega

#print axioms native_print_above_image_impossible
#print axioms native_names_read_geometry

end Vsa.Sim
