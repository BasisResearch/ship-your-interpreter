import Vsa.Sim.Code.FixedImageData

open Std (ExtHashMap)

namespace Vsa.Sim.Code

/-- Byte equality on a bounded interval. Nothing is asserted outside it. -/
def FixedBytesLoaded (base size : Nat) (byte : Nat → BitVec 8)
    (mem : ExtHashMap Nat (BitVec 8)) : Prop :=
  ∀ offset, offset < size → mem[base + offset]? = some (byte offset)

/-- Exact .text bytes of the approved interpreter ELF. -/
def FixedTextLoaded (mem : ExtHashMap Nat (BitVec 8)) : Prop :=
  FixedBytesLoaded fixedTextBase fixedTextSize fixedTextByte mem

/-- Exact .rodata bytes; mutable .data/BSS are deliberately separate. -/
def FixedRodataLoaded (mem : ExtHashMap Nat (BitVec 8)) : Prop :=
  FixedBytesLoaded fixedRodataBase fixedRodataSize fixedRodataByte mem

theorem FixedBytesLoaded.transport
    {base size : Nat} {byte : Nat → BitVec 8}
    {mem mem' : ExtHashMap Nat (BitVec 8)}
    (h : FixedBytesLoaded base size byte mem)
    (hag : ∀ a, base ≤ a → a < base + size → mem'[a]? = mem[a]?) :
    FixedBytesLoaded base size byte mem' := by
  intro offset hoff
  exact (hag (base + offset) (Nat.le_add_right _ _)
    (Nat.add_lt_add_left hoff base)).trans (h offset hoff)

theorem FixedTextLoaded.transport
    {mem mem' : ExtHashMap Nat (BitVec 8)} (h : FixedTextLoaded mem)
    (hag : ∀ a, 0x80000000 ≤ a → a < 0x80018be0 → mem'[a]? = mem[a]?) :
    FixedTextLoaded mem' :=
  FixedBytesLoaded.transport h hag

theorem FixedRodataLoaded.transport
    {mem mem' : ExtHashMap Nat (BitVec 8)} (h : FixedRodataLoaded mem)
    (hag : ∀ a, 0x80018be0 ≤ a → a < 0x8001acf0 → mem'[a]? = mem[a]?) :
    FixedRodataLoaded mem' :=
  FixedBytesLoaded.transport h hag

#print axioms FixedBytesLoaded.transport
#print axioms FixedTextLoaded.transport
#print axioms FixedRodataLoaded.transport

end Vsa.Sim.Code
