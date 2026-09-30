import Vsa.Elf

open Std (ExtHashMap)

namespace Vsa.Sim.Code

def value_boolChunk0 (mem : ExtHashMap Nat (BitVec 8)) : Prop :=
  mem[(0x800027f8 : Nat)]? = some (0xb3 : BitVec 8) ∧
  mem[(0x800027f9 : Nat)]? = some (0x35 : BitVec 8) ∧
  mem[(0x800027fa : Nat)]? = some (0xb0 : BitVec 8) ∧
  mem[(0x800027fb : Nat)]? = some (0x00 : BitVec 8) ∧
  mem[(0x800027fc : Nat)]? = some (0x93 : BitVec 8) ∧
  mem[(0x800027fd : Nat)]? = some (0x07 : BitVec 8) ∧
  mem[(0x800027fe : Nat)]? = some (0x10 : BitVec 8) ∧
  mem[(0x800027ff : Nat)]? = some (0x00 : BitVec 8) ∧
  mem[(0x80002800 : Nat)]? = some (0x23 : BitVec 8) ∧
  mem[(0x80002801 : Nat)]? = some (0x24 : BitVec 8) ∧
  mem[(0x80002802 : Nat)]? = some (0xb5 : BitVec 8) ∧
  mem[(0x80002803 : Nat)]? = some (0x00 : BitVec 8) ∧
  mem[(0x80002804 : Nat)]? = some (0x23 : BitVec 8) ∧
  mem[(0x80002805 : Nat)]? = some (0x20 : BitVec 8) ∧
  mem[(0x80002806 : Nat)]? = some (0xf5 : BitVec 8) ∧
  mem[(0x80002807 : Nat)]? = some (0x00 : BitVec 8) ∧
  mem[(0x80002808 : Nat)]? = some (0x67 : BitVec 8) ∧
  mem[(0x80002809 : Nat)]? = some (0x80 : BitVec 8) ∧
  mem[(0x8000280a : Nat)]? = some (0x00 : BitVec 8) ∧
  mem[(0x8000280b : Nat)]? = some (0x00 : BitVec 8)

def Value_boolLoaded (mem : ExtHashMap Nat (BitVec 8)) : Prop :=
  value_boolChunk0 mem

end Vsa.Sim.Code
