import Vsa.Elf

open Std (ExtHashMap)

namespace Vsa.Sim.Code

def value_strChunk0 (mem : ExtHashMap Nat (BitVec 8)) : Prop :=
  mem[(0x8000281c : Nat)]? = some (0x93 : BitVec 8) ∧
  mem[(0x8000281d : Nat)]? = some (0x07 : BitVec 8) ∧
  mem[(0x8000281e : Nat)]? = some (0x30 : BitVec 8) ∧
  mem[(0x8000281f : Nat)]? = some (0x00 : BitVec 8) ∧
  mem[(0x80002820 : Nat)]? = some (0x23 : BitVec 8) ∧
  mem[(0x80002821 : Nat)]? = some (0x34 : BitVec 8) ∧
  mem[(0x80002822 : Nat)]? = some (0xb5 : BitVec 8) ∧
  mem[(0x80002823 : Nat)]? = some (0x00 : BitVec 8) ∧
  mem[(0x80002824 : Nat)]? = some (0x23 : BitVec 8) ∧
  mem[(0x80002825 : Nat)]? = some (0x20 : BitVec 8) ∧
  mem[(0x80002826 : Nat)]? = some (0xf5 : BitVec 8) ∧
  mem[(0x80002827 : Nat)]? = some (0x00 : BitVec 8) ∧
  mem[(0x80002828 : Nat)]? = some (0x67 : BitVec 8) ∧
  mem[(0x80002829 : Nat)]? = some (0x80 : BitVec 8) ∧
  mem[(0x8000282a : Nat)]? = some (0x00 : BitVec 8) ∧
  mem[(0x8000282b : Nat)]? = some (0x00 : BitVec 8)

def Value_strLoaded (mem : ExtHashMap Nat (BitVec 8)) : Prop :=
  value_strChunk0 mem

end Vsa.Sim.Code
