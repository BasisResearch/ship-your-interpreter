import Vsa.Elf

open Std (ExtHashMap)

namespace Vsa.Sim.Code

def value_intChunk0 (mem : ExtHashMap Nat (BitVec 8)) : Prop :=
  mem[(0x8000280c : Nat)]? = some (0x93 : BitVec 8) ∧
  mem[(0x8000280d : Nat)]? = some (0x07 : BitVec 8) ∧
  mem[(0x8000280e : Nat)]? = some (0x20 : BitVec 8) ∧
  mem[(0x8000280f : Nat)]? = some (0x00 : BitVec 8) ∧
  mem[(0x80002810 : Nat)]? = some (0x23 : BitVec 8) ∧
  mem[(0x80002811 : Nat)]? = some (0x34 : BitVec 8) ∧
  mem[(0x80002812 : Nat)]? = some (0xb5 : BitVec 8) ∧
  mem[(0x80002813 : Nat)]? = some (0x00 : BitVec 8) ∧
  mem[(0x80002814 : Nat)]? = some (0x23 : BitVec 8) ∧
  mem[(0x80002815 : Nat)]? = some (0x20 : BitVec 8) ∧
  mem[(0x80002816 : Nat)]? = some (0xf5 : BitVec 8) ∧
  mem[(0x80002817 : Nat)]? = some (0x00 : BitVec 8) ∧
  mem[(0x80002818 : Nat)]? = some (0x67 : BitVec 8) ∧
  mem[(0x80002819 : Nat)]? = some (0x80 : BitVec 8) ∧
  mem[(0x8000281a : Nat)]? = some (0x00 : BitVec 8) ∧
  mem[(0x8000281b : Nat)]? = some (0x00 : BitVec 8)

def Value_intLoaded (mem : ExtHashMap Nat (BitVec 8)) : Prop :=
  value_intChunk0 mem

end Vsa.Sim.Code
