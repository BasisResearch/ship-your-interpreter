import Vsa.Elf

open Std (ExtHashMap)

namespace Vsa.Sim.Code

def __divdi3Chunk0 (mem : ExtHashMap Nat (BitVec 8)) : Prop :=
  mem[(0x800046a4 : Nat)]? = some (0x63 : BitVec 8) ∧
  mem[(0x800046a5 : Nat)]? = some (0x40 : BitVec 8) ∧
  mem[(0x800046a6 : Nat)]? = some (0x05 : BitVec 8) ∧
  mem[(0x800046a7 : Nat)]? = some (0x06 : BitVec 8) ∧
  mem[(0x800046a8 : Nat)]? = some (0x63 : BitVec 8) ∧
  mem[(0x800046a9 : Nat)]? = some (0xc6 : BitVec 8) ∧
  mem[(0x800046aa : Nat)]? = some (0x05 : BitVec 8) ∧
  mem[(0x800046ab : Nat)]? = some (0x06 : BitVec 8)

def __divdi3Loaded (mem : ExtHashMap Nat (BitVec 8)) : Prop :=
  __divdi3Chunk0 mem

theorem __divdi3_chunk0 {mem : ExtHashMap Nat (BitVec 8)}
    (h : __divdi3Loaded mem) : __divdi3Chunk0 mem := h

theorem __divdi3_at_800046a4 {mem : ExtHashMap Nat (BitVec 8)}
    (h : __divdi3Loaded mem) :
      mem[(0x800046a4 : Nat)]? = some (0x63 : BitVec 8) ∧
      mem[(0x800046a5 : Nat)]? = some (0x40 : BitVec 8) ∧
      mem[(0x800046a6 : Nat)]? = some (0x05 : BitVec 8) ∧
      mem[(0x800046a7 : Nat)]? = some (0x06 : BitVec 8) :=
  have hc := __divdi3_chunk0 h
  ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1⟩

theorem __divdi3_at_800046a8 {mem : ExtHashMap Nat (BitVec 8)}
    (h : __divdi3Loaded mem) :
      mem[(0x800046a8 : Nat)]? = some (0x63 : BitVec 8) ∧
      mem[(0x800046a9 : Nat)]? = some (0xc6 : BitVec 8) ∧
      mem[(0x800046aa : Nat)]? = some (0x05 : BitVec 8) ∧
      mem[(0x800046ab : Nat)]? = some (0x06 : BitVec 8) :=
  have hc := __divdi3_chunk0 h
  ⟨hc.2.2.2.2.1, hc.2.2.2.2.2.1, hc.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2⟩

end Vsa.Sim.Code
