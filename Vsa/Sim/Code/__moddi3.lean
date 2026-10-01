import Vsa.Elf

open Std (ExtHashMap)

namespace Vsa.Sim.Code

def __moddi3Chunk0 (mem : ExtHashMap Nat (BitVec 8)) : Prop :=
  mem[(0x80004728 : Nat)]? = some (0x93 : BitVec 8) ∧
  mem[(0x80004729 : Nat)]? = some (0x82 : BitVec 8) ∧
  mem[(0x8000472a : Nat)]? = some (0x00 : BitVec 8) ∧
  mem[(0x8000472b : Nat)]? = some (0x00 : BitVec 8) ∧
  mem[(0x8000472c : Nat)]? = some (0x63 : BitVec 8) ∧
  mem[(0x8000472d : Nat)]? = some (0xca : BitVec 8) ∧
  mem[(0x8000472e : Nat)]? = some (0x05 : BitVec 8) ∧
  mem[(0x8000472f : Nat)]? = some (0x00 : BitVec 8) ∧
  mem[(0x80004730 : Nat)]? = some (0x63 : BitVec 8) ∧
  mem[(0x80004731 : Nat)]? = some (0x4c : BitVec 8) ∧
  mem[(0x80004732 : Nat)]? = some (0x05 : BitVec 8) ∧
  mem[(0x80004733 : Nat)]? = some (0x00 : BitVec 8) ∧
  mem[(0x80004734 : Nat)]? = some (0xef : BitVec 8) ∧
  mem[(0x80004735 : Nat)]? = some (0xf0 : BitVec 8) ∧
  mem[(0x80004736 : Nat)]? = some (0x9f : BitVec 8) ∧
  mem[(0x80004737 : Nat)]? = some (0xf7 : BitVec 8) ∧
  mem[(0x80004738 : Nat)]? = some (0x13 : BitVec 8) ∧
  mem[(0x80004739 : Nat)]? = some (0x85 : BitVec 8) ∧
  mem[(0x8000473a : Nat)]? = some (0x05 : BitVec 8) ∧
  mem[(0x8000473b : Nat)]? = some (0x00 : BitVec 8) ∧
  mem[(0x8000473c : Nat)]? = some (0x67 : BitVec 8) ∧
  mem[(0x8000473d : Nat)]? = some (0x80 : BitVec 8) ∧
  mem[(0x8000473e : Nat)]? = some (0x02 : BitVec 8) ∧
  mem[(0x8000473f : Nat)]? = some (0x00 : BitVec 8) ∧
  mem[(0x80004740 : Nat)]? = some (0xb3 : BitVec 8) ∧
  mem[(0x80004741 : Nat)]? = some (0x05 : BitVec 8) ∧
  mem[(0x80004742 : Nat)]? = some (0xb0 : BitVec 8) ∧
  mem[(0x80004743 : Nat)]? = some (0x40 : BitVec 8) ∧
  mem[(0x80004744 : Nat)]? = some (0xe3 : BitVec 8) ∧
  mem[(0x80004745 : Nat)]? = some (0x58 : BitVec 8) ∧
  mem[(0x80004746 : Nat)]? = some (0x05 : BitVec 8) ∧
  mem[(0x80004747 : Nat)]? = some (0xfe : BitVec 8) ∧
  mem[(0x80004748 : Nat)]? = some (0x33 : BitVec 8) ∧
  mem[(0x80004749 : Nat)]? = some (0x05 : BitVec 8) ∧
  mem[(0x8000474a : Nat)]? = some (0xa0 : BitVec 8) ∧
  mem[(0x8000474b : Nat)]? = some (0x40 : BitVec 8) ∧
  mem[(0x8000474c : Nat)]? = some (0xef : BitVec 8) ∧
  mem[(0x8000474d : Nat)]? = some (0xf0 : BitVec 8) ∧
  mem[(0x8000474e : Nat)]? = some (0x1f : BitVec 8) ∧
  mem[(0x8000474f : Nat)]? = some (0xf6 : BitVec 8) ∧
  mem[(0x80004750 : Nat)]? = some (0x33 : BitVec 8) ∧
  mem[(0x80004751 : Nat)]? = some (0x05 : BitVec 8) ∧
  mem[(0x80004752 : Nat)]? = some (0xb0 : BitVec 8) ∧
  mem[(0x80004753 : Nat)]? = some (0x40 : BitVec 8) ∧
  mem[(0x80004754 : Nat)]? = some (0x67 : BitVec 8) ∧
  mem[(0x80004755 : Nat)]? = some (0x80 : BitVec 8) ∧
  mem[(0x80004756 : Nat)]? = some (0x02 : BitVec 8) ∧
  mem[(0x80004757 : Nat)]? = some (0x00 : BitVec 8) ∧
  mem[(0x80004758 : Nat)]? = some (0x93 : BitVec 8) ∧
  mem[(0x80004759 : Nat)]? = some (0x92 : BitVec 8) ∧
  mem[(0x8000475a : Nat)]? = some (0xf2 : BitVec 8) ∧
  mem[(0x8000475b : Nat)]? = some (0x01 : BitVec 8) ∧
  mem[(0x8000475c : Nat)]? = some (0xe3 : BitVec 8) ∧
  mem[(0x8000475d : Nat)]? = some (0x14 : BitVec 8) ∧
  mem[(0x8000475e : Nat)]? = some (0x55 : BitVec 8) ∧
  mem[(0x8000475f : Nat)]? = some (0xf4 : BitVec 8) ∧
  mem[(0x80004760 : Nat)]? = some (0x67 : BitVec 8) ∧
  mem[(0x80004761 : Nat)]? = some (0x80 : BitVec 8) ∧
  mem[(0x80004762 : Nat)]? = some (0x00 : BitVec 8) ∧
  mem[(0x80004763 : Nat)]? = some (0x00 : BitVec 8)

def __moddi3Loaded (mem : ExtHashMap Nat (BitVec 8)) : Prop :=
  __moddi3Chunk0 mem

theorem __moddi3_chunk0 {mem : ExtHashMap Nat (BitVec 8)}
    (h : __moddi3Loaded mem) : __moddi3Chunk0 mem := h

theorem __moddi3_at_80004734 {mem : ExtHashMap Nat (BitVec 8)}
    (h : __moddi3Loaded mem) :
      mem[(0x80004734 : Nat)]? = some (0xef : BitVec 8) ∧
      mem[(0x80004735 : Nat)]? = some (0xf0 : BitVec 8) ∧
      mem[(0x80004736 : Nat)]? = some (0x9f : BitVec 8) ∧
      mem[(0x80004737 : Nat)]? = some (0xf7 : BitVec 8) :=
  have hc := __moddi3_chunk0 h
  ⟨hc.2.2.2.2.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem __moddi3_at_8000474c {mem : ExtHashMap Nat (BitVec 8)}
    (h : __moddi3Loaded mem) :
      mem[(0x8000474c : Nat)]? = some (0xef : BitVec 8) ∧
      mem[(0x8000474d : Nat)]? = some (0xf0 : BitVec 8) ∧
      mem[(0x8000474e : Nat)]? = some (0x1f : BitVec 8) ∧
      mem[(0x8000474f : Nat)]? = some (0xf6 : BitVec 8) :=
  have hc := __moddi3_chunk0 h
  ⟨hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

end Vsa.Sim.Code
