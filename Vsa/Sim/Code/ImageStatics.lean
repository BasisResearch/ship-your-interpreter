import Vsa.Elf

open Std (ExtHashMap)

namespace Vsa.Sim.Code

def imgLldFmt (mem : ExtHashMap Nat (BitVec 8)) : Prop :=
  mem[(0x800192c0 : Nat)]? = some (0x25 : BitVec 8) ∧
  mem[(0x800192c1 : Nat)]? = some (0x6c : BitVec 8) ∧
  mem[(0x800192c2 : Nat)]? = some (0x6c : BitVec 8) ∧
  mem[(0x800192c3 : Nat)]? = some (0x64 : BitVec 8) ∧
  mem[(0x800192c4 : Nat)]? = some (0x00 : BitVec 8) ∧
  mem[(0x800192c5 : Nat)]? = some (0x00 : BitVec 8) ∧
  mem[(0x800192c6 : Nat)]? = some (0x00 : BitVec 8) ∧
  mem[(0x800192c7 : Nat)]? = some (0x00 : BitVec 8)

def imgDecPointStr (mem : ExtHashMap Nat (BitVec 8)) : Prop :=
  mem[(0x80019770 : Nat)]? = some (0x2e#8) ∧
  mem[(0x80019770 : Nat) + 1]? = some (0x00#8) ∧
  mem[(0x80019770 : Nat) + 2]? = some (0x00#8) ∧
  mem[(0x80019770 : Nat) + 3]? = some (0x00#8) ∧
  mem[(0x80019770 : Nat) + 4]? = some (0x00#8) ∧
  mem[(0x80019770 : Nat) + 5]? = some (0x00#8) ∧
  mem[(0x80019770 : Nat) + 6]? = some (0x00#8) ∧
  mem[(0x80019770 : Nat) + 7]? = some (0x00#8)

def imgParseSlotD (mem : ExtHashMap Nat (BitVec 8)) : Prop :=
  mem[(0x8001a20c : Nat)]? = some (0x0c#8) ∧
  mem[(0x8001a20c : Nat) + 1]? = some (0xdf#8) ∧
  mem[(0x8001a20c : Nat) + 2]? = some (0xfe#8) ∧
  mem[(0x8001a20c : Nat) + 3]? = some (0xff#8)

def imgParseSlotL (mem : ExtHashMap Nat (BitVec 8)) : Prop :=
  mem[(0x8001a22c : Nat)]? = some (0x38#8) ∧
  mem[(0x8001a22c : Nat) + 1]? = some (0xe4#8) ∧
  mem[(0x8001a22c : Nat) + 2]? = some (0xfe#8) ∧
  mem[(0x8001a22c : Nat) + 3]? = some (0xff#8)

def imgFnSlot (mem : ExtHashMap Nat (BitVec 8)) : Prop :=
  mem[(0x8001b880 : Nat)]? = some (0x68#8) ∧
  mem[(0x8001b880 : Nat) + 1]? = some (0x22#8) ∧
  mem[(0x8001b880 : Nat) + 2]? = some (0x01#8) ∧
  mem[(0x8001b880 : Nat) + 3]? = some (0x80#8) ∧
  mem[(0x8001b880 : Nat) + 4]? = some (0x00#8) ∧
  mem[(0x8001b880 : Nat) + 5]? = some (0x00#8) ∧
  mem[(0x8001b880 : Nat) + 6]? = some (0x00#8) ∧
  mem[(0x8001b880 : Nat) + 7]? = some (0x00#8)

def imgDecPointPtr (mem : ExtHashMap Nat (BitVec 8)) : Prop :=
  mem[(0x8001b898 : Nat)]? = some (0x70#8) ∧
  mem[(0x8001b898 : Nat) + 1]? = some (0x97#8) ∧
  mem[(0x8001b898 : Nat) + 2]? = some (0x01#8) ∧
  mem[(0x8001b898 : Nat) + 3]? = some (0x80#8) ∧
  mem[(0x8001b898 : Nat) + 4]? = some (0x00#8) ∧
  mem[(0x8001b898 : Nat) + 5]? = some (0x00#8) ∧
  mem[(0x8001b898 : Nat) + 6]? = some (0x00#8) ∧
  mem[(0x8001b898 : Nat) + 7]? = some (0x00#8)

def imgMbCurMax (mem : ExtHashMap Nat (BitVec 8)) : Prop :=
  mem[(0x8001b8f8 : Nat)]? = some (0x01#8)

def imgImpurePtr (mem : ExtHashMap Nat (BitVec 8)) : Prop :=
  mem[(0x8001b970 : Nat)]? = some (0x38#8) ∧
  mem[(0x8001b970 : Nat) + 1]? = some (0xb5#8) ∧
  mem[(0x8001b970 : Nat) + 2]? = some (0x01#8) ∧
  mem[(0x8001b970 : Nat) + 3]? = some (0x80#8) ∧
  mem[(0x8001b970 : Nat) + 4]? = some (0x00#8) ∧
  mem[(0x8001b970 : Nat) + 5]? = some (0x00#8) ∧
  mem[(0x8001b970 : Nat) + 6]? = some (0x00#8) ∧
  mem[(0x8001b970 : Nat) + 7]? = some (0x00#8)

def ImageStaticsLoaded (mem : ExtHashMap Nat (BitVec 8)) : Prop :=
  imgLldFmt mem ∧
  imgDecPointStr mem ∧
  imgParseSlotD mem ∧
  imgParseSlotL mem ∧
  imgFnSlot mem ∧
  imgDecPointPtr mem ∧
  imgMbCurMax mem ∧
  imgImpurePtr mem

theorem imageStatics_impurePtr_range {mem : ExtHashMap Nat (BitVec 8)}
    (h : ImageStaticsLoaded mem) : imgImpurePtr mem := h.2.2.2.2.2.2.2

end Vsa.Sim.Code
