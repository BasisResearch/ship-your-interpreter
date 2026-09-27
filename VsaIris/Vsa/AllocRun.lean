import VsaIris.Vsa.SymRun
import VsaIris.Vsa.AllocCode

namespace VsaIris.Sym

open Vsa.MemRepr

abbrev aRegs : List Nat := [32, 1, 10, 2, 5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31, 8, 9, 18, 19]

abbrev AW (live : Nat → Prop) (S : Nat → Prop) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) :
    BitVec 64 → (Nat → BitVec 64) → Mem → Prop :=
  SWP live allocText aRegs S Q

end VsaIris.Sym
