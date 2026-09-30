import VsaIris.Vsa.SnpCode

namespace VsaIris.Sym

open Vsa.MemRepr

abbrev nRegs : List Nat :=
  [32, 1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26,
    27, 28, 29, 30, 31]

abbrev SnpW (live : Nat → Prop) (Dt : Mem) (DA : List Nat) (S : Nat → Prop)
    (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) :
    BitVec 64 → (Nat → BitVec 64) → Mem → Prop :=
  SWP live (snpText ++ dataOf Dt DA) nRegs S Q

end VsaIris.Sym
