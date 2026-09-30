import VsaIris.Vsa.Stdout.Code
import VsaIris.Interp.IRun

namespace VsaIris.Sym

open Vsa.MemRepr

abbrev NW (live : Nat → Prop) (Dt : Mem) (DA : List Nat) (S : Nat → Prop)
    (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) :
    BitVec 64 → (Nat → BitVec 64) → Mem → Prop :=
  SWP live (stdioText ++ dataOf Dt DA) iRegs S Q

end VsaIris.Sym
