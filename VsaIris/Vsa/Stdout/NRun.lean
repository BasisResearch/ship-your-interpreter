import VsaIris.Vsa.Stdout.Code
import VsaIris.Interp.IRun

/-!
# newlib's stdout runs (lane N1)

`NW live D S Q pc R Mt` is `SWP` over newlib's stdout code (`stdioText`,
`Code.lean`) followed by a persistent data view (`Dt` on `DA`: the string a
call prints, the format), with the interpreter's register set `iRegs`: a
newlib call owns every GPR but `gp`/`tp`, as a helper does. The step table
`Steps/*.lean` (`scripts/gen_interp_steps.py --table stdio`) gives one lemma
per instruction over `NW`; `ix_run` drives it.
-/

namespace VsaIris.Sym

open Vsa.MemRepr

abbrev NW (live : Nat → Prop) (Dt : Mem) (DA : List Nat) (S : Nat → Prop)
    (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) :
    BitVec 64 → (Nat → BitVec 64) → Mem → Prop :=
  SWP live (stdioText ++ dataOf Dt DA) iRegs S Q

end VsaIris.Sym
