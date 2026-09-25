import Vsa.Densify.Transport
import Vsa.Densify.GenC

/-!
# The machine is insensitive to absent bytes (P3)

The Sail memory is sparse; an absent byte reads as `0` (`readByte = getD 0`)
and `stepOnce` never inspects presence (`Vsa.Densify.Gen.stepOnce_resp`, a
logical-relations proof over every model function in its call graph, see
`Vsa/Densify/Resp.lean`). Hence a configuration and its fill-with-zero
(`fillZero`: every absent RAM byte inserted as `some 0`) halt with the same
output and exit code, and diverge together.
-/

namespace Vsa.Densify

open Vsa.Machine

/-- `stepOnce` respects zero-equivalence. -/
theorem stepOnce_resp (i u : Nat) : Resp (Vsa.stepOnce i u) := Gen.stepOnce_resp i u

/-- **Halting is invariant under `fillZero`.** -/
theorem halts_fillZero (c : Config) (out : String) (e : Nat) :
    Halts c out e ↔ Halts (fillZero c) out e :=
  halts_iff_of_ceqv stepOnce_resp (ceqv_fillZero c) out e

/-- **Divergence is invariant under `fillZero`.** -/
theorem diverges_fillZero (c : Config) : Diverges c ↔ Diverges (fillZero c) :=
  diverges_iff_of_ceqv stepOnce_resp (ceqv_fillZero c)

/-- More generally, any two zero-equivalent configurations behave alike. -/
theorem halts_iff_ceqv {c c' : Config} (h : CEqv c c') (out : String) (e : Nat) :
    Halts c out e ↔ Halts c' out e :=
  halts_iff_of_ceqv stepOnce_resp h out e

theorem diverges_iff_ceqv {c c' : Config} (h : CEqv c c') : Diverges c ↔ Diverges c' :=
  diverges_iff_of_ceqv stepOnce_resp h

end Vsa.Densify
