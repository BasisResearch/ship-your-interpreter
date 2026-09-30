import Vsa.Densify.Transport
import Vsa.Densify.GenC

namespace Vsa.Densify

open Vsa.Machine

theorem stepOnce_resp (i u : Nat) : Resp (Vsa.stepOnce i u) := Gen.stepOnce_resp i u

theorem halts_fillZero (c : Config) (out : String) (e : Nat) :
    Halts c out e ↔ Halts (fillZero c) out e :=
  halts_iff_of_ceqv stepOnce_resp (ceqv_fillZero c) out e

theorem diverges_fillZero (c : Config) : Diverges c ↔ Diverges (fillZero c) :=
  diverges_iff_of_ceqv stepOnce_resp (ceqv_fillZero c)

end Vsa.Densify
