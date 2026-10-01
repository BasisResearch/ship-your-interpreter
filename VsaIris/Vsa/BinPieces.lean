import Vsa.Sim.TextImage

/-!
# Pieces of the fixed binary outside the text/rodata image

Initialised `.data` words that proofs read as constant text.
-/

namespace VsaIris.Sym

open Vsa.Sim

/-- The initialised `_impure_ptr` word (`.data`, value `0x8001b538`). -/
def impurePtrPiece : TextPiece := ⟨natBytes 0x8001b970 0x8001b538, [(0x8001b970, 0x8001b978)]⟩

end VsaIris.Sym
