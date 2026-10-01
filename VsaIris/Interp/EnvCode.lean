import VsaIris.Vsa.SymRun
import VsaIris.Vsa.TextPieces
import VsaIris.Vsa.BinPieces

/-!
# Environment text

The code of `env_new`, `env_define`, `env_get`, `env_set`, plus the `_impure_ptr` word,
as ranges of the binary image.
-/

namespace VsaIris.Sym

open Vsa.MemRepr Vsa.Sim VsaIris.Newlib

def envCodeRanges : List (Nat × Nat) :=
  [(0x800029fc, 0x80002da8)]

def envPieces : List TextPiece := [⟨textByte, envCodeRanges⟩, impurePtrPiece]

def envText : List (Nat × BitVec 8) := piecesText envPieces

theorem env_code {i : Nat} {code : List (BitVec 8)} (h : bytesHasB envPieces i code = true) :
    ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ envText :=
  codeFoot_mem_pieces h

end VsaIris.Sym
