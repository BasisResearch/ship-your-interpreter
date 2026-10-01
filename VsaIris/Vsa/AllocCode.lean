import VsaIris.Vsa.SymRun
import VsaIris.Vsa.TextPieces
import VsaIris.Vsa.BinPieces

/-!
# Allocator text

The code of `_malloc_r`, `_free_r`, `_realloc_r` and their callees, plus the `_impure_ptr`
word they read, as ranges of the binary image.
-/

namespace VsaIris.Sym

open Vsa.MemRepr Vsa.Sim VsaIris.Newlib

def allocCodeRanges : List (Nat × Nat) :=
  [(0x80000118, 0x80000180), (0x80004790, 0x80005078), (0x8000527c, 0x800058c0),
   (0x8000696c, 0x80006aec), (0x80006bc8, 0x80006cf0), (0x80006fe0, 0x80006fe4),
   (0x80006ff8, 0x80006ffc), (0x8000722c, 0x80007654)]

def allocPieces : List TextPiece := [⟨textByte, allocCodeRanges⟩, impurePtrPiece]

def allocText : List (Nat × BitVec 8) := piecesText allocPieces

theorem alloc_code {i : Nat} {code : List (BitVec 8)} (h : bytesHasB allocPieces i code = true) :
    ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ allocText :=
  codeFoot_mem_pieces h

theorem alloc_impure {m : Mem} (h : TextLoaded allocText m) :
    LPins8 m (0x8001b510#64 + 0x460#64).toNat [0x38#8, 0xb5#8, 0x01#8, 0x80#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8] := by
  rw [show (0x8001b510#64 + 0x460#64).toNat = 0x8001b970 by decide]
  exact lpins8_of_text h rfl (by decide)

end VsaIris.Sym
