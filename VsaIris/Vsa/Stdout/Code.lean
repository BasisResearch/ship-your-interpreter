import VsaIris.Vsa.SymData
import VsaIris.Vsa.TextPieces

/-!
# Stdio text

The code of the newlib stdout chain as ranges of the binary image.
-/

namespace VsaIris.Sym

open Vsa.MemRepr Vsa.Sim VsaIris.Newlib

def stdioCodeRanges : List (Nat × Nat) :=
  [(0x8000003c, 0x8000006c), (0x80000098, 0x800000a0), (0x800000c4, 0x80000110),
   (0x80004640, 0x80004664), (0x800046ac, 0x800046f4), (0x80004764, 0x80004790),
   (0x80005078, 0x8000527c), (0x80005d18, 0x80005d2c), (0x80006120, 0x80006130),
   (0x800061c0, 0x80006210), (0x800062e0, 0x80006514), (0x800069c4, 0x80006bc8),
   (0x80006cf0, 0x80006ea0), (0x80006fd0, 0x80006fd4), (0x80006fd8, 0x80006fdc),
   (0x80006fe0, 0x80006fe4), (0x80006ff8, 0x80006ffc), (0x800070a8, 0x80007218),
   (0x8000a884, 0x8000dd90), (0x8000dda8, 0x8000e7b0), (0x8000e8cc, 0x8000e908),
   (0x8000e9f8, 0x8000eb64), (0x8000eb70, 0x8000ee94), (0x8000efd4, 0x8000f05c),
   (0x8000f0c0, 0x8000f21c), (0x8000f230, 0x8000f394), (0x80010234, 0x8001023c),
   (0x80010258, 0x80010260), (0x80010268, 0x800102b8), (0x8001039c, 0x800103f4),
   (0x800104fc, 0x80010558), (0x80012268, 0x800122d0), (0x8001688c, 0x80016970)]

def stdioPieces : List TextPiece := [⟨textByte, stdioCodeRanges⟩]

def stdioCode : List (Nat × BitVec 8) := piecesText stdioPieces

def stdioRO : List (Nat × BitVec 8) := []

def stdioText : List (Nat × BitVec 8) := stdioCode ++ stdioRO

theorem stdio_code {i : Nat} {code : List (BitVec 8)} (h : bytesHasB stdioPieces i code = true) :
    ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ stdioText :=
  fun p hp => List.mem_append_left _ (codeFoot_mem_pieces h p hp)

theorem stdioText_img_mem : ∀ p ∈ stdioText, textDom p.1 ∧ textByte p.1 = p.2 := by
  intro p hp
  rw [stdioText, stdioRO, List.append_nil] at hp
  refine forall_piecesText (P := fun a b => textDom a ∧ textByte a = b) ?_ p hp
  simp only [stdioPieces, List.mem_singleton]
  rintro q rfl a ha
  exact ⟨inRangesB_within (hi := 0x80018be0) (by decide) ha, rfl⟩

end VsaIris.Sym
