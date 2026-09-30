import VsaIris.Vsa.SymHavoc
import VsaIris.Vsa.ObsStep
import VsaIris.Vsa.TextPieces

/-!
# Snprintf text

The code of `_svfprintf_r` and its callees as ranges of the binary image, and the
`.rodata` conversion table it reads.
-/

namespace VsaIris.Sym

open Vsa.MemRepr Vsa.Sim VsaIris.Newlib

def snpCodeRanges : List (Nat × Nat) :=
  [(0x800046ac, 0x80004728), (0x80005c44, 0x80005d18), (0x800069c4, 0x80006bc8),
   (0x80006cf0, 0x80006dc4), (0x80007654, 0x8000a884), (0x8000e908, 0x8000e9f8),
   (0x8000f394, 0x8000f454), (0x80010234, 0x8001023c), (0x80010258, 0x80010260),
   (0x80012268, 0x800122d0), (0x8001438c, 0x80014520)]

def snpRORanges : List (Nat × Nat) :=
  [(0x8001a0fc, 0x8001a268)]

def snpPieces : List TextPiece := [⟨textByte, snpCodeRanges⟩]

def snpCode : List (Nat × BitVec 8) := piecesText snpPieces

def snpRO : List (Nat × BitVec 8) := piecesText [⟨rodataByte, snpRORanges⟩]

def snpText : List (Nat × BitVec 8) := snpCode

/-- The byte function of the conversion table. -/
def snpROImg (a : Nat) : BitVec 8 := rodataByte a

theorem snp_code {i : Nat} {code : List (BitVec 8)} (h : bytesHasB snpPieces i code = true) :
    ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ snpText :=
  codeFoot_mem_pieces h

theorem snpRO_mem_img {a w : Nat} (h : (accAddrs a w).all (inRangesB snpRORanges) = true) :
    ∀ b ∈ accAddrs a w, (b, snpROImg b) ∈ snpRO :=
  accAddrs_mem_piece h

theorem snpText_img_mem : ∀ p ∈ snpText, textDom p.1 ∧ textByte p.1 = p.2 := by
  refine forall_piecesText (P := fun a b => textDom a ∧ textByte a = b) ?_
  simp only [snpPieces, List.mem_singleton]
  rintro q rfl a ha
  exact ⟨inRangesB_within (hi := 0x80018be0) (by decide) ha, rfl⟩

/-- Conversion-table loads at literal addresses evaluate to literals. -/
macro "nx_tab" : tactic => `(tactic| simp only [VsaIris.Sym.imgLoad] at *)

end VsaIris.Sym
