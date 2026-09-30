import VsaIris.Vsa.SymData
import VsaIris.Vsa.TextPieces

/-!
# Interpreter text

The code and `.rodata` bytes the interpreter's recursive evaluator executes and reads,
as ranges of the fixed binary image.
-/

namespace VsaIris.Sym

open Vsa.MemRepr Vsa.Sim VsaIris.Newlib

def interpCodeRanges : List (Nat × Nat) :=
  [(0x800027ec, 0x800029fc), (0x80002df4, 0x80004308), (0x800043ec, 0x80004588),
   (0x80004640, 0x80004664), (0x800046a4, 0x80004764)]

def interpRORanges : List (Nat × Nat) :=
  [(0x80019370, 0x8001937c), (0x80019ef8, 0x80019fdc), (0x80019fe0, 0x80019ff8)]

def interpCodePieces : List TextPiece := [⟨textByte, interpCodeRanges⟩]

def interpROPieces : List TextPiece := [⟨rodataByte, interpRORanges⟩]

def interpCode : List (Nat × BitVec 8) := piecesText interpCodePieces

def interpRO : List (Nat × BitVec 8) := piecesText interpROPieces

def interpText : List (Nat × BitVec 8) := interpCode ++ interpRO

/-- The byte function of the interpreter's constant tables. -/
def interpROImg (a : Nat) : BitVec 8 := rodataByte a

theorem interp_code {i : Nat} {code : List (BitVec 8)}
    (h : bytesHasB interpCodePieces i code = true) :
    ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText :=
  fun p hp => List.mem_append_left _ (codeFoot_mem_pieces h p hp)

theorem interpRO_mem_img {a w : Nat} (h : (accAddrs a w).all (inRangesB interpRORanges) = true) :
    ∀ b ∈ accAddrs a w, (b, interpROImg b) ∈ interpRO :=
  accAddrs_mem_piece h

theorem interpText_img_mem :
    ∀ p ∈ interpText, (textDom p.1 ∧ textByte p.1 = p.2) ∨
      (rodataDom p.1 ∧ rodataByte p.1 = p.2) := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · refine .inl (forall_piecesText (P := fun a b => textDom a ∧ textByte a = b) ?_ p hp)
    simp only [interpCodePieces, List.mem_singleton]
    rintro q rfl a ha
    exact ⟨inRangesB_within (hi := 0x80018be0) (by decide) ha, rfl⟩
  · refine .inr (forall_piecesText (P := fun a b => rodataDom a ∧ rodataByte a = b) ?_ p hp)
    simp only [interpROPieces, List.mem_singleton]
    rintro q rfl a ha
    exact ⟨inRangesB_within (hi := 0x8001acf0) (by decide) ha, rfl⟩

/-- Constant-table loads at literal addresses evaluate to literals. -/
macro "ix_tab" : tactic => `(tactic| simp only [VsaIris.Sym.imgLoad] at *)

end VsaIris.Sym
