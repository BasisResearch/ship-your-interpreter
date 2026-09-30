import Vsa.Sim.Code.FixedImageData
import Vsa.Sim.TextImage

open Std (ExtHashMap)

namespace Vsa.Sim.Code

def FixedBytesLoaded (base size : Nat) (byte : Nat → BitVec 8)
    (mem : ExtHashMap Nat (BitVec 8)) : Prop :=
  ∀ offset, offset < size → mem[base + offset]? = some (byte offset)

def FixedTextLoaded (mem : ExtHashMap Nat (BitVec 8)) : Prop :=
  FixedBytesLoaded fixedTextBase fixedTextSize fixedTextByte mem

def fixedScriptSize : Nat := 454

def FixedRodataLoaded (mem : ExtHashMap Nat (BitVec 8)) : Prop :=
  ∀ offset, fixedScriptSize ≤ offset → offset < fixedRodataSize →
    mem[fixedRodataBase + offset]? = some (fixedRodataByte offset)

theorem FixedBytesLoaded.transport
    {base size : Nat} {byte : Nat → BitVec 8}
    {mem mem' : ExtHashMap Nat (BitVec 8)}
    (h : FixedBytesLoaded base size byte mem)
    (hag : ∀ a, base ≤ a → a < base + size → mem'[a]? = mem[a]?) :
    FixedBytesLoaded base size byte mem' := by
  intro offset hoff
  exact (hag (base + offset) (Nat.le_add_right _ _)
    (Nat.add_lt_add_left hoff base)).trans (h offset hoff)

theorem FixedTextLoaded.transport
    {mem mem' : ExtHashMap Nat (BitVec 8)} (h : FixedTextLoaded mem)
    (hag : ∀ a, 0x80000000 ≤ a → a < 0x80018be0 → mem'[a]? = mem[a]?) :
    FixedTextLoaded mem' :=
  FixedBytesLoaded.transport h hag

theorem FixedRodataLoaded.transport
    {mem mem' : ExtHashMap Nat (BitVec 8)} (h : FixedRodataLoaded mem)
    (hag : ∀ a, 0x80018da6 ≤ a → a < 0x8001acf0 → mem'[a]? = mem[a]?) :
    FixedRodataLoaded mem' := by
  intro offset hlo hhi
  exact (hag (fixedRodataBase + offset)
    (by unfold fixedRodataBase; unfold fixedScriptSize at hlo; omega)
    (by unfold fixedRodataBase; unfold fixedRodataSize at hhi; omega)).trans (h offset hlo hhi)

theorem FixedRodataLoaded.byteAt {mem : ExtHashMap Nat (BitVec 8)} (h : FixedRodataLoaded mem)
    {a : Nat} (hlo : 0x80018da6 ≤ a) (hhi : a < 0x8001acf0) :
    mem[a]? = some (fixedRodataByte (a - 0x80018be0)) := by
  have hb := h (a - 0x80018be0) (by unfold fixedScriptSize; omega)
    (by unfold fixedRodataSize; omega)
  have e : fixedRodataBase + (a - 0x80018be0) = a := by unfold fixedRodataBase; omega
  rw [e] at hb
  exact hb

/-- The fixed text image on `[lo, hi)`. -/
def fixedCodePieces (lo hi : Nat) : List TextPiece :=
  [⟨fun a => fixedTextByte (a - fixedTextBase), [(lo, hi)]⟩]

/-- The code of a function at `[lo, hi)` is present, as in the fixed image. -/
abbrev CodeLoaded (lo hi : Nat) (mem : ExtHashMap Nat (BitVec 8)) : Prop :=
  TextIn (piecesText (fixedCodePieces lo hi)) mem

theorem CodeLoaded.transport {lo hi : Nat} {mem mem' : ExtHashMap Nat (BitVec 8)}
    (h : CodeLoaded lo hi mem) (hag : ∀ a, lo ≤ a → a < hi → mem'[a]? = mem[a]?) :
    CodeLoaded lo hi mem' :=
  TextIn.transport h fun p hp => by
    obtain ⟨q, hq, hr, -⟩ := mem_piecesText_iff.1 hp
    simp only [fixedCodePieces, List.mem_singleton] at hq
    subst hq
    obtain ⟨r, hrr, h1, h2⟩ := inRangesB_iff.1 hr
    simp only [List.mem_singleton] at hrr
    subst hrr
    exact hag _ h1 h2

theorem FixedTextLoaded.code {mem : ExtHashMap Nat (BitVec 8)} (h : FixedTextLoaded mem)
    {lo hi : Nat} (hr : 0x80000000 ≤ lo ∧ hi ≤ 0x80018be0 := by decide) : CodeLoaded lo hi mem := by
  intro p hp
  obtain ⟨q, hq, hrq, he⟩ := mem_piecesText_iff.1 hp
  simp only [fixedCodePieces, List.mem_singleton] at hq
  subst hq
  obtain ⟨r, hrr, h1, h2⟩ := inRangesB_iff.1 hrq
  simp only [List.mem_singleton] at hrr
  subst hrr
  have := h (p.1 - fixedTextBase) (by unfold fixedTextBase fixedTextSize at *; simp only at h1 h2; omega)
  rw [show fixedTextBase + (p.1 - fixedTextBase) = p.1 by unfold fixedTextBase at *; simp only at h1; omega] at this
  rw [he]; exact this

end Vsa.Sim.Code
