import Vsa.Sim.Boot.Config
import Vsa.Sim.Code.FixedImage

namespace Vsa.Sim.Boot

open Vsa.MemRepr

def ViewOf (m : Mem) (v : Nat → Option (BitVec 8)) : Prop := ∀ x, m[x]? = v x

def readLEv (v : Nat → Option (BitVec 8)) (a : Nat) : Nat → Option Nat
  | 0 => some 0
  | k + 1 => do
    let b ← v a
    let rest ← readLEv v (a + 1) k
    pure (b.toNat + 256 * rest)

theorem bootMem_view {script : Nat} {L : PackedLog} {t : RunTree} (h : LogOk L t) :
    ViewOf (bootMem script L) (bootView script t) :=
  bootMem_get h

def RunTree.above (t : RunTree) (lo : Nat) : Bool := t.runs.all fun r => decide (lo ≤ r.base)

theorem RunTree.fin_none_below {t : RunTree} {lo : Nat} (h : t.above lo = true) {x : Nat}
    (hx : x < lo) : t.fin x = none := by
  unfold RunTree.fin
  cases hc : (t.find x).cell x with
  | none => rfl
  | some c =>
    have hr := Run.cell_range hc
    have := List.all_eq_true.mp h _ (t.find_mem x)
    simp only [decide_eq_true_eq] at this
    omega

theorem inPieces_seg {x : Nat} (hlo : 0x80000000 ≤ x) (hhi : x < 0x8001b990) :
    inPieces bootPieces x = true := by
  simp only [inPieces, bootPieces, List.any_cons, List.any_nil, Bool.or_eq_true,
    decide_eq_true_eq]
  omega

theorem bootView_below {script : Nat} {t : RunTree} {lo : Nat} (h : t.above lo = true)
    {x : Nat} (hx : x < lo) : bootView script t x = imageView script x := by
  unfold bootView logView
  rw [RunTree.fin_none_below h hx]

theorem bootView_text {script : Nat} {t : RunTree} (ha : t.above 0x80018be0 = true)
    {off : Nat} (hoff : off < Code.fixedTextSize) :
    bootView script t (Code.fixedTextBase + off) = some (Code.fixedTextByte off) := by
  unfold Code.fixedTextSize at hoff
  show bootView script t (0x80000000 + off) = _
  have hp := inPieces_seg (x := 0x80000000 + off) (by omega) (by omega)
  have h1 : ¬ 0x80000000 + off < 0x80000000 := by omega
  have h2 : 0x80000000 + off < 0x80018be0 := by omega
  rw [bootView_below ha h2]
  simp only [imageView, hp, imageByte, h1, h2, ↓reduceIte, Nat.add_sub_cancel_left]

theorem bootView_rodata {script : Nat} {t : RunTree} (ha : t.above 0x8001acf0 = true)
    {off : Nat} (hlo : Code.fixedScriptSize ≤ off) (hoff : off < Code.fixedRodataSize) :
    bootView script t (Code.fixedRodataBase + off) = some (Code.fixedRodataByte off) := by
  unfold Code.fixedRodataSize at hoff
  unfold Code.fixedScriptSize at hlo
  show bootView script t (0x80018be0 + off) = _
  have hp := inPieces_seg (x := 0x80018be0 + off) (by omega) (by omega)
  have h1 : ¬ 0x80018be0 + off < 0x80000000 := by omega
  have h2 : ¬ 0x80018be0 + off < 0x80018be0 := by omega
  have h3 : ¬ 0x80018be0 + off < 0x80018be0 + 453 := by omega
  have h4 : 0x80018be0 + off < 0x8001acf0 := by omega
  rw [bootView_below ha h4]
  simp only [imageView, hp, imageByte, h1, h2, h3, h4, ↓reduceIte, Nat.add_sub_cancel_left]

end Vsa.Sim.Boot
