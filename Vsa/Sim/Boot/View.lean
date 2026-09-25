import Vsa.Sim.Boot.Config
import Vsa.Sim.Code.FixedImage

/-!
# Reads through a byte view

`ViewOf m v`: the memory `m` reads byte by byte as the function `v`. For the
boot memory, `v` is `bootView script runs` (`Image.lean`), a kernel-computable
function, so every read fact of `Loaded` is one `decide +kernel` over `v`:
`boot_read` rewrites the reads of a goal into the view and decides it.

The images: `.text` and `.rodata` after the script are the loader's bytes
when no store lands below `.data` (`RunTree.above`, decided per trace).
-/

namespace Vsa.Sim.Boot

open Vsa.MemRepr

/-- `m` reads as `v`, byte by byte. -/
def ViewOf (m : Mem) (v : Nat → Option (BitVec 8)) : Prop := ∀ x, m[x]? = v x

/-- `readLE` over a byte view. -/
def readLEv (v : Nat → Option (BitVec 8)) (a : Nat) : Nat → Option Nat
  | 0 => some 0
  | k + 1 => do
    let b ← v a
    let rest ← readLEv v (a + 1) k
    pure (b.toNat + 256 * rest)

theorem ViewOf.readLE {m : Mem} {v : Nat → Option (BitVec 8)} (h : ViewOf m v) (a n : Nat) :
    Vsa.MemRepr.readLE m a n = readLEv v a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp only [Vsa.MemRepr.readLE, readLEv, h a, ih]

theorem ViewOf.read64 {m : Mem} {v : Nat → Option (BitVec 8)} (h : ViewOf m v) (a : Nat) :
    Vsa.MemRepr.read64 m a = readLEv v a 8 := h.readLE a 8

theorem ViewOf.read32 {m : Mem} {v : Nat → Option (BitVec 8)} (h : ViewOf m v) (a : Nat) :
    Vsa.MemRepr.read32 m a = readLEv v a 4 := h.readLE a 4

theorem isSome_exists {α : Type} {o : Option α} (h : o.isSome = true) : ∃ b, o = some b :=
  Option.isSome_iff_exists.mp h

/-- Rewrite every read of `m` in the goal through the view `h : ViewOf m v`
and decide it in the kernel. Handles `readLE`/`read32`/`read64` equations,
byte lookups, and presence (`∃ b, … = some b`). -/
macro "boot_read " h:term : tactic =>
  `(tactic| first
    | (apply isSome_exists
       first
         | rw [ViewOf.readLE $h]
         | rw [ViewOf.read64 $h]
         | rw [ViewOf.read32 $h]
         | rw [$h:term]
       decide +kernel)
    | (first
         | rw [ViewOf.read64 $h]
         | rw [ViewOf.read32 $h]
         | rw [ViewOf.readLE $h]
         | rw [$h:term]
       decide +kernel))

/-! ## The boot memory's view -/

theorem bootMem_view {script : Nat} {L : PackedLog} {t : RunTree} (h : LogOk L t) :
    ViewOf (bootMem script L) (bootView script t) :=
  bootMem_get h

/-- Every run lies at or above `lo`. -/
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

/-- The segment `[0x80000000, 0x8001b990)` is one loader piece. -/
theorem inPieces_seg {x : Nat} (hlo : 0x80000000 ≤ x) (hhi : x < 0x8001b990) :
    inPieces bootPieces x = true := by
  simp only [inPieces, bootPieces, List.any_cons, List.any_nil, Bool.or_eq_true,
    decide_eq_true_eq]
  omega

/-- Below the first store, the entry memory is the loader's. -/
theorem bootView_below {script : Nat} {t : RunTree} {lo : Nat} (h : t.above lo = true)
    {x : Nat} (hx : x < lo) : bootView script t x = imageView script x := by
  unfold bootView logView
  rw [RunTree.fin_none_below h hx]

/-- The `.text` image is the loader's when every store lies above it. -/
theorem bootMem_text {script : Nat} {L : PackedLog} {t : RunTree} (h : LogOk L t)
    (ha : t.above 0x80018be0 = true) : Code.FixedTextLoaded (bootMem script L) := by
  intro off hoff
  unfold Code.fixedTextSize at hoff
  show (bootMem script L)[0x80000000 + off]? = _
  have hp := inPieces_seg (x := 0x80000000 + off) (by omega) (by omega)
  have h1 : ¬ 0x80000000 + off < 0x80000000 := by omega
  have h2 : 0x80000000 + off < 0x80018be0 := by omega
  rw [bootMem_view h, bootView_below ha h2]
  simp only [imageView, hp, imageByte, h1, h2, ↓reduceIte, Nat.add_sub_cancel_left]

/-- `.rodata` after the script blob and its NUL is the loader's when every
store lies above it (REVIEW.md P2's pin). -/
theorem bootMem_rodata {script : Nat} {L : PackedLog} {t : RunTree} (h : LogOk L t)
    (ha : t.above 0x8001acf0 = true) :
    ∀ off, 454 ≤ off → off < Code.fixedRodataSize →
      (bootMem script L)[Code.fixedRodataBase + off]? = some (Code.fixedRodataByte off) := by
  intro off hlo hoff
  unfold Code.fixedRodataSize at hoff
  show (bootMem script L)[0x80018be0 + off]? = _
  have hp := inPieces_seg (x := 0x80018be0 + off) (by omega) (by omega)
  have h1 : ¬ 0x80018be0 + off < 0x80000000 := by omega
  have h2 : ¬ 0x80018be0 + off < 0x80018be0 := by omega
  have h3 : ¬ 0x80018be0 + off < 0x80018be0 + 453 := by omega
  have h4 : 0x80018be0 + off < 0x8001acf0 := by omega
  rw [bootMem_view h, bootView_below ha h4]
  simp only [imageView, hp, imageByte, h1, h2, h3, h4, ↓reduceIte, Nat.add_sub_cancel_left]

end Vsa.Sim.Boot

namespace Vsa.Sim.Boot

/-- Split a structure of read facts and decide each through the view `h`. -/
macro "boot_facts " h:term : tactic =>
  `(tactic| repeat' (first | boot_read $h | constructor))

end Vsa.Sim.Boot
