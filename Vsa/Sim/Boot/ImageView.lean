import Vsa.Sim.Boot.Emit

/-!
# A faster view of the loaded data segment

`bootView` falls back to `imageView` for bytes the log never wrote, and the kernel reaches a
data-segment byte there through `inPieces` and a page select. `imgRuns` holds the data segment
`[dataLo, dataHi)` as runs (generated natively, checked once by `imgRuns_ok`), and `fastView`
consults it before `imageView`. `fastView_eq`: the two views are equal, so a check may be
decided on `fastView` and used on `bootView`.
-/

namespace Vsa.Sim.Boot

open Lean Elab Command

def dataLo : Nat := 0x8001acf0
def dataHi : Nat := 0x8001b990

/-- The data segment as runs of 64 bytes (writer index 0). -/
def Derive.imageRuns : RunTree :=
  let leaves := ((List.range ((dataHi - dataLo + 63) / 64)).map fun p =>
    let base := dataLo + 64 * p
    let len := min 64 (dataHi - base)
    (⟨base, len, (List.range len).foldl (fun acc j =>
      acc ||| (((bootDataByte (base + j - dataLo)).toNat * 2 ^ 24) <<< (32 * j))) 0⟩ : Run)).toArray
  Derive.buildTree leaves 0 leaves.size

elab "boot_image_runs" : command => do
  let t ← liftTermElabM <|
    unsafe Meta.evalExpr RunTree (mkConst ``RunTree) (mkConst ``Derive.imageRuns)
  Derive.addLiteralDef `Vsa.Sim.Boot.imgRuns t

boot_image_runs

def imgCellsOk (r : Run) : Bool := (List.range r.len).all fun j =>
  Nat.ble dataLo (r.base + j) && Nat.blt (r.base + j) dataHi &&
  bootDataByte (r.base + j - dataLo) == BitVec.ofNat 8 (((r.cells >>> (32 * j)) % 2 ^ 32) >>> 24)

theorem imgRuns_ok : imgRuns.runs.all imgCellsOk = true := by decide +kernel

theorem imageView_data {script x : Nat} (hlo : dataLo ≤ x) (hhi : x < dataHi) :
    imageView script x = some (bootDataByte (x - dataLo)) := by
  unfold dataLo at hlo ⊢
  unfold dataHi at hhi
  have hp := inPieces_seg (x := x) (by omega) (by omega)
  have h1 : ¬ x < 0x80000000 := by omega
  have h2 : ¬ x < 0x80018be0 := by omega
  have h3 : ¬ x < 0x80018be0 + 453 := by omega
  have h4 : ¬ x < 0x8001acf0 := by omega
  simp only [imageView, hp, imageByte, h1, h2, h3, h4, ↓reduceIte]

theorem imgRuns_cell {x k b : Nat} {script : Nat} {r : Run} (hr : r ∈ imgRuns.runs)
    (hc : r.cell x = some (k, b)) : imageView script x = some (BitVec.ofNat 8 b) := by
  have hx := Run.cell_range hc
  have hall := List.all_eq_true.mp (List.all_eq_true.mp imgRuns_ok r hr) (x - r.base)
    (List.mem_range.mpr (by omega))
  rw [show r.base + (x - r.base) = x by omega] at hall
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, beq_iff_eq] at hall
  rw [imageView_data hall.1.1 hall.1.2, hall.2]
  unfold Run.cell at hc
  simp only [hx, and_self, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
  rw [← hc.2]

noncomputable def fastView (script : Nat) (t : RunTree) (x : Nat) : Option (BitVec 8) :=
  match (t.findB x).cell x with
  | some (_, b) => some (BitVec.ofNat 8 b)
  | none =>
    match (imgRuns.findB x).cell x with
    | some (_, b) => some (BitVec.ofNat 8 b)
    | none => imageView script x

theorem fastView_eq (script : Nat) (t : RunTree) : fastView script t = bootView script t := by
  funext x
  unfold fastView bootView logView RunTree.fin
  rw [RunTree.findB_eq, RunTree.findB_eq]
  cases h1 : (t.find x).cell x with
  | some kb => obtain ⟨k, b⟩ := kb; rfl
  | none =>
    cases h2 : (imgRuns.find x).cell x with
    | some kb =>
      obtain ⟨k, b⟩ := kb
      exact (imgRuns_cell (imgRuns.find_mem x) h2).symm
    | none => rfl

end Vsa.Sim.Boot
