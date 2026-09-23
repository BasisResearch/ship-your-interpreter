import VsaIris.Vsa.Instance
import VsaIris.Vsa.Tools
import VsaIris.Interp.Repr
import VsaIris.MallocRun
import Vsa.Sim.JmpSpec

/-!
# Segments over owned byte images

H5's segments read and write bytes the Iris side owns as images
(`ownImg S img`: a frame, `main`'s saved words, newlib's data). `wp_segW`
takes its read footprint as a list and each `ld` as a byte list with a
`MemFacts` fact. This module converts once:

* `ownImg_range`: an owned `n`-byte extent as the segment footprint list
  (`imgFoot`), and back;
* `imgWord img a`: the loaded bytes of an `ld` at `a`, with
  `bytesVal_imgWord` (the loaded value is `imgW img a`) and `ldFact`
  (the `MemFacts` of the load from the footprint's agreement);
* `stdioAt_open`/`stdioAt_close`: a window of newlib's data out of `stdioAt`
  and back, keeping the image.
-/

namespace VsaIris.Inst

open Iris Iris.BI Iris.Std Iris.ProofMode
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Sim VsaIris.Interp

/-! ## Loaded words -/

/-- The 8 bytes an `ld` at `a` reads from `img`. -/
def imgWord (img : Nat → BitVec 8) (a : Nat) : List (BitVec 8) :=
  [img a, img (a + 1), img (a + 2), img (a + 3), img (a + 4), img (a + 5), img (a + 6),
    img (a + 7)]

theorem toNat_append8 {m : Nat} (x : BitVec m) (y : BitVec 8) :
    (x.append y).toNat = y.toNat + 256 * x.toNat := by
  change (x ++ y).toNat = _
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]
  omega

/-- An `ld` of `imgWord img a` loads the little-endian word `imgW img a`. -/
theorem bytesVal_imgWord (img : Nat → BitVec 8) (a : Nat) :
    bytesVal .ld (imgWord img a) = imgW img a := by
  apply BitVec.eq_of_toNat_eq
  rw [imgW_toNat]
  simp only [bytesVal, imgWord, List.getD_cons_zero, List.getD_cons_succ, sext64_id_jmp]
  simp only [imgLE, toNat_append8, Nat.add_assoc, Nat.reduceAdd]
  omega

/-- An `ld` at `ea` in RAM, off the HTIF words, where the memory agrees with
`img`: its `MemFacts` with the loaded bytes `imgWord img ea`. -/
theorem ldFact {m : Std.ExtHashMap Nat (BitVec 8)} {L : GRegs} {a : MInstr}
    {img : Nat → BitVec 8} {ea : Nat} (hk : a.kind = .ld) (hea : (eaddrM a L).toNat = ea)
    (hlo : 0x80000000 ≤ ea) (hhi : ea + 8 ≤ 0x100000000)
    (hwin : ea + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ ea)
    (hpin : ∀ k, k < 8 → (m[ea + k]?).getD 0 = img (ea + k)) :
    MemFacts m L (imgWord img ea) a := by
  unfold MemFacts
  rw [hk]
  simp only
  rw [hea]
  refine ⟨⟨hlo, hhi, hwin⟩, ?_⟩
  simp only [LPins8, imgWord, List.getD_cons_zero, List.getD_cons_succ]
  exact ⟨by simpa using hpin 0 (by omega), hpin 1 (by omega), hpin 2 (by omega),
    hpin 3 (by omega), hpin 4 (by omega), hpin 5 (by omega), hpin 6 (by omega),
    hpin 7 (by omega)⟩

/-- A `sw` at `ea`: its `MemFacts`. -/
theorem swFact {m : Std.ExtHashMap Nat (BitVec 8)} {L : GRegs} {a : MInstr} {bs : List (BitVec 8)}
    {ea : Nat} (hk : a.kind = .sw) (hea : (eaddrM a L).toNat = ea)
    (hlo : 0x80000000 ≤ ea) (hhi : ea + 4 ≤ 0x100000000) (hwin : tohostAddr + 16 ≤ ea)
    (hal : ea % 4 = 0) : MemFacts m L bs a := by
  unfold MemFacts
  rw [hk]
  simp only
  rw [hea]
  exact ⟨hlo, hhi, hwin, hal⟩

/-- A `sd` at `ea`: its `MemFacts`. -/
theorem sdFact {m : Std.ExtHashMap Nat (BitVec 8)} {L : GRegs} {a : MInstr} {bs : List (BitVec 8)}
    {ea : Nat} (hk : a.kind = .sd) (hea : (eaddrM a L).toNat = ea)
    (hlo : 0x80000000 ≤ ea) (hhi : ea + 8 ≤ 0x100000000) (hwin : tohostAddr + 16 ≤ ea)
    (hal : ea % 8 = 0) : MemFacts m L bs a := by
  unfold MemFacts
  rw [hk]
  simp only
  rw [hea]
  exact ⟨hlo, hhi, hwin, hal⟩

/-- `base + sext imm` for a nonnegative 12-bit offset that does not wrap. -/
theorem addr_off (base : BitVec 64) (imm : BitVec 12) (off : Nat)
    (himm : (sign_extend (m := 64) imm : BitVec 64).toNat = off)
    (h : base.toNat + off < 2 ^ 64) :
    (base + sign_extend (m := 64) imm).toNat = base.toNat + off := by
  rw [BitVec.toNat_add, himm]
  exact Nat.mod_eq_of_lt h

/-! ## Owned extents as segment footprints -/

/-- The read footprint of an owned `n`-byte extent at the image `img`. -/
def imgFoot (a n : Nat) (img : Nat → BitVec 8) : List (Nat × DFrac × BitVec 8) :=
  (List.range' a n).map (fun k => (k, DFrac.own 1, img k))

/-- The written-byte list of an owned `n`-byte extent at `img`. -/
def imgW8 (a n : Nat) (img : Nat → BitVec 8) : List (Nat × BitVec 8) :=
  (List.range' a n).map (fun k => (k, img k))

section Own

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

theorem ownImg_inExt_iff (a n : Nat) (k : Nat) : InExt (a, n) k ↔ k ∈ List.range' a n := by
  unfold InExt; rw [List.mem_range']; constructor
  · intro h; exact ⟨k - a, by simp at h; omega, by simp at h; omega⟩
  · rintro ⟨i, hi, rfl⟩; simp; omega

theorem ownImg_range (a n : Nat) (img : Nat → BitVec 8) :
    ownImg (GF := GF) (InExt (a, n)) img ⊣⊢
      sepL (imgFoot a n img) (fun p => p.1 ↦ₘ{p.2.1} p.2.2) := by
  unfold imgFoot
  rw [VsaIris.sepL_map]
  constructor
  · iintro H
    ihave H := ownSet_iff _ (ownImg_inExt_iff a n) $$ H
    iapply ownSet_to_sepL _ (List.nodup_range' _ (by omega)) $$ H
  · iintro H
    ihave H := sepL_to_ownSet _ (List.nodup_range' _ (by omega)) $$ H
    iapply ownSet_iff _ (fun k => (ownImg_inExt_iff a n k).symm) $$ H

theorem ownImg_range_w (a n : Nat) (img : Nat → BitVec 8) :
    ownImg (GF := GF) (InExt (a, n)) img ⊣⊢ sepL (imgW8 a n img) (fun p => p.1 ↦ₘ p.2) := by
  unfold imgW8
  rw [VsaIris.sepL_map]
  constructor
  · iintro H
    ihave H := ownSet_iff _ (ownImg_inExt_iff a n) $$ H
    iapply ownSet_to_sepL _ (List.nodup_range' _ (by omega)) $$ H
  · iintro H
    ihave H := sepL_to_ownSet _ (List.nodup_range' _ (by omega)) $$ H
    iapply ownSet_iff _ (fun k => (ownImg_inExt_iff a n k).symm) $$ H

/-- A footprint agreement on an owned extent reads every byte of it. -/
theorem imgFoot_pin {live : Nat → Prop} {c : Vsa.Machine.Config} {MR : List (Nat × DFrac × BitVec 8)}
    {a n : Nat} {img : Nat → BitVec 8}
    (hMR : ∀ p ∈ MR, (vsaModel live).mem c p.1 = p.2.2) (hsub : ∀ p ∈ imgFoot a n img, p ∈ MR) :
    ∀ k, a ≤ k → k < a + n → (c.σ.mem[k]?).getD 0 = img k := by
  intro k h1 h2
  have := hMR (k, DFrac.own 1, img k) (hsub _ (List.mem_map.mpr ⟨k, by
    rw [List.mem_range']; exact ⟨k - a, by omega, by omega⟩, rfl⟩))
  exact this

end Own

end VsaIris.Inst
