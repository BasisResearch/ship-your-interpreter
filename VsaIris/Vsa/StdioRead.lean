import VsaIris.Interp.Bridge
import VsaIris.Vsa.Stdio

/-!
# Words of newlib's data, read off a `StdioOK` image

`StdioOK img` quantifies over memories agreeing with `img` on `stdioFoot`.
`fillMem` builds one, so each memory fact of `ConsoleStream`/`ExitRuntimeData`
becomes a word of the image (`StdioOK.word`). H5 reads `_impure_ptr` and
`_impure_data._stderr` this way at `main`'s error line. `StdioOK.impureImg`
gives `_impure_ptr` byte by byte.
-/

namespace VsaIris.Stdio

open Vsa.MemRepr Vsa.Sim VsaIris.Interp

/-- A memory holding `img` on `l`. -/
def fillMem (img : Nat → BitVec 8) : List Nat → Mem
  | [] => ∅
  | a :: l => (fillMem img l).insert a (img a)

theorem fillMem_get (img : Nat → BitVec 8) : ∀ {l : List Nat} {a : Nat}, a ∈ l →
    (fillMem img l)[a]? = some (img a)
  | b :: l, a, h => by
    simp only [fillMem]
    rw [Std.ExtHashMap.getElem?_insert]
    by_cases hb : b = a
    · subst hb; simp
    · simp only [beq_iff_eq, hb, ite_false]
      exact fillMem_get img (List.mem_of_ne_of_mem (Ne.symm hb) h)

attribute [irreducible] fillMem

/-- `.data`/`.bss` from `__sglue` to `__bss_end`. Irreducible: it has 3144
elements. -/
@[irreducible] def dataList : List Nat := List.range' 0x8001b520 (0x8001c168 - 0x8001b520)

theorem mem_dataList_iff {a : Nat} : a ∈ dataList ↔ 0x8001b520 ≤ a ∧ a < 0x8001c168 := by
  unfold dataList; rw [List.mem_range']
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · intro h; exact ⟨a - 0x8001b520, by omega, by omega⟩

theorem mem_dataList {a : Nat} (h : stdioFoot a) : a ∈ dataList := by
  rw [mem_dataList_iff]
  unfold stdioFoot InRange at h
  omega

/-- The canonical memory of a `StdioOK` image. -/
theorem StdioOK.facts {img : Nat → BitVec 8} (h : StdioOK img) :
    ConsoleStream (fillMem img dataList) ∧ ExitRuntimeData (fillMem img dataList) ∧
      read64 (fillMem img dataList) stderrPtrAddr = some exitStderr ∧
      LocaleData (fillMem img dataList) ∧ StderrStream (fillMem img dataList) :=
  h (fillMem img dataList) (fun _ ha => fillMem_get (l := dataList) img (mem_dataList ha))

/-- A word of the image, from a `read64` fact about its canonical memory. -/
theorem StdioOK.word {img : Nat → BitVec 8} {a v : Nat}
    (hr : read64 (fillMem img dataList) a = some v)
    (hin : ∀ i, i < 8 → a + i ∈ dataList) : imgW img a = BitVec.ofNat 64 v := by
  have h := readLE_memImg (n := 8) hr
  have e : imgLE img a 8 = imgLE (memImg (fillMem img dataList)) a 8 :=
    imgLE_congr fun i hi => by unfold memImg; rw [fillMem_get img (hin i hi)]; rfl
  unfold imgW
  rw [e, h]

theorem dataList_range {a : Nat} (h1 : 0x8001b520 ≤ a) (h2 : a + 8 ≤ 0x8001c168) :
    ∀ i, i < 8 → a + i ∈ dataList := by
  intro i hi; rw [mem_dataList_iff]; omega

/-- `_impure_ptr` holds `&_impure_data`. -/
theorem StdioOK.impure {img : Nat → BitVec 8} (h : StdioOK img) :
    imgW img consoleImpurePtrAddr = BitVec.ofNat 64 consoleReent :=
  StdioOK.word h.facts.1.impure (dataList_range (by decide) (by decide))

/-- `_impure_data._stderr` holds `&__sf[2]`. -/
theorem StdioOK.stderr {img : Nat → BitVec 8} (h : StdioOK img) :
    imgW img stderrPtrAddr = BitVec.ofNat 64 exitStderr :=
  StdioOK.word h.facts.2.2.1 (dataList_range (by decide) (by decide))

/-- The bytes of a little-endian number, one by one. -/
theorem imgLE_byte (img : Nat → BitVec 8) : ∀ {n a i : Nat}, i < n →
    img (a + i) = BitVec.ofNat 8 (imgLE img a n / 256 ^ i)
  | n + 1, a, 0, _ => by
    apply BitVec.eq_of_toNat_eq
    simp only [imgLE, Nat.pow_zero, Nat.div_one, Nat.add_zero, BitVec.toNat_ofNat]
    have := (img a).isLt
    omega
  | n + 1, a, i + 1, h => by
    rw [show a + (i + 1) = (a + 1) + i by omega, imgLE_byte img (n := n) (a := a + 1) (by omega)]
    congr 1
    simp only [imgLE]
    rw [Nat.pow_succ, Nat.mul_comm (256 ^ i) 256, ← Nat.div_div_eq_div_mul]
    congr 1
    have := (img a).isLt
    omega

/-- A `StdioOK` image holds `&_impure_data` in `_impure_ptr`, byte by byte. -/
theorem StdioOK.impureImg {img : Nat → BitVec 8} (h : StdioOK img) : ImpureImg img := by
  intro a ha
  have hw := congrArg BitVec.toNat h.impure
  rw [imgW_toNat, BitVec.toNat_ofNat] at hw
  unfold consoleImpurePtrAddr at hw
  rw [Nat.mod_eq_of_lt (by unfold consoleReent; omega)] at hw
  unfold impureW at ha
  obtain ⟨i, rfl⟩ : ∃ i, a = 0x8001b970 + i := ⟨a - 0x8001b970, by omega⟩
  rw [imgLE_byte img (n := 8) (a := 0x8001b970) (i := i) (by omega), hw]
  unfold impureByte
  rw [Nat.add_sub_cancel_left]

section Own

open Iris Iris.BI Iris.Std Iris.ProofMode

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- **Open** the bytes `R` of newlib's exclusive data, keeping the image and
`_impure_ptr`. -/
theorem stdioAt_open (P : (Nat → BitVec 8) → Prop) (R : Nat → Prop) :
    stdioAt (GF := GF) P ⊢ ∃ img, ⌜P img ∧ ImpureImg img⌝ ∗
      ownSet (fun k => stdioExcl k ∧ R k) (fun k => k ↦ₘ img k) ∗
      ownSet (fun k => stdioExcl k ∧ ¬ R k) (fun k => k ↦ₘ img k) ∗ impureRO := by
  unfold stdioAt
  iintro ⟨%img, %hp, H, #Hr⟩
  iexists img
  ihave ⟨H1, H2⟩ := ownSet_split stdioExcl R _ $$ H
  iframe H1 H2 Hr
  ipureintro; exact hp

/-- **Close** them again, at the same image. -/
theorem stdioAt_close (P : (Nat → BitVec 8) → Prop) (R : Nat → Prop) (img : Nat → BitVec 8)
    (hp : P img) (hi : ImpureImg img) :
    ownSet (GF := GF) (fun k => stdioExcl k ∧ R k) (fun k => k ↦ₘ img k) ∗
      ownSet (fun k => stdioExcl k ∧ ¬ R k) (fun k => k ↦ₘ img k) ∗ impureRO ⊢ stdioAt P := by
  unfold stdioAt
  iintro ⟨H1, H2, #Hr⟩
  iexists img
  iframe Hr
  isplitr
  · ipureintro; exact ⟨hp, hi⟩
  ihave H := ownSet_join _ _ _
    (fun k (h1 : stdioExcl k ∧ R k) (h2 : stdioExcl k ∧ ¬ R k) => h2.2 h1.2) $$ [H1 H2]
  · iframe H1 H2
  iapply ownSet_iff _ _ $$ H
  intro k; constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro h; by_cases hr : R k
    · exact .inl ⟨h, hr⟩
    · exact .inr ⟨h, hr⟩

end Own

end VsaIris.Stdio
