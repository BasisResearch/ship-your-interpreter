import Vsa.Sim.rows.EntryGroundRows
import Vsa.Sim.EvalNotSim
import Vsa.Sim.rows.TransportValue_intRange
import Vsa.Sim.Code.FixedImage_Eval_expr
import Vsa.Sim.Code.FixedImage_Value_int
import Vsa.Sim.Code.FixedImage_Value_bool
import Vsa.Sim.Code.FixedImage_Value_str
import Vsa.Sim.Code.FixedImage_Value_truthy
import Vsa.Sim.Code.FixedImage_Value_null

namespace Vsa.Sim
open LeanRV64DExecutable Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.Sim.Code

/-- The fixed rodata image supplies the existing eval jump-table byte manifest. -/
theorem fixedRodata_evalTableBytes {m : Mem} (h : FixedRodataLoaded m) :
    ∀ off b, (off, b) ∈ Rows.kindTableBytes →
      m[jumpTableBase + off]? = some (BitVec.ofNat 8 b) := by
  have checked : ∀ p ∈ Rows.kindTableBytes,
      p.1 < 44 ∧ fixedRodataByte (0x1378 + p.1) = BitVec.ofNat 8 p.2 := by decide
  intro off b hm
  have hc := checked (off, b) hm
  have hb := h (0x1378 + off) (by change 0x1378 + off < 8464; omega)
  change m[(0x80018be0 : Nat) + (0x1378 + off)]? =
    some (fixedRodataByte (0x1378 + off)) at hb
  have ha : (0x80018be0 : Nat) + (0x1378 + off) = jumpTableBase + off := by
    simp only [jumpTableBase]; omega
  rw [ha] at hb
  exact hb.trans (congrArg some hc.2)

/-- Initial fixed-image data and protected geometry supply all eval-call pins.
The initial store and arena protection supply the arena exclusion argument. -/
theorem evalCallSupport_of_fixedImage {m : Mem} {SL : StackLayout} {A : Arena}
    (sp : BitVec 64) (htext : FixedTextLoaded m) (hrodata : FixedRodataLoaded m)
    (hstack : tohostAddr + 16 ≤ SL.lo)
    (harena : A.hi ≤ 0x80000000 ∨ 0x8001acf0 ≤ A.lo) :
    EvalCallSupport m SL A sp := by
  have hs : 0x8001ad10 ≤ SL.lo := hstack
  have hImage : StaticImageSupport m SL A :=
    { text := htext
      rodata := hrodata
      stack := Or.inr (by omega)
      arena := harena }
  refine { image := hImage, pins := ?_ }
  intro m' hag
  have hImage' := hImage.transport hag
  have hb := fixedRodata_evalTableBytes hImage'.rodata
  refine ⟨hImage'.text.Eval_exprLoaded, hImage'.text.Value_intLoaded,
    hImage'.text.Value_truthyLoaded, ?_, ?_, Rows.kindTablePins_of_bytes hb⟩
  · exact ⟨hb 0 0xb0 (by decide), hb 1 0x94 (by decide),
      hb 2 0xfe (by decide), hb 3 0xff (by decide)⟩
  · refine
      { null_code := hImage'.text.Value_nullLoaded
        bool_code := hImage'.text.Value_boolLoaded
        str_code := hImage'.text.Value_strLoaded
        null_slot := ⟨hb 12 0xd4 (by decide), hb 13 0x94 (by decide),
          hb 14 0xfe (by decide), hb 15 0xff (by decide)⟩
        bool_slot := ⟨hb 8 0xc8 (by decide), hb 9 0x94 (by decide),
          hb 10 0xfe (by decide), hb 11 0xff (by decide)⟩
        str_slot := ⟨hb 4 0xbc (by decide), hb 5 0x94 (by decide),
          hb 6 0xfe (by decide), hb 7 0xff (by decide)⟩ }

#print axioms fixedRodata_evalTableBytes
#print axioms evalCallSupport_of_fixedImage
end Vsa.Sim
