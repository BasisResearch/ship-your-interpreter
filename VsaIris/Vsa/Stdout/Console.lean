import VsaIris.Vsa.Stdout.Mem
import VsaIris.Vsa.StdioRead
import VsaIris.Vsa.ImpureRO

/-!
# `stdout` at the boundary, as loads (lane N1)

`StdioOK img` (H5) pins `stdout`'s `FILE` through VSA's `ConsoleStream`.
A stdout run reads those fields with `ld`/`lw`/`lh`/`lhu` from its tracking
memory `Mt`, which agrees with `img` on `stdioFoot`. `ConsoleMt Mt` states
each field as the load value `ix_run` rewrites with; `consoleMt_of` derives it.
The addresses are literals: `stdout = 0x8001bb20`, `_impure_data = 0x8001b538`.
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio
open LeanRV64DExecutable LeanRV64DExecutable.Functions

/-- The `stdout` fields a write path loads, as load values of `Mt`. -/
structure ConsoleMt (Mt : Mem) : Prop where
  /-- `_impure_data.__cleanup` (`__sinit` has run) -/
  sinit : ldv .ld Mt 0x8001b580 = 0x80005d2c#64
  /-- `_impure_data._stdout` -/
  stdout : ldv .ld Mt 0x8001b548 = 0x8001bb20#64
  /-- `_p` -/
  p : ldv .ld Mt 0x8001bb20 = 0x8001bb97#64
  /-- `_w` -/
  w : ldv .lw Mt 0x8001bb2c = 0#64
  /-- `_flags` (`__SWR | __SNBF | __SORD`) -/
  flagsU : ldv .lhu Mt 0x8001bb30 = 0x200a#64
  flagsS : ldv .lh Mt 0x8001bb30 = 0x200a#64
  /-- `_file` -/
  fd : ldv .lh Mt 0x8001bb32 = 1#64
  /-- `_bf._base` -/
  base : ldv .ld Mt 0x8001bb38 = 0x8001bb97#64
  /-- `_bf._size` -/
  bsize : ldv .lw Mt 0x8001bb40 = 1#64
  /-- `_lbfsize` -/
  lbf : ldv .lw Mt 0x8001bb48 = 0#64
  /-- `_cookie` -/
  cookie : ldv .ld Mt 0x8001bb50 = 0x8001bb20#64
  /-- `_write` -/
  writer : ldv .ld Mt 0x8001bb60 = 0x8000efd4#64
  /-- `_lock` -/
  lock : ldv .ld Mt 0x8001bbc0 = 0#64
  /-- `_flags2` -/
  lockMode : ldv .lw Mt 0x8001bbd0 = 0#64

theorem stdio_imgLE {img : Nat → BitVec 8} {Mt : Mem}
    (hM : ∀ a, stdioFoot a → ¬ impureW a → imgM Mt a = img a) {a n v : Nat}
    (hr : readLE (fillMem img dataList) a n = some v)
    (hin : ∀ i, i < n → stdioFoot (a + i) ∧ ¬ impureW (a + i)) :
    imgLE (imgM Mt) a n = v := by
  have h := readLE_memImg hr
  rw [← h]
  refine imgLE_congr fun i hi => ?_
  rw [hM _ (hin i hi).1 (hin i hi).2]
  unfold memImg
  rw [fillMem_get img (mem_dataList (hin i hi).1)]
  rfl

theorem ldv_ld_of_imgLE {Mt : Mem} {a v : Nat} (h : imgLE (imgM Mt) a 8 = v) :
    ldv .ld Mt a = BitVec.ofNat 64 v := ldvf_ld_imgLE h

theorem ldv_lw_of_imgLE {Mt : Mem} {a v : Nat} (h : imgLE (imgM Mt) a 4 = v) :
    ldv .lw Mt a = sign_extend (m := 64) (BitVec.ofNat 32 v) := by rw [ldv_lw_img, h]

theorem ldv_lh_of_imgLE {Mt : Mem} {a v : Nat} (h : imgLE (imgM Mt) a 2 = v) :
    ldv .lh Mt a = sign_extend (m := 64) (BitVec.ofNat 16 v) := by rw [ldv_lh_img, h]

theorem ldv_lhu_of_imgLE {Mt : Mem} {a v : Nat} (h : imgLE (imgM Mt) a 2 = v) :
    ldv .lhu Mt a = BitVec.ofNat 64 v := by rw [ldv_lhu_img, h]

/-- **`stdout` at the boundary, as loads.** -/
theorem consoleMt_of {img : Nat → BitVec 8} (h : StdioOK img) {Mt : Mem}
    (hM : ∀ a, stdioFoot a → ¬ impureW a → imgM Mt a = img a) : ConsoleMt Mt := by
  obtain ⟨hc, _, _⟩ := h.facts
  have F : ∀ a n, 0x8001b520 ≤ a → a + n ≤ 0x8001b538 ∨ (0x8001b53c ≤ a ∧ a + n ≤ 0x8001b960) ∨
      (0x8001b978 ≤ a ∧ a + n ≤ 0x8001b990) ∨ (0x8001ba68 ≤ a ∧ a + n ≤ 0x8001c168) →
      ∀ i, i < n → stdioFoot (a + i) ∧ ¬ impureW (a + i) := by
    intro a n h1 h2 i hi; unfold stdioFoot InRange impureW; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ldv_ld_of_imgLE (stdio_imgLE hM hc.sinit (F _ _ (by decide) (by decide)))
  · exact ldv_ld_of_imgLE (stdio_imgLE hM hc.stdout (F _ _ (by decide) (by decide)))
  · exact ldv_ld_of_imgLE (stdio_imgLE hM hc.cursor (F _ _ (by decide) (by decide)))
  · exact (ldv_lw_of_imgLE (stdio_imgLE hM hc.writeCount (F _ _ (by decide) (by decide)))).trans (by decide)
  · exact ldv_lhu_of_imgLE (stdio_imgLE hM hc.flags (F _ _ (by decide) (by decide)))
  · exact (ldv_lh_of_imgLE (stdio_imgLE hM hc.flags (F _ _ (by decide) (by decide)))).trans (by decide)
  · exact (ldv_lh_of_imgLE (stdio_imgLE hM hc.fd (F _ _ (by decide) (by decide)))).trans (by decide)
  · exact ldv_ld_of_imgLE (stdio_imgLE hM hc.base (F _ _ (by decide) (by decide)))
  · exact (ldv_lw_of_imgLE (stdio_imgLE hM hc.bufSize (F _ _ (by decide) (by decide)))).trans (by decide)
  · exact (ldv_lw_of_imgLE (stdio_imgLE hM hc.lineBufSize (F _ _ (by decide) (by decide)))).trans (by decide)
  · exact ldv_ld_of_imgLE (stdio_imgLE hM hc.cookie (F _ _ (by decide) (by decide)))
  · exact ldv_ld_of_imgLE (stdio_imgLE hM hc.writer (F _ _ (by decide) (by decide)))
  · exact ldv_ld_of_imgLE (stdio_imgLE hM hc.lock (F _ _ (by decide) (by decide)))
  · exact (ldv_lw_of_imgLE (stdio_imgLE hM hc.lockMode (F _ _ (by decide) (by decide)))).trans (by decide)

/-- `_impure_ptr` as a persistent data view (`impureRO`). -/
def impDt : Mem := fillMem impureByte (List.range' 0x8001b970 8)

theorem ldv_impDt : ldv .ld impDt 0x8001b970 = 0x8001b538#64 := by
  have e : ∀ j, j < 8 → imgM impDt (0x8001b970 + j) = impureByte (0x8001b970 + j) := fun j hj => by
    unfold imgM impDt
    rw [fillMem_get impureByte (List.mem_range'.mpr ⟨j, hj, by simp⟩)]; rfl
  have h : imgLE (imgM impDt) 0x8001b970 8 = 0x8001b538 := by
    rw [imgLE_congr (img' := impureByte) e]; decide
  exact ldvf_ld_imgLE h

end VsaIris.Sym
