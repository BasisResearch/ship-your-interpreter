import VsaIris.Vsa.Stdout.Console

/-!
# `stderr` at the boundary, as loads (lane N3)

`ConsoleMt` (lane N1) for `stderr` (`__sf[2]`, `0x8001bbd8`): the fields its
first write reads, from `StdioOK`'s `ExitIdleFile` (flags `__SRW | __SNBF`,
descriptor 2, cookie, lock) and `StderrStream` (`_bf._base = NULL`,
`_write = __swrite`).
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio
open LeanRV64DExecutable LeanRV64DExecutable.Functions

/-- The `stderr` fields a first write loads, as load values of `Mt`. -/
structure ErrMt (Mt : Mem) : Prop where
  /-- `_flags` (`__SRW | __SNBF`) -/
  flagsU : ldv .lhu Mt 0x8001bbe8 = 0x12#64
  flagsS : ldv .lh Mt 0x8001bbe8 = 0x12#64
  /-- `_file` -/
  fd : ldv .lh Mt 0x8001bbea = 2#64
  /-- `_bf._base` -/
  base : ldv .ld Mt 0x8001bbf0 = 0#64
  /-- `_cookie` -/
  cookie : ldv .ld Mt 0x8001bc08 = 0x8001bbd8#64
  /-- `_write` -/
  writer : ldv .ld Mt 0x8001bc18 = 0x8000efd4#64
  /-- `_lock` -/
  lock : ldv .ld Mt 0x8001bc78 = 0#64
  /-- `_flags2` -/
  lockMode : ldv .lw Mt 0x8001bc88 = 0#64

/-- **`stderr` at the boundary, as loads.** -/
theorem errMt_of {img : Nat → BitVec 8} (h : StdioOK img) {Mt : Mem}
    (hM : ∀ a, stdioFoot a → ¬ impureW a → imgM Mt a = img a) : ErrMt Mt := by
  obtain ⟨_, he, _, _, hs⟩ := h.facts
  have F : ∀ a n, 0x8001ba68 ≤ a → a + n ≤ 0x8001c168 → ∀ i, i < n →
      stdioFoot (a + i) ∧ ¬ impureW (a + i) := by
    intro a n h1 h2 i hi; unfold stdioFoot InRange impureW; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ldv_lhu_of_imgLE (stdio_imgLE hM he.stderr.flags_read (F _ _ (by decide) (by decide)))
  · exact (ldv_lh_of_imgLE (stdio_imgLE hM he.stderr.flags_read (F _ _ (by decide) (by decide)))).trans
      (by decide)
  · exact (ldv_lh_of_imgLE (stdio_imgLE hM he.stderr.descriptor_read (F _ _ (by decide) (by decide)))).trans
      (by decide)
  · exact ldv_ld_of_imgLE (stdio_imgLE hM hs.base (F _ _ (by decide) (by decide)))
  · exact ldv_ld_of_imgLE (stdio_imgLE hM he.stderr.cookie (F _ _ (by decide) (by decide)))
  · exact ldv_ld_of_imgLE (stdio_imgLE hM hs.writer (F _ _ (by decide) (by decide)))
  · exact ldv_ld_of_imgLE (stdio_imgLE hM he.stderr.lock (F _ _ (by decide) (by decide)))
  · exact (ldv_lw_of_imgLE (stdio_imgLE hM he.stderr.lockMode (F _ _ (by decide) (by decide)))).trans
      (by decide)

end VsaIris.Sym
