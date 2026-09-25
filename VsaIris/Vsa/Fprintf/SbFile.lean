import VsaIris.Vsa.Fprintf.Flush
import VsaIris.Vsa.SymCompact

/-!
# The memory after a loop-bearing call; `__sbprintf`'s `FILE` (lane N5)

A call whose effect depends on its data (`__sfvwrite_r`'s copy/flush loop)
cannot hand its caller an explicit write log. It hands back the caller's
memory with its footprint regions replaced by some bytes `g` (`fillR`, N3's
`SymCompact.lean`), together with named facts about the new contents. Loads
outside the regions read through to the caller's memory (`nx_mem` below
peels each region with `ldv_*_fillR_miss`), loads inside meet the facts.

`SbFile M f pend` is `__sbprintf`'s stack `FILE` at `f` (buffer at
`f + 184`) holding the pending bytes `pend`: the fields `_vfprintf_r`,
`__sfvwrite_r` and `_fflush_r` load, as load values of `M`.
-/

namespace VsaIris.Sym.Fp

open Vsa.Sim Vsa.MemRepr VsaIris.Sym VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio

/-- Store forwarding through `fillR` regions too (a load off a region reads
the memory below it). -/
macro_rules
  | `(tactic| nx_mem) => `(tactic| simp (disch := nx_addr) only [ldv_store_hit, ldv_ld_hit_eq,
      ldv_ld_miss, ldv_lw_miss, ldv_lw_store8, ldv_lw_hit, ldv_lh_hit, ldv_lhu_hit, ldv_lbu_hit,
      ldv_lh_miss, ldv_lhu_miss, ldv_lbu_miss, ldv_lwu_miss, ldv_ld_fillR_miss, ldv_lw_fillR_miss,
      ldv_lwu_fillR_miss, ldv_lh_fillR_miss, ldv_lhu_fillR_miss, ldv_lbu_fillR_miss])

/-- A load is determined by the bytes it reads. -/
theorem ldv_agree {k : MKind} {M M' : Mem} {a : Nat}
    (h : ∀ j, j < widthOfM k → imgM M' (a + j) = imgM M (a + j)) : ldv k M' a = ldv k M a := by
  unfold ldv bytesAt
  congr 1
  refine List.map_congr_left fun j hj => ?_
  exact h j (List.mem_range.mp hj)

/-- **`__sbprintf`'s stack `FILE`** at `f` with `pend` buffered (at most 1023
bytes: a full buffer is flushed at once). -/
structure SbFile (M : Mem) (f : BitVec 64) (pend : List (BitVec 8)) : Prop where
  len : pend.length < 1024
  p : ldv .ld M f.toNat = f + 184#64 + BitVec.ofNat 64 pend.length
  w : ldv .lw M (f + 12#64).toNat = BitVec.ofNat 64 (1024 - pend.length)
  flags : ldv .lh M (f + 16#64).toNat = 0x2008#64
  flagsU : ldv .lhu M (f + 16#64).toNat = 0x2008#64
  base : ldv .ld M (f + 24#64).toNat = f + 184#64
  size : ldv .lw M (f + 32#64).toNat = 1024#64
  cookie : ldv .ld M (f + 48#64).toNat = 0x8001bb20#64
  writer : ldv .ld M (f + 64#64).toNat = 0x8000efd4#64
  flags2 : ldv .lw M (f + 176#64).toNat = 0#64
  buf : ∀ i (h : i < pend.length), imgM M ((f + 184#64).toNat + i) = pend[i]

end VsaIris.Sym.Fp
