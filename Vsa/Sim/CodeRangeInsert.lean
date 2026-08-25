import Vsa.Sim.SnprintfSpec5

/-!
# `CodeRangeInsert` — generic `…Loaded`-under-write preservation

Every code byte-pin file (`Code/Memmove.lean`, `Code/Strcpy.lean`, …) needs
"the pins survive data writes": each spec file has so far hand-rolled its own
`getElem?_insert_above*` + `X_insert` lemma pair.  The generic pieces below
close that per-file duplication: the code region is an interval `[lo, hi)`,
and any write whose key set misses the interval preserves every read in it.

Recipe for a new `XLoaded` preservation lemma (the 40×-faster pattern):

```lean
theorem x_insert (mem …) (k v) (hk : k < LO ∨ HI ≤ k) (h : XLoaded mem) :
    XLoaded (mem.insert k v) := by
  unfold XLoaded xChunk0 xChunk1 … at h ⊢
  simp (disch := omega) only [getElem?_insert_outside LO HI mem k v hk]
  exact h
```

where `LO`/`HI` are the region's literal bounds — `simp`'s discharger closes
the per-pin `LO ≤ a ∧ a < HI` side conditions by `omega`.  `writeMap8` /
`writeMap4` stores are 8/4 chained inserts; use the `_writeMap8` / `_writeMap4`
variants the same way, or apply the single-insert lemma 8/4 times.
-/

open LeanRV64DExecutable Vsa

namespace Vsa.Sim

/-- Reads inside `[lo, hi)` are unchanged by an insert whose key is outside. -/
theorem getElem?_insert_outside (lo hi : Nat) (mem : Std.ExtHashMap Nat (BitVec 8))
    (k : Nat) (v : BitVec 8) (hk : k < lo ∨ hi ≤ k)
    (a : Nat) (ha1 : lo ≤ a) (ha2 : a < hi) :
    (mem.insert k v)[a]? = mem[a]? := by
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]

/-- Reads inside `[lo, hi)` are unchanged by an 8-byte store whose window is
outside. -/
theorem getElem?_writeMap8_outside (lo hi : Nat) (mem : Std.ExtHashMap Nat (BitVec 8))
    (k : Nat) (d : BitVec (8 * 8)) (hk : k + 8 ≤ lo ∨ hi ≤ k)
    (a : Nat) (ha1 : lo ≤ a) (ha2 : a < hi) :
    (writeMap8 mem k d)[a]? = mem[a]? :=
  getElem?_writeMap8_out mem k d a (by omega)

/-- Reads inside `[lo, hi)` are unchanged by a 4-byte store whose window is
outside. -/
theorem getElem?_writeMap4_outside (lo hi : Nat) (mem : Std.ExtHashMap Nat (BitVec 8))
    (k : Nat) (d : BitVec (8 * 4)) (hk : k + 4 ≤ lo ∨ hi ≤ k)
    (a : Nat) (ha1 : lo ≤ a) (ha2 : a < hi) :
    (writeMap4 mem k d)[a]? = mem[a]? := by
  show ((((mem.insert k _).insert (k+1) _).insert (k+2) _).insert (k+3) _)[a]? = mem[a]?
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]

end Vsa.Sim
