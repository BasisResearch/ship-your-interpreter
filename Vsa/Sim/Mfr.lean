import Vsa.Sim.MfrAttr
import Vsa.Sim.SnprintfSpec5
import Vsa.Sim.CodeRangeInsert

/-!
# `mfr` — the memory-frame simp set

Tags the disjointness-conditional "reads survive this write" rules so a batch
of byte-pin survival obligations discharges with one bounded call instead of a
`rw [getElem?_writeMap8_out _ _ _ _ (by omega)]` chain per write:

```lean
simp (disch := omega) only [mfr]
```

`simp only` with a fixed set: no search, no unfolding. Each rule's LHS is a
read of a written map (`writeMap8`/`writeMap4`/`insert`) and every variable of
the disjointness side condition occurs in the LHS, so `disch := omega` closes
the side condition from numerals and context hypotheses; where the read hits
the written window the discharge fails and simp skips that occurrence, leaving
it for the readback lemma.

Included:
* `getElem?_writeMap8_out` (SnprintfSpec5) — `(writeMap8 mem k d)[a]? = mem[a]?`
  given `a < k ∨ k + 8 ≤ a`;
* `getElem?_writeMap4_out` (below) — the 4-byte twin, derived from
  `getElem?_writeMap4_outside` (CodeRangeInsert) at the point interval `[a,a+1)`;
* `getElem?_insert_out` (below) — `(mem.insert k v)[a]? = mem[a]?` given
  `a ≠ k`; the omega-dischargeable form of `Std.ExtHashMap.getElem?_insert`.

Excluded (verified to misfire as simp rules — do not add back without a test):
* `getElem?_insert_outside` / `getElem?_writeMap8_outside` /
  `getElem?_writeMap4_outside` (CodeRangeInsert): the interval bounds `lo`/`hi`
  occur only in the hypotheses, not in the LHS, so simp cannot instantiate
  them — the side conditions reach the discharger with metavariables and
  `omega` fails on every occurrence. Keep using them explicitly applied
  (`simp only [getElem?_insert_outside LO HI …]`) as CodeRangeInsert documents.
* `Std.ExtHashMap.getElem?_insert`: unconditional — it rewrites every insert
  read to an `if k == a then …`, including the pins that should *not* be
  framed, and leaves the `if` for a separate `if_neg` pass instead of
  discharging disjointness. Superseded by `getElem?_insert_out`.
* `slotHolds_writeMap8` / `slotHolds_insert` (SnprintfSpec5): their major
  premise `SlotHolds … mem` is a Prop, not an arithmetic side condition —
  `disch := omega` can never supply it. Apply them by name.
-/

open LeanRV64DExecutable Vsa

namespace Vsa.Sim

/-- Reads at any other key are unchanged by a single byte insert (the
omega-dischargeable rewrite form of `Std.ExtHashMap.getElem?_insert`). -/
theorem getElem?_insert_out (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat)
    (v : BitVec 8) (a : Nat) (ha : a ≠ k) :
    (mem.insert k v)[a]? = mem[a]? := by
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]

/-- Reads outside a 4-byte `writeMap4` window are unchanged (the `writeMap4`
twin of `getElem?_writeMap8_out`). -/
theorem getElem?_writeMap4_out (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat)
    (d : BitVec (8 * 4)) (a : Nat) (ha : a < k ∨ k + 4 ≤ a) :
    (writeMap4 mem k d)[a]? = mem[a]? :=
  getElem?_writeMap4_outside a (a + 1) mem k d (by omega) a (Nat.le_refl a) (by omega)

attribute [mfr]
  getElem?_writeMap8_out   -- 8-byte store frame (SnprintfSpec5)
  getElem?_writeMap4_out   -- 4-byte store frame
  getElem?_insert_out      -- single byte-insert frame

end Vsa.Sim
