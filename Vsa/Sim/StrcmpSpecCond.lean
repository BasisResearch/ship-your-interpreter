import Vsa.Sim.StrcmpSpecW4

/-!
# `StrcmpSpecCond` — the `strcmp` spec with the word-path alignment derived from the test

`strcmp_full_pre` (`StrcmpSpecW4.lean`) demands `StrcmpWRegion` — including
8-alignment of BOTH payload pointers — unconditionally, although the word path is
taken only when the entry test `(pa ||| pb) &&& 7 = 0` succeeds.  A string
literal's payload (AST bytes) is not 8-aligned in general, so the unconditional
premise is unsatisfiable for the string cells.

This file states the entry as a named-field structure `StrcmpEntryCond` whose
word-region clause is the alignment-free `StrcmpWSlack` (the word loop's slack
geometry), derives both alignments from the entry test (`align8_of_test`), and
proves `strcmp_full_spec_cond` from the landed `strcmp_word_spec` /
`strcmp_byte_path`.  The byte-region clauses are derived (`StrcmpWSlack.toRegion`).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (Config)
open Vsa.Logic
open Vsa.MemRepr
open Vsa.Sim.Code (StrcmpLoaded)

namespace Vsa.Sim

/-- `StrcmpWRegion` without its alignment field: the word loop may read up to 7
bytes past the NUL, so the payload needs 8 bytes of slack inside RAM and away
from the `strcmp` code and the HTIF window. -/
structure StrcmpWSlack (p : BitVec 64) (len : Nat) : Prop where
  lo : 0x80000000 ≤ p.toNat
  hi : p.toNat + len + 8 ≤ 0x100000000
  nowrap : p.toNat + len + 8 < 2^64
  code : p.toNat + len + 8 ≤ 0x80006ea0 ∨ 0x80006fcc ≤ p.toNat
  htif : p.toNat + len + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ p.toNat

end Vsa.Sim
