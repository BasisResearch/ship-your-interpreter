import Vsa.Sim.StrlenSpec
import Vsa.Sim.ObsAvoid

/-!
# Layer 3 — `strlen` unaligned head-peel + full spec (`strlen_full_spec`)

Completes the `strlen` total-correctness spec for the **unaligned** entry path
(`bnez a5` taken at `0xcf8` → `0xd78`), and assembles the top-level
`strlen_full_spec` that dispatches on `p.toNat % 8 = 0`.

This file is purely additive over the verified `Vsa/Sim/StrlenSpec.lean` (whose
aligned `strlen_spec` and the three head transitions `head_body`/`head_nul_exit`/
`head_continue` are reused unchanged).

## Control flow (unaligned path), from the disassembly

* entry `0xcf0..0xcf8`: `andi a5,a0,7; mv a4,a0; bnez a5,d78` — TAKEN (unaligned),
  jumping directly to `0xd78` with `a0 = a4 = base`.
* head peel `0xd78..0xd84`: `lbu a5,0(a4); addi a4,a4,1; andi a3,a4,7; bnez a5,d74`.
* `0xd74 beqz a3`: alignment test on the ADVANCED pointer `base+(m+1)`.  Taken
  (aligned) rejoins the aligned scan at `0xcfc` (`a0 = base`, `a4 = base+off0`
  8-aligned, `off0 = m+1`); not taken loops back to `0xd78`.
* NUL-in-head exit `0xd88..0xd90`: `sub a4,a4,a0; addi a0,a4,-1; ret`, returning
  `a0 = m = len`.

## Two segments

1. **Head loop** (`Triple.loop`): from the unaligned entry, peel bytes until either
   the NUL is found (→ `Done`) or 8-alignment is reached (→ the rejoin config at
   `0xcfc`).
2. **Offset-generalized word scan**: from the rejoin config, scan 8-aligned words
   starting at `q = base + off0` with `a0 = base` (`≠ q` in general).  This clones
   the aligned word-loop/tail machinery with a `base`/`off0` split.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.MemRepr
open Vsa.Sim.Code (StrlenLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Unaligned entry (`0xcf0 → 0xd78`)

`UPre`: entry precondition for the unaligned path (`p.toNat % 8 ≠ 0`).  Runs
`andi a5,a0,7` (`a5 = p & 7 ≠ 0`), `mv a4,a0` (`a4 = p`), `bnez a5` TAKEN → `0xd78`,
establishing the head-loop head `HSt p r len cs m0 0`. -/

/-- For an unaligned `p`, `p &&& sext(0x007) ≠ 0` (some low bit set). -/
theorem andi7_unaligned (p : BitVec 64) (halign : p.toNat % 8 ≠ 0) :
    (p &&& sign_extend (m := 64) (0x007#12)) ≠ 0#64 := by
  intro h
  apply halign
  have : (p &&& sign_extend (m := 64) (0x007#12)).toNat = 0 := by rw [h]; rfl
  rw [BitVec.toNat_and, show (sign_extend (m := 64) (0x007#12) : BitVec 64).toNat = 7 from by decide,
    show (7:Nat) = 2^3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    show (2:Nat)^3 = 8 from rfl] at this
  exact this

/-! ## Alignment-exit rejoin config (`0xcfc`)

`HAlign base r len cs m0 off0`: the config at `0xcfc` after peeling `off0 = m+1`
bytes and finding the pointer `base+off0` 8-aligned (`(base+off0) % 8 = 0`), with no
NUL in `[base, base+off0)` (so `off0 ≤ len`).  Here `a0 = base` (the length origin),
`a4 = base+off0` (the aligned scan base `q`), and `x1 = r`.  From here the magic setup
and word loop scan the rest — but with `a0 = base ≠ a4` in general. -/

/-! ## Head NUL-exit to the pre-`ret` state

`head_nul_exit` bundles the `ret`; for the loop we need to stop at a PC distinct from
the head (`0xd78`) and from `r`, so we peel only up to the pre-`ret` `AtRet` state at
`0xd90` (`sub a4,a4,a0; addi a0,a4,-1`).  The `ret` is run once after the loop. -/

/-! ## Head-loop assembly (`Triple.loop`)

Invariant `HLoopI`: at the head `0xd78` (some peel-count `m`, `m ≤ len`), or at the
pre-`ret` NUL-exit state `0xd90` (`AtRet`), or rejoined the aligned scan at `0xcfc`
(`HAlign off0`).  All three PCs are distinct literals, so the measure — `len + 1 - m`
at the head, else `0` — is provably `0` on the two exit disjuncts.  Guard `HLoopB`: at
the head.  The body runs one `head_body`, then dispatches: NUL (`m = len`) → `AtRet`;
aligned → `HAlign`; else → `HSt (m+1)` (measure drops). -/

/-! ## Offset-generalized word scan (`0xcfc → Done`)

From `HAlign base r len cs m0 off0` (at `0xcfc`, `a0 = base`, `a4 = base+off0`,
`(base+off0) % 8 = 0`, `off0 ≤ len`), the magic setup runs then the word loop scans
8-aligned words starting at `q = base+off0`.  This clones the aligned word-loop/tail
machinery decoupling `a0 = base` (length origin) from the scan base `q`.  The string
facts are about `base`; scan positions are `off0 + 8j`.  Setting `off0 = 0`, `base = q`
recovers the aligned spec — so the arithmetic is identical modulo the `off0` shift.

We phrase the scan positions via a single index `t = off0 + 8j` (bytes scanned from
`base`).  The load, detection, and exit arithmetic all read `t`. -/

/-! ### Generalized word-loop states

`WStG base r len cs m0 off0 j`: word-loop head `0xd10`, scan position `base + (off0+8j)`,
`a0 = base`, `a4 = base + ofNat(off0+8j)`.  `t = off0+8j` is the byte index from `base`.
`W28G`, `WTailG` mirror the aligned `W28`/`WTail` with the `base`/`off0` split. -/

/-- `(base + ofNat(off0+8j)) + sext 8 = base + ofNat(off0+8(j+1))`. -/
theorem a4_incrG (base : BitVec 64) (off0 j : Nat) :
    (base + BitVec.ofNat 64 (off0+8*j)) + sign_extend (m := 64) (0x008#12)
      = base + BitVec.ofNat 64 (off0+8*(j+1)) := by
  rw [show (sign_extend (m := 64) (0x008#12) : BitVec 64) = BitVec.ofNat 64 8 from by
        apply BitVec.eq_of_toNat_eq; decide, BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2

/-! ### Generalized word-loop assembly (`Triple.loop`) -/

/-! ### Magic setup from the alignment rejoin (`0xcfc → 0xd10`)

From `HAlign base r len cs m0 off0` (at `0xcfc`, `a0 = base`, `a4 = base+off0`), the magic
setup `lui/addi/slli/add/li` builds `a3 = magic7f`, `a1 = allOnes` (leaving `a0`, `a4`
untouched), landing at the word-loop head `WStG off0 0` (`a4 = base+off0 = base+(off0+8·0)`). -/

/-! ### Generalized byte tail (`WTailG → Done`)

Mirrors the aligned `WTail → Done`, with `a0 = base` (length origin), scan base
`q = base+off0`, `a4 = base + ofNat(off0+8(j+1))`.  The `sub a3,a4,a0` gives
`a3 = ofNat(off0+8(j+1))` and the exit `addi a0,a3,-(8-k)` computes
`off0+8(j+1)-(8-k) = off0+8j+k = len`.  Byte at tail offset `k` is the string byte at
index `off0+8j+k` from `base`.  We phrase the tail via the byte index `t = off0+8j`. -/

/-! ### Generalized tail `beqz` exits (→ `Done`) and advances (→ next offset) -/

/-- Generalized `snez`-path arithmetic: `snez_val + ofNat(off0+8(j+1)) + sext(-2) = ofNat len`. -/
theorem snez_finalG (off0 j len : Nat) (b6 : BitVec 8)
    (hlo : off0 + 8*j + 5 < len) (hhi : len < off0 + 8*(j+1)) (hnw : off0 + 8*(j+1) + 8 < 2^64)
    (hb6 : b6 = 0 ↔ off0 + 8*j + 6 = len) :
    (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (zero_extend (m := 64) b6)))
      + BitVec.ofNat 64 (off0+8*(j+1))) + sign_extend (m := 64) (0xffe#12) = BitVec.ofNat 64 len := by
  have hsext : (sign_extend (m := 64) (0xffe#12) : BitVec 64) = -(BitVec.ofNat 64 2) := by
    apply BitVec.eq_of_toNat_eq; decide
  have hsnez : (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (zero_extend (m := 64) b6)))).toNat
      = (if b6 = 0 then 0 else 1) := snez_toNat b6
  -- the snez value's toNat, bounded and pinned by `hsnez`
  have hsvlt : (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (zero_extend (m := 64) b6)))).toNat < 2 := by
    rw [hsnez]; by_cases h : b6 = 0
    · simp only [if_pos h]; decide
    · simp only [if_neg h]; decide
  have hval : (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (zero_extend (m := 64) b6)))).toNat + (off0+8*(j+1)) - 2 = len := by
    rw [hsnez]
    by_cases h : b6 = 0
    · have := hb6.mp h; simp only [if_pos h]; omega
    · have hne : ¬ (off0 + 8*j + 6 = len) := fun hc => h (hb6.mpr hc); simp only [if_neg h]; omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, hsext, BitVec.toNat_neg]
  have h2 : (2#64 : BitVec 64).toNat = 2 := rfl
  rw [h2, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show len < 2^64 from by omega),
    Nat.mod_eq_of_lt (show off0+8*(j+1) < 2^64 from by omega),
    Nat.mod_eq_of_lt (show (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (zero_extend (m := 64) b6)))).toNat + (off0+8*(j+1)) < 2^64 from by omega)]
  have hm2 : (2^64 - 2) % 2^64 = 2^64 - 2 := Nat.mod_eq_of_lt (by omega)
  rw [hm2]
  rw [show (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (zero_extend (m := 64) b6)))).toNat + (off0+8*(j+1)) + (2^64 - 2) = len + 2^64 from by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (show len < 2^64 from by omega)]

/-! ### Generalized byte-tail assembly (`WTailG → Done`) -/

/-! ## Unaligned path assembly (`UPre → Done`) and `strlen_full_spec`

The head loop exits to `AtRet 0xd90 ∨ HAtAlign`; the NUL-exit `ret` (`AtRet → Done`)
and the alignment-exit word scan (`HAlign → Done`) both land in `Done`. -/

/-! ## Top-level full spec (`strlen_full_spec`)

`Triple.cases` over the `0xcf0` alignment test unifies the aligned fast path
(`strlen_spec`) and the unaligned head-peel path (`strlen_unaligned_spec`).  The shared
precondition `strlen_full_pre` omits the alignment guard (the machine decides it); both
paths share the postcondition `strlen_post`. -/

end Vsa.Sim
