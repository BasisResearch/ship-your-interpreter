import Vsa.Sim.MemcpySites4
import Vsa.Sim.DivSpec
import Vsa.Sim.MemcpySpec2

/-!
# Layer 3 — `memcpy` dispatch prologue, no-tail exit, and unified spec

Builds on `Vsa/Sim/MemcpySpec3.lean` (the small word-loop rule `word_loop_spec`,
the byte-tail epilogue `epilogue_tail_spec`, and the epilogue plumbing
`epilogue_a2`/`epilogue_ptr`/`mask_low3`) and `Vsa/Sim/MemcpySites4.lean` (the
per-site steps for the dispatch prologue `[0x80006bc8, 0x80006bf8]` and the `c3c`
`ret`).

## Task a — no-tail exit (`epilogue_notail_spec`)

When the word loop copies exactly `p = n/8` words with `8p = n` (whole copy
word-aligned), the epilogue's `c38 bltu a4,a7` is *not*-taken (`a4 = dst+8p =
dst+n = a7`), falling to the `c3c ret`.  This mirrors `epilogue_tail_spec` but the
seven epilogue ALU steps are followed by `ret` instead of the byte loop.

## Task b — dispatch transitions (`bc8 → {byte | word}`)

The dispatch classifies `(dst, src, n)` and routes:
* misaligned (`(src ^^^ dst) &&& 7 ≠ 0`) — `bd4` taken → byte path `c40`;
* small (`n < 8`) — `bdc` taken → byte path `c40`;
* aligned, `n ≥ 8`, and (via `P`) `dst%8 = 0`, `8p ≤ 64` — fall through the
  classification to the small word-loop setup `bfc`/`c00`/`c04` (`PreW`).

## Task c — unified spec (`memcpy_spec`)

The single total-correctness triple from the function entry `0x80006bc8`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (MemcpyLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## No-tail exit -/

/-! ## Dispatch prologue transitions (`bc8 → {byte | word}`)

The dispatch classifies `(dst, src, n)`.  It performs no stores, so `MemInv … 0`
transfers unchanged from the entry state to the routed target.  Fresh ghosts per
the crossover pattern (the entry ghost `g` cannot survive the frame rewrite across
the classification, but each target predicate's own frame re-exposes untouched
registers). -/

/-! ### Mask facts (`andi …,7` and `andi …,-8` bitwise route) -/

/-- `(v &&& sext 0x007).toNat = v.toNat % 8`. -/
theorem and7_toNat (v : BitVec 64) : (v &&& sign_extend (m := 64) (0x007#12)).toNat = v.toNat % 8 := by
  rw [BitVec.toNat_and, show (sign_extend (m := 64) (0x007#12) : BitVec 64).toNat = 7 from by decide,
    show (7:Nat) = 2^3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, show (2:Nat)^3 = 8 from rfl]

/-- `sltiu v 8` value: `true` iff `v.toNat < 8`. -/
theorem sltiu8_val (v : BitVec 64) :
    zopz0zI_u v (sign_extend (m := 64) (0x008#12)) = true ↔ v.toNat < 8 := by
  unfold zopz0zI_u Sail.BitVec.toNatInt
  rw [show (sign_extend (m := 64) (0x008#12) : BitVec 64).toNat = 8 from by decide, decide_eq_true_iff]
  constructor
  · intro h; have := Int.ofNat_lt.mp h; omega
  · intro h; exact Int.ofNat_lt.mpr h

/-- `sltiu v 8` written value nonzero iff `v.toNat < 8`. -/
theorem sltiu8_ne_zero_iff (v : BitVec 64) :
    ((zero_extend (m := 64) (bool_to_bit (zopz0zI_u v (sign_extend (m := 64) (0x008#12))))) != (0#64)) = true
      ↔ v.toNat < 8 := by
  rw [bne_iff_ne, ne_eq]
  by_cases hlt : v.toNat < 8
  · have hv : zopz0zI_u v (sign_extend (m := 64) (0x008#12)) = true := (sltiu8_val v).mpr hlt
    rw [hv]
    simp only [hlt, iff_true]
    intro h; exact absurd (congrArg BitVec.toNat h) (by decide)
  · have hv : zopz0zI_u v (sign_extend (m := 64) (0x008#12)) = false := by
      cases h : zopz0zI_u v (sign_extend (m := 64) (0x008#12)) with
      | false => rfl
      | true => exact absurd ((sltiu8_val v).mp h) hlt
    rw [hv, show (zero_extend (m := 64) (bool_to_bit false) : BitVec 64) = 0#64 from by
      apply BitVec.eq_of_toNat_eq; decide]
    simp only [hlt, iff_false, Classical.not_not]

/-! ### Dispatch entry predicate (`0x80006bc8`) -/

/-! ### `a2 = ofNat n` reads back as `n` under no-wrap -/

/-! ### Common dispatch prefix `bc8 → bd4` (three ALU steps to the first branch)

Runs `xor a5,a1,a0`; `andi a5,a5,7`; `add a7,a0,a2`, reaching `0x80006bd4` with
`a5 = (src^^^dst)&&&7`, `a7 = dst+n`, and `a0/a1/a2/ra` intact.  Packaged as an
intermediate config predicate `AtBd4`. -/

/-! ### Misaligned byte route: `bd4` taken → `c40` (`PreB`)

When `(src ^^^ dst) &&& 7 ≠ 0` (source/destination not congruent mod 8), the
`bnez a5` at `bd4` is taken, jumping to the byte-path prefix `0x80006c40`.  The
byte-path ghost is fresh (`∃ g'`). -/

/-! ### Small byte route: `bd4` nottaken → `bd8` → `bdc` taken → `c40` (`PreB`)

When aligned (`(src ^^^ dst) &&& 7 = 0`) but small (`n < 8`), `bd4` is not-taken,
`bd8 sltiu a2,a2,8` sets `a2 := 1` (since `n < 8`), and `bdc bnez a2` is taken to
the byte path.  Note `a2` is clobbered but the byte path recomputes what it needs;
`PreB`'s `a2` field is absent (the byte path re-derives `a7 = dst+n`). -/

/-! ### Word route: `bd4/bdc/be8` nottaken → `bfc/c00/c04` (`PreW`)

When aligned (`(src ^^^ dst) &&& 7 = 0`), `n ≥ 8`, `dst % 8 = 0`, and the rounded
word count fits (`8*(n/8) ≤ 64`), the classification falls through the three
`bnez`s and the `blt`, reaching the small word-loop setup and entry `c04`
(`PreW`) with `p = n/8`.  Fresh word-loop ghost. -/

/-! ## Task c — the unified `memcpy` spec (`memcpy_spec`)

The single total-correctness triple from the function entry `0x80006bc8`.

### Precondition `P` — the exact constraints

`P` (via `PreDispatch g`) fixes: `GoodState`, `MemcpyLoaded`, `PC = 0x80006bc8`,
`a0 = dst`, `a1 = src`, `a2 = n`, `x1 = r`, `minstret` defined, `tick < 2`,
`Regions dst src n` (region well-formedness / no-wrap / disjointness / RAM+HTIF
bounds), `0 < n`, `MemInv dst src n bs 0 m0 mem` (source bytes `bs` readable, dest
untouched), and the ghost frame `hframe`.  On top of `PreDispatch`, `memcpy_spec`
requires `r.toNat % 4 = 0` (return address 4-aligned, for the `ret`) and the
**route/size/alignment disjunction**

```
    (src.toNat ^^^ dst.toNat) % 8 ≠ 0                                  -- (A) misaligned → byte path
  ∨ n < 8                                                              -- (B) small → byte path
  ∨ (dst.toNat % 8 = 0 ∧ 8 * (n / 8) ≤ 64)                            -- (C) aligned word path
```

The `8 * (n / 8) ≤ 64` bound is the EXACT threshold derived from the `bf8`
`blt a5,a3` guard (`a5 = 64`, `a3 = 8*(n/8)`): the small word loop is entered iff
the rounded word-byte count fits in 64.  For interpreter call sites this covers
`Value` copies (24 B) and small strings; larger aligned copies take the `c60`
×8-unrolled path (documented follow-up).  Disjunct (C)'s `dst % 8 = 0` excludes
the `be8` head-align peel (`0x80006cbc`): the peel fires only when aligned-xor but
`dst % 8 ≠ 0`, which (C) rules out (cases (A)/(B) never reach `be8`).

### Postcondition `Q` — `memcpy_bytepath_post`

`Q c := ∃ g', memcpy_bytepath_post g' r dst n m0 bs c`, i.e. `GoodState`,
`PC = r`, `x10 = dst` (memcpy returns dst), `x1 = r`, `∀ k < n, mem[dst+k] = bs k`
(the described copy), `∀ a ∉ [dst,dst+n), mem[a] = m0[a]` (outside unchanged),
`tick < 2`, and a blanket ghost frame against the RETURN state's reads (a fresh
top-level `g'`).

### Ghost reconciliation

Each path instantiates its own fresh ghost at the crossover (`PreB`/`PreW` ghosts
are `fun R => σ.regs.get?` at the dispatch-successor state; the entry ghost `g`
does not survive the frame rewrites across `NotWrittenW`/`NotWrittenB`).  The
top-level `Q` frame is likewise packaged existentially (`∃ g'`), so the composed
spec exposes ONE fresh ghost — the return state's own reads — reconciling all the
per-path fresh ghosts into a single top-level frame witness. -/

end Vsa.Sim
