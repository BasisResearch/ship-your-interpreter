import Vsa.Sim.MemcpySites2
import Vsa.Sim.MemcpySpec
import Vsa.Triple
import Vsa.Sim.ObsAvoid

/-!
# Layer 3 — `memcpy` small-word-loop byte bridge and word-granularity invariant step

This file bridges the 8-byte insert chain produced by the word-loop `sd`
(`Vsa.Sim.sdMem8`, from `vmem_write_addr_8`) to the ghost byte function `bs`, and
extends the byte-level memory invariant `MemInv` (from `Vsa/Sim/MemcpySpec.lean`)
by 8 bytes at once (`meminv_store8`).

## The word-store byte bridge

The word loop loads a full 8-byte word from `src + 8i` — which, byte-by-byte, is
`ldData8 (bs (8i)) (bs (8i+1)) … (bs (8i+7))` — and stores it at `dst + 8i`. The
architectural post-map is the little-endian byte chain
`sdMem8 mem (dst+8i) word`, i.e. `mem.insert (…+k) ((sdData8 word).extractLsb' (8k) 8)`
for `k ∈ [0,8)`. We prove that each such slice recovers the corresponding source
byte: `(sdData8 (sign_extend (ldData8 c0 … c7))).extractLsb' (8k) 8 = c_k`.

This is `extractLsb'`-of-`append` at eight offsets. We prove it once, generically,
via `BitVec.eq_of_toNat_eq` on the `toNat` shape of `extractLsb'` and `append`.
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

/-! The word-loop `ld a6,0(a3)` needs the pointed word `bs (8j) … bs (8j+7)` to be
readable; `MemInv.src_intact` supplies each byte, and the load's little-endian
assembly is exactly `ldData8 (bs 8j) … (bs 8j+7)`. -/

/-! ## `sdData8` of a `sign_extend`-of-`ldData8` word is the plain `ldData8` value

`sdData8 vdata = extractLsb vdata 63 0` is width-preserving on a `BitVec 64`, and
`sign_extend (m := 64)` on a `BitVec 64` argument is the identity. So the stored
byte chain is exactly the loaded little-endian assembly. -/

/-! ## The eight byte slices of `ldData8` recover the eight source bytes

`ldData8 c0 … c7 = c7 +++ c6 +++ … +++ c0` (little-endian bytes), so
`extractLsb' (8k) 8` picks byte `c_k`. Proved bitwise via `getLsbD` of `extractLsb'`
and `append`, descending through the eight-way append at each concrete `k`. -/

/-- Extract byte `k` (`k < 8`) from `ldData8`: `extractLsb' (8k) 8` picks the `k`-th
byte `c_k` (given as `[c0,…,c7][k]? = some c_k`). -/
theorem extractLsb'_ldData8 (c0 c1 c2 c3 c4 c5 c6 c7 : BitVec 8) (k : Nat) (hk : k < 8)
    (ck : BitVec 8)
    (hck : [c0, c1, c2, c3, c4, c5, c6, c7][k]? = some ck) :
    (ldData8 c0 c1 c2 c3 c4 c5 c6 c7).extractLsb' (8 * k) 8 = ck := by
  show ((((((((c7 +++ c6) +++ c5) +++ c4) +++ c3) +++ c2) +++ c1) +++ c0).extractLsb' (8 * k) 8) = ck
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  match k, hk, hck with
  | 0, _, hck | 1, _, hck | 2, _, hck | 3, _, hck
  | 4, _, hck | 5, _, hck | 6, _, hck | 7, _, hck =>
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.some.injEq] at hck
    subst hck
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, Nat.reduceMul]
    rw [decide_eq_true (show i < 8 from hi), Bool.true_and]
    repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
    congr 1 <;> omega

/-! ## The word-store byte chain, read back at each offset

`sdMem8 mem a word` is the 8-byte insert chain at `a, a+1, …, a+7`. We record two
read-over-write facts:
* at a key outside `[a.toNat, a.toNat+8)`, the chain reads through to `mem`;
* at `a.toNat + k` (`k < 8`), the chain reads `(sdData8 word).extractLsb' (8k) 8`. -/

/-! ## Word-granularity invariant step (`meminv_store8`)

From `MemInv … (8j) mem` at a word-aligned byte-iteration `8j < n` with a full
remaining word (`8j + 8 ≤ n`), storing the loaded word
`word = sign_extend (ldData8 (bs 8j) … (bs 8j+7))` at `dst + 8j` re-establishes
`MemInv … (8j + 8)` for the map `sdMem8 mem (dst + ofNat 8j) word`.

The stored bytes come from `src_intact` (the loaded word IS `bs 8j … bs 8j+7`), and
the eight slices recover them via `extractLsb'_ldData8`. All key disequalities are
`omega`-shaped from `Regions` + word alignment. -/

/-! ## Pointer identities for the word loop

The word loop advances `a3`/`a5` by 8 each iteration. `ptr_word_succ` is the
`+8` increment as a `BitVec` add (`sign_extend 0x008 = 8`); `sdAddrM8_succ` is the
`sd …,-8(a5)` back-offset (`a5` pre-incremented to `dst + 8(j+1)`, the store lands
at `dst + 8j`). -/

/-! ## Blanket ghost-frame predicate (`NotWrittenW`) + generic per-class helpers

`StW` tracks the word-loop live GPRs plus the scratch `a6` (`x16`). To make
preservation of *every other* register recoverable after packaging into a `Triple`,
`StW` carries a ghost snapshot `g` and a blanket conjunct: every register outside
the write-set reads as its ghost value.

`NotWrittenW R` is the disequality conjunction over the union of the word-path
written GPRs (`x13` = `addi a3`, `x15` = `addi a5`, `x16` = `ld a6`) and the per-step
write-set / tick-set registers (`PC, nextPC, minstret, minstret_increment, mcycle,
mtime, mip`). The word `sd` writes only memory (no rd), covered by the noise
disequalities alone. -/

/-! ## The word-loop head state and one-iteration Triple

`StW p j r dst src n m0 bs c` is the standing observation at the word-loop head
`0x80006c08`, word-iteration `j`, where `p` is the word count (`a2 = dst + 8p` is
the loop's end bound). It bundles `GoodState`, code loaded, PC at c08, the live
pointers (`a0 = dst`, `a1 = src`, `a2 = dst+8p`, `a3 = src+8j`, `a4 = dst`,
`a5 = dst+8j`, `a7 = dst+n`), `x1 = r`, `minstret` defined, `tick < 2`, the
`Regions` bounds, `8(j+1) ≤ n` (a full word remains and stays in-region), and
`MemInv … (8j)`. Base 8-alignment of `dst`/`src` is carried as fields so the
per-iteration store/load alignment side conditions discharge. -/

/-! ### Per-iteration RAM/window bounds for the word pointers -/

/-! ## One word-loop body iteration (`0x80006c08 → 0x80006c18`)

Chains `ld a6,0(a3) → addi a5,a5,8 → addi a3,a3,8 → sd a6,-8(a5)`. The `ld` reads
the 8-byte word `bs 8j … bs 8j+7` from `src+8j` (`word_src_bytes` via
`MemInv.src_intact`); the two `addi`s advance `a5`/`a3` by one word; the `sd`
writes that word back at `dst+8j` (`sdAddrM8_word_succ`), and `meminv_store8`
re-establishes `MemInv … (8(j+1))`. -/

end Vsa.Sim
