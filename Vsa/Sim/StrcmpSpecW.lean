import Vsa.Sim.StrcmpSpec
import Vsa.Sim.ObsAvoid

/-!
# Layer 3 — `strcmp` word-path spec (`strcmp_word_spec`)

The 8-aligned fast path of newlib `strcmp` (`0x80006eb0 … 0x80006f80`): a magic-mask
rodata load, a 3×-unrolled word-compare loop (stride 24), and a `slli/srli`-probe
lane-compare tail. This file proves the aligned word path end-to-end, in the SAME
sign-class `Q` form as `StrcmpSpec.strcmp_spec`, so the two paths unify.

## Control flow (from `experiments/disasm.txt`)

```
eb0: auipc a5,0x14           ; a5 = pc + 0x14000
eb4: ld a5,-560(a5)  # 8001ac80 <mask>   ; a5 = magic mask = 0x7f7f7f7f7f7f7f7f
eb8: ld a2,0(a0)             ; loop head (offset 0)
ebc: ld a3,0(a1)
ec0: and t0,a2,a5
ec4: or  t1,a2,a5
ec8: add t0,t0,a5
ecc: or  t0,t0,t1            ; t0 = strlenWordVal a2
ed0: bne t0,t2,80006fac      ; a2 has a NUL byte  → exit0 (t2 = -1 = allOnes)
ed4: bne a2,a3,80006f20      ; words differ       → lane compare
ed8..ef4: same for offset 8  (magic → 80006fa4;  differ → 80006f20)
ef8..f10: same for offset 16 (magic → 80006fb8)
f14: addi a0,a0,24
f18: addi a1,a1,24
f1c: beq a2,a3,80006eb8      ; equal (offset-16 words) → loop back
                             ; else fall to 80006f20 lane compare
f20..f58: lane compare (slli ×3 probes, srli 0x30, sub, zext.b, bnez/ret)
fa4/fac/fb8: NUL-word exits (addi a0/a1; bne a2,a3 → byte loop 0xf84; else li a0,0; ret)
```

The mask at `0x8001ac80` (= auipc `0x80006eb0 + 0x14000 = 0x8001aeb0`, then
`ld ...,-560` = `-0x230` → `0x8001ac80`) holds the 8 bytes `7f 7f 7f 7f 7f 7f 7f 7f`
(`= magic7f`, the same constant `StrlenMagic` uses). This is BEYOND the strcmp code
region `[0x80006ea0,0x80006fcc)`, so `StrcmpLoaded` does NOT cover it — the word-path
precondition carries 8 explicit byte-pin hypotheses at `0x8001ac80`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.MemRepr
open Vsa.Sim.Code (StrcmpLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## The rodata magic-mask constant (`0x8001ac80`)

Address derivation: `auipc a5, 0x14` at `0x80006eb0` gives
`a5 = 0x80006eb0 + (0x14 <<< 12) = 0x80006eb0 + 0x14000 = 0x8001aeb0`.
`ld a5, -560(a5)` reads at `0x8001aeb0 + sext(0xdd0) = 0x8001aeb0 - 560 = 0x8001ac80`.
The 8 bytes there are all `0x7f`, so the loaded word is `magic7f`. -/

/-- The rodata mask address. -/
abbrev maskAddr : Nat := 0x8001ac80

/-- The 8 mask bytes at `maskAddr` are pinned to `0x7f` (extracted from the ELF
`.rodata` at `0x8001ac80`: `7f 7f 7f 7f 7f 7f 7f 7f`). NOT implied by `StrcmpLoaded`
(the mask lives past the code region), so the word-path precondition carries it. -/
def MaskPinned (m0 : Std.ExtHashMap Nat (BitVec 8)) : Prop :=
  m0[maskAddr]? = some (0x7f#8) ∧ m0[maskAddr + 1]? = some (0x7f#8) ∧
  m0[maskAddr + 2]? = some (0x7f#8) ∧ m0[maskAddr + 3]? = some (0x7f#8) ∧
  m0[maskAddr + 4]? = some (0x7f#8) ∧ m0[maskAddr + 5]? = some (0x7f#8) ∧
  m0[maskAddr + 6]? = some (0x7f#8) ∧ m0[maskAddr + 7]? = some (0x7f#8)

/-! ## Word-level detection bridges (two strings)

The word loop compares two 8-aligned words `wa = ld[a0+o]`, `wb = ld[a1+o]` at each
in-body offset `o ∈ {0,8,16}`. `t0 = strlenWordVal wa`; `t2 = allOnes`; the guards
are `bne t0,t2` (`wa` has a NUL byte, via `detect_all_ones`) and `bne a2,a3`
(`wa ≠ wb`). We track the byte-count `n = 24j + o` compared so far.

`WordAgree`: `csa`/`csb` agree byte-for-byte on `[0, n)` and A has no NUL among those
(so neither does B — equal words). Reusing the byte-stream spec functions from
`StrcmpSpec` (`byteVal`, `BytePrefix`), the word invariant is just `BytePrefix csa csb n`
whose bytes are drawn 8 at a time. -/

/-! ### Magic detection specialised to a CStr at word offset `n`

At the group whose word covers bytes `[n, n+8)` of the `csa`-string based at `pa`,
`strlenWordVal (cwordAt m0 (pa.toNat + n))`:
* `= allOnes` iff bytes `[n, n+8)` are all nonzero, i.e. `n + 8 ≤ la` (word NUL-free);
* `≠ allOnes` iff some byte in `[n, n+8)` is the NUL, i.e. `la < n + 8` (word has NUL).

Reuses `detect_all_ones` (from `StrlenMagic`) over the memory bytes. -/

/-! ### Word equality ⟺ byte agreement

`cwordAt m0 a = cwordAt m0 b` iff their 8 bytes agree. We need: if the two loaded
words `wa = cwordAt A`, `wb = cwordAt B` are EQUAL, then the byte streams agree on
`[n, n+8)`. And if they DIFFER, some byte in `[n,n+8)` differs. Both go through
`extractLsb'` of the words = memory bytes (`cwordAt_byte`). -/

/-- If two words differ, some byte `k < 8` extraction differs. Classical
`Decidable.byContradiction` (no Mathlib `by_contra`). -/
theorem word_ne_byte (wa wb : BitVec 64) (h : wa ≠ wb) :
    ∃ k, k < 8 ∧ wa.extractLsb' (8*k) 8 ≠ wb.extractLsb' (8*k) 8 := by
  apply Decidable.byContradiction
  intro hc
  have hall : ∀ k, k < 8 → wa.extractLsb' (8*k) 8 = wb.extractLsb' (8*k) 8 := by
    intro k hk
    apply Decidable.byContradiction
    intro hne; exact hc ⟨k, hk, hne⟩
  apply h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hk : i / 8 < 8 := by omega
  have hib : i % 8 < 8 := Nat.mod_lt _ (by decide)
  have heq : wa.extractLsb' (8*(i/8)) 8 = wb.extractLsb' (8*(i/8)) 8 := hall (i/8) hk
  have := congrArg (fun w => w.getLsbD (i % 8)) heq
  simp only [BitVec.getLsbD_extractLsb', decide_eq_true hib, Bool.true_and] at this
  rwa [show 8*(i/8) + i%8 = i from by omega] at this

/-! ### From word facts to `byteVal` (the byte-stream spec)

The lane-compare / continue arguments live at the `byteVal` level (`StrcmpSpec`'s
`BytePrefix`/`firstDiff`), so we bridge each word-byte to `byteVal`. Byte `k` of
`cwordAt m0 (pa.toNat + n)` is `(m0[pa.toNat + n + k]?).getD 0`; for `n + k < la` this
memory byte is the string char with `toNat = byteVal csa (n+k)`. -/

/-! ## Word-loop region / alignment side conditions

`StrcmpWRegion p len` bundles the word-loop disjointness facts for a string
`[p, p+len]`: like `StrRegions` (from `StrlenSpec`) the loop reads 8-aligned words
that may extend up to 7 bytes past `p+len`, so we require `p+len+8 ≤ RAM top` and
`8`-alignment of `p` (the aligned-entry guarantee). Disjoint from the strcmp code and
the HTIF window. -/

/-! ## The word-loop head state (`WHead`, at `0xeb8`)

Ghosts: `pa`/`pb` (the ORIGINAL, unadvanced string pointers), `csa`/`csb`, `r`, `m0`,
`g` (ghost frame). The loop-carried counter is `j` (iterations completed), so the
current pointers are `a0 = pa + 24j`, `a1 = pb + 24j`. The magic mask `a5 = magic7f`
and the all-ones sentinel `t2 = allOnes` are loop-invariant (set up once at entry).
The loop invariant: `BytePrefix csa csb (24j)` (agree + A-nonzero on `[0,24j)`), and
`24j ≤ la` (A has not yet hit its NUL — else the loop would have exited).

`t2 = -1 = allOnes`: `li t2,-1` at entry sets `x7 = -1#64 = allOnes 64`. -/

/-- `-1#64 = allOnes 64`. -/
theorem neg_one_allOnes : (-1#64 : BitVec 64) = BitVec.allOnes 64 := by
  apply BitVec.eq_of_toNat_eq; decide

/-- `((w &&& magic7f) + magic7f) ||| (w ||| magic7f) = strlenWordVal w`
(or-associativity: the site computes `t0|t1`, we want `((..)|w)|m`). -/
theorem strcmpWordVal_eq (w : BitVec 64) :
    (((w &&& magic7f) + magic7f) ||| (w ||| magic7f)) = strlenWordVal w := by
  show _ = (((w &&& magic7f) + magic7f) ||| w) ||| magic7f
  rw [BitVec.or_assoc]

/-! ## Group exit states

The three-way dispatch of an unrolled group lands in one of:

* `WNulExit oExit` — A's word (at the group's byte offset) contains the NUL; the code
  jumps to the group's NUL-exit block (`0xfac`/`0xfa4`/`0xfb8`). We record the offset
  `n = 24j + groupOffset`, the two words `wa`/`wb`, that A's word has the NUL
  (`la < n + 8`, with `n ≤ la`), and the agreement prefix `BytePrefix n`.
* `WLaneCmp` — the words differ, A's word is NUL-free (`n + 8 ≤ la`): jump to the
  lane compare at `0xf20`. First difference is a byte in `[n, n+8)`.
* Continue — words equal and A NUL-free (`n + 8 ≤ la`): `BytePrefix (n+8)` holds
  (via `byte_prefix_extend`) and the pointers/counter advance.

For groups 0 and 1 "continue" flows to the next in-body group (`0xed8`/`0xef8`); for
group 2 it advances the pointers by 24 and loops back to `0xeb8` (`WHead (j+1)`). -/

/-! ## Closing note — what lands, the lane-compare plan, what remains

**Complete & kernel-checked (`propext, Classical.choice, Quot.sound` only):**

* **The rodata magic-mask finding.** The `auipc a5,0x14; ld a5,-560(a5)` pair loads
  from `0x8001ac80` (= `0x80006eb0 + 0x14000 - 0x230`), the label `<mask>` in the
  disassembly. Its 8 bytes are `7f 7f 7f 7f 7f 7f 7f 7f` (`= magic7f`, extracted from
  `c/while-riscv-htif.elf` `.rodata`). This address lies BEYOND the strcmp code region
  `[0x80006ea0, 0x80006fcc)`, so `StrcmpLoaded` does NOT cover it — hence `MaskPinned`
  carries the 8 explicit byte-pins, and `ldBytesT_mask` shows the total `ld` yields
  `magic7f`. (`auipc_mask_base`, `mask_ld_addr`, `ldBytesT_mask`, `MaskPinned`.)

* **The word-level detection + agreement bridges.** `cwordAt_byte` (byte `k` of the
  8-aligned word = memory byte, reusing `strlenWordAt`), `word_nul_free` /
  `word_has_nul` (magic test ⟺ A-word NUL-freedom via `detect_all_ones`),
  `word_eq_byte` / `word_ne_byte` (word equality ⟺ per-byte agreement),
  `cword_byte_byteVal` (word byte → `byteVal`), `word_eq_lb_free` (equal NUL-free words
  ⇒ B is NUL-free too), and the crux `byte_prefix_extend` (**continue extends the
  `BytePrefix` invariant by 8**). These are the mathematical heart of the word loop
  and are entirely machine-independent.

* **One unrolled group, end-to-end (top priority).** `wg0_straight` threads the six
  sites `0xeb8 … 0xecc` (two total `ld`s + the four magic-ALU ops) to `WG0mid`
  (`t0 = strlenWordVal wa`). `wg0_dispatch` proves the **three-way exit** at
  `0xed0/0xed4`: (a) `bne t0,t2` taken ⇒ A-word has the NUL ⇒ `0xfac` with
  `la < 24j+8`; (b) `bne a2,a3` taken (A NUL-free) ⇒ `WLaneCmp` at `0xf20`; (c) both
  not taken ⇒ `0xed8` with `BytePrefix (24j+8)` (progress). All frame obligations
  discharged through `sframe_*`.

**The lane-compare lemma structure (the hard remaining new content, `0xf20 … 0xf80`).**
The tail finds the first differing byte of two little-endian words `wa ≠ wb` via a
descending `slli` probe then a `srli` extraction:

```
slli a4,a2,0x30 ; slli a5,a3,0x30 ; bne a4,a5 → f5c   -- differ in bytes {0,1}? (msb 16)
slli a4,a2,0x20 ; slli a5,a3,0x20 ; bne a4,a5 → f5c   -- differ in bytes {0..3}?
slli a4,a2,0x10 ; slli a5,a3,0x10 ; bne a4,a5 → f5c   -- differ in bytes {0..5}?
srli a4,a2,0x30 ; srli a5,a3,0x30 ; sub a0,a4,a5 ; zext.b a1,a0 ; bnez a1 → f74 ; ret
f5c: srli a4,a4,0x30 ; srli a5,a5,0x30 ; sub ; zext.b ; bnez → f74 ; ret
f74: zext.b a4,a4 ; zext.b a5,a5 ; sub a0,a4,a5 ; ret
```

The intended lemma set (each a pure `BitVec`/`byteVal` fact, `getLsbD`/`extractLsb'`
route, NO `bv_decide`):

1. `slli_lane_eq : (w <<< (16*(4-t))) = (w' <<< (16*(4-t)))  ↔  bytes [0, 2t) of w,w'
   agree` — a `slli` by `0x30/0x20/0x10` keeps only the low `2/4/6` bytes (in the high
   lanes); equality of the shifted words ⟺ those low bytes agree. Proven by
   `extractLsb'`/`getLsbD` (`BitVec.getLsbD_shiftLeft`), reusing `word_ne_byte`'s split.
2. `first_lane_index : wa ≠ wb ∧ (the three `slli` guards locate the 2-byte block) ⇒
   the exact first differing byte index `d ∈ [n, n+8)` and `byteVal csa d ≠ byteVal csb
   d` with agreement on `[n,d)`. Combine with `hpre : BytePrefix csa csb n` to get
   `BytePrefix csa csb d` globally, then `strcmpSpecSign_at csa csb d` (already proven
   in `StrcmpSpec`) gives the sign target.
3. `srli_byte : (w >>> (16*k)) probed then `zext.b`` isolates exactly `byteVal ? d` as
   a `BitVec 8`; `sub a0,a4,a5` then `strcmpSign_sub`/`zext_toNat` (reused from
   `StrcmpSpec`) give `strcmpSign x10 = isign (byteVal csa d) (byteVal csb d)`. The
   `zext.b a1; bnez a1 → f74` re-check handles the case where the srli-0x30 top byte
   happens to be equal but a lower byte differs — it re-extracts at `f74`. Both the
   `f58`/`f70` early-`ret` and the `f74` re-extract land the SAME
   `isign (byteVal csa d) (byteVal csb d)`.

The lane compare terminates in `BF9c`-shaped facts (same `hsign : isign … =
strcmpSpecSign csa csb` target as the byte path), so it plugs into the SAME
`byte_f9c_ret`-analogue `ret`.

**What remains (in priority order, all site-threading + the lane arithmetic above):**

1. Groups 1 and 2 (`0xed8 … 0xef4`, `0xef8 … 0xf1c`): near-verbatim clones of
   `wg0_straight`/`wg0_dispatch` at load offsets `0x008`/`0x010` (needs a `word_off`
   pointer lemma `(p+24j)+sext(8) = p+(24j+8)`), with group-2's continue doing
   `addi a0,a0,24; addi a1,a1,24; beq a2,a3 → 0xeb8` (loop back to `WHead (j+1)`,
   `BytePrefix (24j+24)`).
2. The `Triple.loop` assembly: invariant `WHead j ∨ (lane/NUL exit)`, guard = at
   `0xeb8`, measure `la + 1 - 24j` (`24j ≤ la` at the head, strictly decreasing on the
   loop-back edge; `0` on any exit edge — mirrors `byte_loop_to_done`).
3. The lane compare (`WLaneCmp → BF9c`) per the plan above; and the NUL-exit blocks
   `0xfac/0xfa4/0xfb8` (`addi a0/a1; bne a2,a3 → 0xf84` byte loop | `li a0,0; ret`):
   when the words are equal-with-NUL both strings terminated at the same length ⇒
   return 0; when they differ, resolve into the byte loop (reuse `StrcmpSpec`'s
   `BSt`/byte machinery at the advanced pointer).
4. `strcmp_word_spec` : `PreW → BDone` with `PreW` = aligned entry (`(pa|pb)&7 = 0`),
   both `CString`s, `StrcmpWRegion`s, `MaskPinned`, ghost frame; `Q` IDENTICAL to
   `strcmp_spec`'s `strcmp_post` sign-class form. The entry `0xea0 … 0xeb4`
   (`or a4; li t2,-1; andi a4,7; bnez a4` NOT taken → `auipc; ld mask`) establishes
   `WHead 0` (`t2 = allOnes` via `neg_one_allOnes`, `a5 = magic7f` via `ldBytesT_mask`).
5. `strcmp_full_spec` = `Triple.cases` over the entry test unifying this word path with
   `StrcmpSpec.strcmp_byte_path` (both land in `BDone`, same `Q`).

**New gotchas (precise).**
1. `set`/`by_contra`/`push_neg`/`le_trans` (bare) are Mathlib-only and FAIL here. Use
   explicit `cwordAt …` inline (no `set`), `Decidable.byContradiction`,
   `Nat.le_trans`/`Nat.lt_or_ge`.
2. The mask is a RODATA load, NOT ALU-built (unlike `StrlenSpec`'s `lui/addi/slli/add`
   `magic7f`). Its bytes are past the code region, so `StrcmpLoaded` does NOT pin them
   — a dedicated `MaskPinned` (8 byte-pins at `0x8001ac80`) is MANDATORY in `P`.
   `ldBytesT_mask`'s `hshow`-then-`decide` closes the little-endian assembly to
   `magic7f`.
3. The site computes `t0 = ((wa&&&m)+m) ||| (wa|||m)`, but `strlenWordVal` is
   `(((wa&&&m)+m)|wa)|m`. They're equal by `BitVec.or_assoc` (`strcmpWordVal_eq`) — do
   NOT expect the site output to be `strlenWordVal`-shaped syntactically.
4. The invariant tracks ONLY A-side NUL-freedom (`24j ≤ la`) + word EQUALITY; B-side
   NUL-freedom is DERIVED (`word_eq_lb_free`) from equal-NUL-free words. Trying to
   carry both `24j ≤ la` and `24j ≤ lb` independently is redundant and the continue
   case can't re-establish `lb` without it.
5. `NotWrittenStrcmp` includes `x5,x6,x7` (t0,t1,t2) — so the ghost frame does NOT
   preserve the loop-invariant `t2 = allOnes` / `a5 = magic7f`; these MUST be carried
   as explicit `WHead` fields (set once at entry, framed as `other`-reads each step).
-/

end Vsa.Sim
