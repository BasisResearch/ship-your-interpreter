import Vsa.Sim.StrlenSites
import Vsa.Sim.StrlenMagic
import Vsa.Sim.Muldi3Spec
import Vsa.MemRepr
import Vsa.Triple
import Vsa.Sim.ObsAvoid
import Vsa.Alloc

/-!
# Layer 3 — `strlen` total-correctness spec (`strlen_spec`)

Config-level (`Vsa.Logic.Triple`) composition of the per-site observational steps
(`Vsa/Sim/StrlenSites.lean`) and the magic-constant zero-byte detection arithmetic
(`Vsa/Sim/StrlenMagic.lean`) into a total-correctness triple for newlib `strlen`
(`[0x80006cf0, 0x80006dc4)`).

## Control flow (from the disassembly)

* entry `0xcf0..0xcfc`: `andi a5,a0,7; mv a4,a0; bnez a5,d78`.  Aligned ⇒ set up
  the magic mask and fall to the word loop; unaligned ⇒ jump to the head peel.
* magic setup `0xd00..0xd0c`: builds `a3 = 0x7f7f…7f`, `a1 = -1 = allOnes`.
* word loop `0xd10..0xd28`: `ld a2,0(a4); addi a4,a4,8;` compute
  `a5 = strlenWordVal a2`; `beq a5,a1,d10` (loop while no zero byte).
* byte tail `0xd2c..0xd70`: `lbu`/`beqz` ladder locating the NUL in the hit word.
* head peel `0xd74..0xd90`: byte-at-a-time until 8-aligned (own back-edge).
* exit blocks `0xd94..0xdc0`: `addi a0,a3,imm; ret` computing the length.

This file proves the pieces bottom-up.  See the end-of-file summary for exactly
what lands.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.MemRepr
open Vsa.Alloc
open Vsa.Sim.Code (StrlenLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## CStr byte facts

From `CStr m p cs`, the byte at `p + k` (`k < cs.length`) is the (nonzero) char,
and the byte at `p + cs.length` is `0`.  These bridge the string predicate to the
per-address `m[·]?` values the load chain consumes. -/

/-! ## Loaded-word byte extraction

The word-loop `ld` produces `sign_extend (ldBytesT σ a)`, which — since
`sign_extend (m := 64)` is identity on a `BitVec 64` — is exactly `ldBytesT σ a`.
Byte `k` of that word (`extractLsb' (8k) 8`) is the total (`getD 0`) memory byte
at `a + k`.  This bridges the loaded word to the per-address memory bytes that the
`CStr` facts describe, so `detect_all_ones` can fire on the string content. -/

/-- `sign_extend (m := 64)` is the identity on a `BitVec 64`. -/
theorem sext64_self (x : BitVec 64) : sign_extend (m := 64) x = x := by
  simp only [sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq]

/-- Byte `k` (`k < 8`) of the totally-loaded word `ldBytesT σ a` is the memory byte
at `a.toNat + k` (`getD 0`).  Bitwise via `getLsbD` of `extractLsb'`/`append`. -/
theorem ldBytesT_byte (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64)
    (k : Nat) (hk : k < 8) :
    (ldBytesT σ a).extractLsb' (8*k) 8 = (σ.mem[a.toNat + k]?).getD 0 := by
  have hshow : ldBytesT σ a =
    ((((((((σ.mem[a.toNat + 7]?).getD 0) +++ ((σ.mem[a.toNat + 6]?).getD 0)) +++
     ((σ.mem[a.toNat + 5]?).getD 0)) +++ ((σ.mem[a.toNat + 4]?).getD 0)) +++
     ((σ.mem[a.toNat + 3]?).getD 0)) +++ ((σ.mem[a.toNat + 2]?).getD 0)) +++
     ((σ.mem[a.toNat + 1]?).getD 0)) +++ ((σ.mem[a.toNat]?).getD 0) := rfl
  rw [hshow]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  rw [decide_eq_true (show i < 8 from hi), Bool.true_and]
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
    congr 1 <;> omega

/-! ## Region / string side conditions

`StrRegions p len` bundles the disjointness / no-wrap side facts for the string
`[p, p+len]` (`len+1` bytes: `len` chars plus the NUL): the region lives in RAM,
disjoint from the `strlen` code `[0x80006cf0, 0x80006dc4)` and the HTIF window, and
does not wrap.  The word loop reads 8-aligned words that may extend up to 7 bytes
past `p+len`; those still lie in RAM (we require `p+len` far enough below the RAM
top), and their trailing content is read `getD 0` — never asserted. -/

/-- Exact pointer arithmetic under no-wrap: `(base + ofNat k).toNat = base.toNat + k`. -/
theorem ptrN (base : BitVec 64) (k : Nat) (h : base.toNat + k < 2^64) :
    (base + BitVec.ofNat 64 k).toNat = base.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2^64 from by omega),
    Nat.mod_eq_of_lt h]

/-! ## The magic-test detection bridge

At the word-loop guard `beq a5,a1` (`a5 = strlenWordVal a2`, `a1 = allOnes`), with
`a2 = ldBytesT σ pos` and `pos = p + 8j` (`8j ≤ len`), the branch is **taken** (no
zero byte in the word) iff `8j + 8 ≤ len`.

* Taken (`8j+8 ≤ len`): every byte `p+8j+k` (`k<8`) is a string char (`< len`), hence
  nonzero — `detect_all_ones` gives `strlenWordVal a2 = allOnes`.
* Not taken (`8j ≤ len < 8j+8`): byte `p+len` is the NUL, at word offset `len-8j < 8`,
  so `detect_all_ones` fails and `strlenWordVal a2 ≠ allOnes`. -/

/-! ## The word-scan loop (`0xd10 … 0xd28`)

Ghosts: `p` (the 8-aligned scan base — for the aligned entry path, `p = a0`),
`len` (the string length, `= cs.length`), `cs`/`r`/`m0`; `hword : p.toNat % 8 = 0`.

Loop-head state `WSt j`, iteration `j` (`8j ≤ len`): PC at `0xd10`, `a4 = p+8j`,
`a3 = magic7f`, `a1 = allOnes`, `a0 = p`, `x1 = r`, `mem = m0`, string facts, region
bounds, `minstret` defined, `tick < 2`.  The body loads the word at `a4`, advances
`a4 += 8`, computes `a5 = strlenWordVal(word)`, and the `beq a5,a1` at `0xd28` loops
(`8(j+1) ≤ len`) or exits to the byte tail at `0xd2c` (`len < 8(j+1)`, NUL in word). -/

/-- `v + sext 0 = v`. -/
theorem sext0_add (v : BitVec 64) : v + sign_extend (m := 64) (0x000#12) = v := by
  rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by
        apply BitVec.eq_of_toNat_eq; decide, BitVec.add_zero]

/-- `strlenWordVal w` matches the site-level composition `(((w & m)+m)|w)|m`. -/
theorem strlenWordVal_eq (w : BitVec 64) :
    ((w &&& magic7f) + magic7f ||| w) ||| magic7f = strlenWordVal w := rfl

/-! ### Bounds for the load at `a4 = p + 8j` -/

/-- The word `strlen` loads at scan position `p+8j` (total `getD 0` bytes, as a
`BitVec 64`).  Depends only on `m0` (via the address bytes). -/
def strlenWordAt (m0 : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) : BitVec 64 :=
  ((((((((m0[a + 7]?).getD 0).append ((m0[a + 6]?).getD 0)).append
    ((m0[a + 5]?).getD 0)).append ((m0[a + 4]?).getD 0)).append
    ((m0[a + 3]?).getD 0)).append ((m0[a + 2]?).getD 0)).append
    ((m0[a + 1]?).getD 0)).append ((m0[a]?).getD 0)

/-- `ldBytesT σ a = strlenWordAt σ.mem a.toNat` (both are the `getD 0` little-endian word). -/
theorem ldBytesT_wordAt (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64) :
    ldBytesT σ a = strlenWordAt σ.mem a.toNat := rfl

/-! ### Word-loop assembly (`Triple.loop`)

Invariant `WLoopI`: either at the head `0xd10` (some iteration `j`, `8j ≤ len`) or
done at the byte-tail entry `0xd2c` (`WTail`).  Guard `WLoopB`: at the head.  Measure
`WLoopMu = len + 1 - 8j` **at the head `0xd10`**, else `0` — the PC guard drops the
measure to `0` on the exit edge (to `0xd2c`), and the back-edge advances `j`. -/

/-! ## Entry + magic-constant setup (`0xcf0 … 0xd0c`), aligned path

Entry precondition `Pre`: PC at `0x80006cf0`, `a0 = p` (`p.toNat % 8 = 0`, the aligned
fast path), `x1 = r`, `mem = m0`, the `CStr` facts, regions.  The entry runs
`andi a5,a0,7` (`a5 = 0`), `mv a4,a0`, `bnez a5` (not taken, since aligned), then the
magic setup, landing at the word-loop head `0xd10` with `WSt 0`.

We isolate the aligned path here; the unaligned head-peel path (`bnez` taken) is a
separate (lower-priority) segment. -/

/-- For an 8-aligned `p`, `p &&& sext(0x007) = 0` (low 3 bits clear). -/
theorem andi7_aligned (p : BitVec 64) (halign : p.toNat % 8 = 0) :
    (p &&& sign_extend (m := 64) (0x007#12)) = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (sign_extend (m := 64) (0x007#12) : BitVec 64).toNat = 7 from by decide,
    show (7:Nat) = 2^3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    show (2:Nat)^3 = 8 from rfl, halign]
  rfl

/-- The magic-mask value `a3` built by `lui/addi/slli/add` equals `magic7f`. -/
theorem magic_build :
    (shift_bits_left (sign_extend (m := 64) ((0x7f7f8#20) +++ (0x000#12)) + sign_extend (m := 64) (0xf7f#12))
      (Sail.BitVec.extractLsb (0x20#6) 5 0)
      + (sign_extend (m := 64) ((0x7f7f8#20) +++ (0x000#12)) + sign_extend (m := 64) (0xf7f#12)))
      = magic7f := by
  apply BitVec.eq_of_toNat_eq; decide

/-- The `a1 = -1` value equals `allOnes 64`. -/
theorem allOnes_build : ((0#64) + sign_extend (m := 64) (0xfff#12)) = BitVec.allOnes 64 := by
  apply BitVec.eq_of_toNat_eq; decide

/-! ## Byte tail (`0xd2c … 0xd70`) and exit blocks (`0xd94 … 0xdc0`)

From `WTail j` (at `0xd2c`, `8j ≤ len < 8(j+1)`, `a4 = p+8(j+1)`, `a0 = p`): the tail
probes bytes `p+8j … p+8j+7` with `lbu`/`beqz`, and on hitting the NUL (at offset
`i₀ = len - 8j`) jumps to the exit block computing `a0 = a3 + (i₀ - 8) = 8(j+1) - 8 +
i₀ = 8j + i₀ = len`.  `d30 sub a3,a4,a0` sets `a3 = 8(j+1)`.

The final observation `Done`: PC at `r`, `a0 = ofNat len`, `x1 = r`, `GoodState`, mem
unchanged.  This is the strlen postcondition. -/

/-- `ofNat a - ofNat b = ofNat (a-b)` for `b ≤ a` (via add-cancel; no `2^64` omega). -/
theorem ofNat_sub (a b : Nat) (h : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  have : (BitVec.ofNat 64 (a-b)) + BitVec.ofNat 64 b = BitVec.ofNat 64 a := by
    rw [← BitVec.ofNat_add]; congr 1; omega
  rw [← this, BitVec.add_sub_cancel]

/-- `sub a3,a4,a0` value: `(p + ofNat m) - p = ofNat m`. -/
theorem sub_a4_a0_val (p : BitVec 64) (m : Nat) :
    (p + BitVec.ofNat 64 m) - p = BitVec.ofNat 64 m := by
  rw [BitVec.add_comm, BitVec.add_sub_cancel]

/-! ### Tail cursor states and the ladder

`TDec k` observes the config at the `beqz` (for `k ≤ 5`) / at `0xd60` (`k = 6`) decision
point for byte offset `k`, having found no NUL in offsets `0..k-1` (so `8j + k ≤ len`).
`a5 = byte@(p+8j+k)`, `a3 = ofNat(8(j+1))`, `a0 = p`, `x1 = r`, the string/region facts.

Byte-offset → `beqz`-PC map (from disasm): 0↦d34, 1↦d3c, 2↦d44, 3↦d4c, 4↦d54, 5↦d5c;
`beqz`-target (exit-addi PC) for offset `k` is the block computing `a0 = a3 - (8-k)`:
0↦d9c, 1↦d94, 2↦dac, 3↦da4, 4↦db4, 5↦dbc. Offsets 6,7 use the `snez` path at d60. -/

/-- `zext b == 0` iff `b == 0` (the `beqz a5` guard reads the loaded byte). -/
theorem zext_beqz (b : BitVec 8) : ((zero_extend (m := 64) b) == (0#64)) = (b == 0#8) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  constructor
  · intro h
    have : (zero_extend (m := 64) b).toNat = 0 := by rw [h]; rfl
    apply BitVec.eq_of_toNat_eq
    simpa [zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (show b.toNat < 2^64 from by have := b.isLt; omega)] using this
  · intro h; rw [h]; rfl

/-! ### Generic tail decision transitions

For each offset `k ≤ 5` we have two one-step-family transitions from the `beqz`-PC:
* **exit** (byte `= 0`, i.e. `8j+k = len`): `beqz` taken to the exit-addi PC, then
  `addi a0,a3,-(8-k)` gives `a0 = ofNat len`, and `ret` returns.  We package this via
  a `tail_exit` helper parameterized by the beqz/addi/ret sites.
* **next** (byte `≠ 0`, i.e. `8j+k < len`): `beqz` not taken, then the next `lbu`
  reads byte `k+1` → `TDec (k+1)`.

We handle the six offsets by direct instantiation; offsets 6,7 use the `snez` path. -/

/-! ### Byte-tail `beqz` decisions → `Done`

At `TDec j k` (`k ≤ 5`) with `8j+k = len` (the NUL byte), `beqz a5` is taken to the
exit-addi block, which computes `a0 = ofNat len`, then `ret`.  We chain the beqz-taken
transition (→ `AtAddi`) with the addi (→ `AtRet`) and `ret_to_done` (→ `Done`). -/

/-! ### Byte-tail `beqz` not-taken → next offset

At `TDec j k` with `8j+k < len` (byte nonzero), `beqz` falls through and the next
`lbu` reads byte `k+1`, reaching `TDec j (k+1)`.  We prove each `k → k+1` step.  These
share a helper `tdec_next` parameterized by the beqz-PC, next-lbu-PC, next-beqz-PC,
the beqz imm (for the fall-through), and the next `lbu` site (via a callback). -/

/-! ### The `snez` tail path (offsets 6, 7)

If bytes `0..5` are all nonzero (`8j+5 < len`, so `len ∈ {8j+6, 8j+7}`), the tail
skips the `beqz` ladder: `0xd60` loads byte 6, `0xd64 snez a0,a5` (`a0 = byte6 ≠ 0 ? 1
: 0`), `0xd68 add a0,a0,a3` (`+ 8(j+1)`), `0xd6c addi a0,a0,-2`, `0xd70 ret`.  The
result is `a0 = snez(byte6) + 8(j+1) - 2 = len`: for `len = 8j+6`, byte 6 is the NUL so
`snez = 0` giving `8j+6`; for `len = 8j+7`, byte 6 is a char so `snez = 1` giving
`8j+7`. -/

/-- The `snez` value as a `Nat`: `1` iff byte `≠ 0`, else `0`. -/
theorem snez_toNat (b : BitVec 8) :
    (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (zero_extend (m := 64) b)))).toNat
      = (if b = 0 then 0 else 1) := by
  rcases (Decidable.em (b = 0)) with h | h
  · subst h; decide
  · simp only [if_neg h]
    have hpos : 0 < (zero_extend (m := 64) b).toNat := by
      rcases Nat.eq_zero_or_pos (zero_extend (m := 64) b).toNat with hz | hp
      · exfalso; apply h; apply BitVec.eq_of_toNat_eq
        simpa [zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth,
          Nat.mod_eq_of_lt (show b.toNat < 2^64 from by have := b.isLt; omega)] using hz
      · exact hp
    have : zopz0zI_u (0#64) (zero_extend (m := 64) b) = true := by
      unfold zopz0zI_u Sail.BitVec.toNatInt
      simp only [decide_eq_true_eq, Int.ofNat_eq_natCast]
      rw [show (0#64 : BitVec 64).toNat = 0 from rfl]; exact_mod_cast hpos
    rw [this]; rfl

/-! ### Byte-tail assembly (`WTail → Done`)

Dispatch on `i₀ = len - 8j ∈ {0,…,7}`.  For `i₀ ≤ 5` the tail scans offsets `0..i₀-1`
(each nonzero, via `tdec_next`) then exits at offset `i₀` (`tdec_exit`).  For `i₀ ∈
{6,7}` it scans through offset 5 then takes the `snez` path (`tdec_snez`). -/

/-! ### Byte-at-a-time alignment head (`0xd74 … 0xd90`), NUL-in-head exit

For the unaligned entry path (`bnez a5` taken at `0xcf8` → `0xd78`), the code peels
bytes one at a time until either it finds the NUL (this section) or reaches an
8-aligned pointer (then the word loop scans the rest — that exit requires the
offset-generalized word loop, noted at the end of file).

Head-loop head `0xd78`, having peeled `m` bytes (`a4 = base + m`, `m ≤ len`, no NUL in
`[base, base+m)`, `(base+m) % 8 ≠ 0` — else we would have exited to the word loop):
`0xd78 lbu a5,0(a4)` loads byte `base+m`, `0xd7c addi a4,a4,1`, `0xd80 andi a3,a4,7`,
`0xd84 bnez a5,d74`.  If the byte is `0` (`m = len`), `bnez` falls through to `0xd88`
`sub a4,a4,a0`; `0xd8c addi a0,a4,-1`; `0xd90 ret`, returning `a0 = (m+1) - 1 = m = len`.

`HSt base r len cs m0 m`: the head-loop head observation at `0xd78`.  We prove the
NUL-exit (`byte = 0` ⇒ `Done`) here; the alignment-exit is the remaining item. -/

/-! ## The aligned-path `strlen` spec (`Pre → Done`)

For the 8-aligned fast path: entry + magic setup → word loop → byte tail → return.
`r` must be 4-aligned (so `ret`'s bit-0 clear is a no-op). -/

/-! ## Top-level `strlen` specification

`strlen_pre`/`strlen_post` package the prompt's P/Q.  The precondition pins the
entry configuration (`PC = 0x80006cf0`, `x10 = p`, `x1 = r` 4-aligned, `mem = m0`), a
`CString m0 p s` string of length `s.length`, and the `StrRegions` disjointness /
no-wrap side conditions.  The postcondition returns to `r` with `x10 = ofNat
s.length`, `x1 = r`, `mem = m0` (strlen never stores).

`strlen_spec` is proved here for the **8-aligned fast path** (`p.toNat % 8 = 0`), the
common case the caller controls; it composes the fully verified entry, magic setup,
word loop, byte tail, and exit blocks.  The unaligned head-peel path is discussed in
the closing note. -/

/-! ## Unaligned head-peel path — status

The byte-at-a-time alignment head (`0xd74 … 0xd90`) is fully modelled: `head_body`
(`0xd78 → 0xd84`), `head_nul_exit` (`0xd84` bnez not-taken, `m = len` ⇒ `Done` with
`a0 = m = len`), and `head_continue` (`0xd84` taken + `0xd74` not-taken ⇒ `HSt (m+1)`).

Two items complete the unaligned path (`bnez a5` taken at `0xcf8`):

1. **Head loop assembly** (`Triple.loop` over `HSt m ∨ Done`, measure `len + 1 - m`,
   PC-guarded at `0xd78`): straightforward from `head_body`/`head_nul_exit`/
   `head_continue` in the pattern of `wloop_to_tail`, plus the unaligned entry
   `0xcf0 → 0xd78` (`andi`; `mv`; `bnez` taken).

2. **Alignment exit** (`0xd74` beqz taken ⇒ `0xcfc`, re-entering the magic setup then
   the word loop with `a4` 8-aligned but `a0 = base ≠ a4`).  This is the one piece
   that needs the word loop **offset-generalized**: the verified `WSt`/`W28`/`WTail`/
   `TDec` and their transitions carry a single scan base `p` used simultaneously for
   `a0`, the string origin, and the aligned addresses.  For the alignment exit these
   must be decoupled — `a0 = base` (length origin), scan base `q = base + off0`
   (aligned), length positions `off0 + 8j + k` — a mechanical parameterization (the
   aligned spec is the `off0 = 0` instance).  Every arithmetic lemma already generalizes
   (`detect_taken/nottaken`, `exit_addi_val`, `snez_final` are stated over the length
   index, not `p`); only the structure fields and the ~20 site-threading proofs need the
   extra `off0`/`base` parameters.  No new mathematical content is required.
-/

/-! ## Frame-preserving `strlen` spec (`strlen_spec_framed`)

The composition consumers (`EnvDefCompose`) need `strlen` to preserve the caller's
ABI-callee-saved register frame across the call: the exact "missing preservation
clauses" the ledger flagged.  `strlen` physically preserves them — its 8-aligned fast
path writes ONLY `{x1, x10, x11, x12, x13, x14, x15}` (`ra`, `a0…a5`), and
`AbiPreserved` = `{x2,x3,x4,x8,x9,x18…x27}` is disjoint from that set — but the stated
`strlen_post` (PC/x10/x1/mem only) does not express it.

`AbiFrame g c` is the carried register frame (`∀ R, AbiPreserved R → get? R = g R`)
plus the intra-tick bound `c.tick < 2`.  We thread it through the whole aligned chain
(entry ≫ word loop ≫ byte tail ≫ ret) as an explicit conjunct, re-running the SAME
per-site observations used by the unframed spec and lifting the frame at each step via
the `strlenFrame_*` readbacks (built directly from `get?_sigmaPost_*`, no `strcmp`
dependency — `StrcmpSpec` imports this file, so its `sframe_*` are unreachable here).

The frame survives every site because the written register is never `AbiPreserved`
(`abiPreserved_wr` closes `(rd == R) = false` from `AbiPreserved R` by `decide` on the
concrete `rd`).  Memory is unchanged (already in `strlen_post`), so any mem-and-gp
–stable allocator invariant survives as a downstream corollary. -/

/-! ### Framed block Triples — re-run each aligned block carrying `AbiFrame g`.

Each mirrors its unframed sibling (`entry_aligned`/`wloop_to_tail`/`wattail_to_done`),
threading the ghost tie `hghost : ∀R, AbiPreserved R → get? R = g R` across every site
via the `strlenFrame_*` readbacks.  `c.tick < 2` re-derives at the exit from the site's
`i' < 2` (the observations carry it) — bundled into `AbiFrame`. -/

/-! ### Framed byte tail — re-run each tail piece carrying the ghost.

Each piece writes only `{x10,x13,x15}` (`a0/a3/a5`) plus branches — none `AbiPreserved`
— so the frame survives every site via `strlenFrame_alu`/`strlenFrame_btaken`/
`strlenFrame_bnottaken`.  We provide framed siblings for the pieces the aligned tail
composes, then reassemble exactly as `tail_to_done`/`wattail_to_done`. -/

/-! ### Concrete framed advances/exits — thin wrappers over the generics. -/

/-! ### Exponentiating tail composition.

The dispatch composes at most five `next` advances then one `exit`.  To keep
elaboration linear (avoid the deep-nested-`.seq` whnf blowup + eager per-offset
`decide`s), each offset's advance/exit is packaged as a **standalone framed Triple
theorem** (`next{0..4}_framed`, `exit{0..5}_framed`, `tdec_snez_framed`) whose heavy
`decide`s are paid ONCE at that theorem's own elaboration, and the assembly composes
them by name — a plain `.seq` fold over already-checked constants (rule: emit plain
terms, seams `rfl`, no re-elaboration of leaf `decide`s).

The concrete `exit{k}_framed` wrappers each apply the `exitk_framed` generic with the
offset's literals; the 64-bit `BitVec` side `decide`s are paid once per wrapper. -/

