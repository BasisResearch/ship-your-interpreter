import Vsa.Sim.StrcmpSpec

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

/-- The `auipc`-computed base `0x80006eb0 + (0x14 <<< 12)` equals `0x8001aeb0`. -/
theorem auipc_mask_base :
    ((0x80006eb0#64) + sign_extend (m := 64) ((0x00014#20) +++ 0x000#12)) = (0x8001aeb0#64 : BitVec 64) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- The `ld` effective address `0x8001aeb0 + sext(0xdd0) = 0x8001ac80`. -/
theorem mask_ld_addr :
    ((0x8001aeb0#64 : BitVec 64) + sign_extend (m := 64) (0xdd0#12)).toNat = maskAddr := by
  decide

/-- The total 8-byte load at `maskAddr` yields `magic7f`, given the 8 pinned bytes.
Each byte of `ldBytesT` (`getD 0`) is `0x7f`; the little-endian assembly is `magic7f`. -/
theorem ldBytesT_mask (σ : SequentialState RegisterType trivialChoiceSource)
    (hmask : MaskPinned σ.mem) :
    ldBytesT σ (0x8001ac80#64) = magic7f := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hmask
  have hshow : ldBytesT σ (0x8001ac80#64) =
    ((((((((σ.mem[maskAddr + 7]?).getD 0) +++ ((σ.mem[maskAddr + 6]?).getD 0)) +++
     ((σ.mem[maskAddr + 5]?).getD 0)) +++ ((σ.mem[maskAddr + 4]?).getD 0)) +++
     ((σ.mem[maskAddr + 3]?).getD 0)) +++ ((σ.mem[maskAddr + 2]?).getD 0)) +++
     ((σ.mem[maskAddr + 1]?).getD 0)) +++ ((σ.mem[maskAddr]?).getD 0) := rfl
  rw [hshow, h0, h1, h2, h3, h4, h5, h6, h7]
  apply BitVec.eq_of_toNat_eq; decide

/-! ## Word-level detection bridges (two strings)

The word loop compares two 8-aligned words `wa = ld[a0+o]`, `wb = ld[a1+o]` at each
in-body offset `o ∈ {0,8,16}`. `t0 = strlenWordVal wa`; `t2 = allOnes`; the guards
are `bne t0,t2` (`wa` has a NUL byte, via `detect_all_ones`) and `bne a2,a3`
(`wa ≠ wb`). We track the byte-count `n = 24j + o` compared so far.

`WordAgree`: `csa`/`csb` agree byte-for-byte on `[0, n)` and A has no NUL among those
(so neither does B — equal words). Reusing the byte-stream spec functions from
`StrcmpSpec` (`byteVal`, `BytePrefix`), the word invariant is just `BytePrefix csa csb n`
whose bytes are drawn 8 at a time. -/

/-- The 8-aligned word of `m0` at address `a` (little-endian `getD 0`), reusing the
`strlenWordAt` ghost. -/
abbrev cwordAt (m0 : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) : BitVec 64 :=
  strlenWordAt m0 a

/-- Byte `k` (`k < 8`) of `cwordAt m0 a` is the memory byte at `a + k`. Mirrors
`ldBytesT_byte` (same `append` structure). -/
theorem cwordAt_byte (m0 : Std.ExtHashMap Nat (BitVec 8)) (a k : Nat) (hk : k < 8) :
    (cwordAt m0 a).extractLsb' (8*k) 8 = (m0[a + k]?).getD 0 := by
  show (strlenWordAt m0 a).extractLsb' (8*k) 8 = (m0[a + k]?).getD 0
  have hshow : strlenWordAt m0 a =
    ((((((((m0[a + 7]?).getD 0) +++ ((m0[a + 6]?).getD 0)) +++
     ((m0[a + 5]?).getD 0)) +++ ((m0[a + 4]?).getD 0)) +++
     ((m0[a + 3]?).getD 0)) +++ ((m0[a + 2]?).getD 0)) +++
     ((m0[a + 1]?).getD 0)) +++ ((m0[a + 0]?).getD 0) := by
    simp only [strlenWordAt, Nat.add_zero]; rfl
  rw [hshow]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  rw [decide_eq_true (show i < 8 from hi), Bool.true_and]
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
    congr 1 <;> omega

/-! ### Magic detection specialised to a CStr at word offset `n`

At the group whose word covers bytes `[n, n+8)` of the `csa`-string based at `pa`,
`strlenWordVal (cwordAt m0 (pa.toNat + n))`:
* `= allOnes` iff bytes `[n, n+8)` are all nonzero, i.e. `n + 8 ≤ la` (word NUL-free);
* `≠ allOnes` iff some byte in `[n, n+8)` is the NUL, i.e. `la < n + 8` (word has NUL).

Reuses `detect_all_ones` (from `StrlenMagic`) over the memory bytes. -/

/-- Word at `pa.toNat + n` is NUL-free iff `n + 8 ≤ la`, for a `CStr`-string.
Forward direction (used for the continue/differ cases): `n + 8 ≤ la` ⇒ all-ones. -/
theorem word_nul_free (m0 : Std.ExtHashMap Nat (BitVec 8)) (pa : BitVec 64) (csa : List Char)
    (hcstr : CStr m0 pa.toNat csa) (n : Nat) (hle : n + 8 ≤ csa.length) :
    strlenWordVal (cwordAt m0 (pa.toNat + n)) = BitVec.allOnes 64 := by
  rw [detect_all_ones]
  intro k hk
  rw [cwordAt_byte m0 _ k hk]
  obtain ⟨b, hb, hbne⟩ := cstr_byte_ne m0 hcstr (n + k) (by omega)
  rw [show pa.toNat + n + k = pa.toNat + (n + k) from by omega, hb]
  simpa using hbne

/-- Word at `pa.toNat + n` contains a NUL iff `n ≤ la < n + 8`, for a `CStr`-string.
Used for the magic-taken case: `la < n + 8` (with `n ≤ la`) ⇒ NOT all-ones. -/
theorem word_has_nul (m0 : Std.ExtHashMap Nat (BitVec 8)) (pa : BitVec 64) (csa : List Char)
    (hcstr : CStr m0 pa.toNat csa) (n : Nat) (hlo : n ≤ csa.length) (hhi : csa.length < n + 8) :
    strlenWordVal (cwordAt m0 (pa.toNat + n)) ≠ BitVec.allOnes 64 := by
  intro hall
  rw [detect_all_ones] at hall
  have hk : csa.length - n < 8 := by omega
  have := hall (csa.length - n) hk
  rw [cwordAt_byte m0 _ _ hk] at this
  apply this
  have hnul : m0[pa.toNat + csa.length]? = some 0 := cstr_byte_nul m0 hcstr
  rw [show pa.toNat + n + (csa.length - n) = pa.toNat + csa.length from by omega, hnul]
  rfl

/-! ### Word equality ⟺ byte agreement

`cwordAt m0 a = cwordAt m0 b` iff their 8 bytes agree. We need: if the two loaded
words `wa = cwordAt A`, `wb = cwordAt B` are EQUAL, then the byte streams agree on
`[n, n+8)`. And if they DIFFER, some byte in `[n,n+8)` differs. Both go through
`extractLsb'` of the words = memory bytes (`cwordAt_byte`). -/

/-- If two words are equal, their byte `k` (`k<8`) extractions are equal. -/
theorem word_eq_byte (wa wb : BitVec 64) (h : wa = wb) (k : Nat) :
    wa.extractLsb' (8*k) 8 = wb.extractLsb' (8*k) 8 := by rw [h]

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

/-- The `getD 0` byte at offset `k < 8` of the word at `pa.toNat + n` has `toNat`
`byteVal csa (n+k)` when `n + k ≤ la` (string char, or the NUL past-end = 0). -/
theorem cword_byte_byteVal (m0 : Std.ExtHashMap Nat (BitVec 8)) (pa : BitVec 64) (csa : List Char)
    (hcstr : CStr m0 pa.toNat csa) (n k : Nat) (hk : k < 8) (hle : n + k ≤ csa.length) :
    ((cwordAt m0 (pa.toNat + n)).extractLsb' (8*k) 8).toNat = byteVal csa (n+k) := by
  rw [cwordAt_byte m0 _ k hk, show pa.toNat + n + k = pa.toNat + (n+k) from by omega]
  obtain ⟨b, hb, _, hval⟩ := cstr_byte_val m0 pa.toNat csa hcstr (n+k) hle
  rw [hb]; simpa using hval

/-- Memory byte at `pa+i` (for `i ∈ [n,n+8)`) is byte `i-n` of the word at `pa+n`. -/
theorem mem_byte_of_word (m0 : Std.ExtHashMap Nat (BitVec 8)) (pa : BitVec 64)
    (n i : Nat) (hi1 : n ≤ i) (hi2 : i < n + 8) :
    (m0[pa.toNat + i]?).getD 0 = (cwordAt m0 (pa.toNat + n)).extractLsb' (8*(i-n)) 8 := by
  rw [cwordAt_byte m0 _ (i-n) (by omega), show pa.toNat + n + (i-n) = pa.toNat + i from by omega]

/-- **Equal NUL-free words ⇒ B's word is NUL-free too.** If the words at offset `n`
are equal and A's is NUL-free (`n + 8 ≤ la`), then `n + 8 ≤ lb`: else B's NUL byte
`lb ∈ [n, n+8)` would be zero while A's byte there is a nonzero string char. -/
theorem word_eq_lb_free (m0 : Std.ExtHashMap Nat (BitVec 8)) (pa pb : BitVec 64)
    (csa csb : List Char) (hcstra : CStr m0 pa.toNat csa) (hcstrb : CStr m0 pb.toNat csb)
    (n : Nat) (heq : cwordAt m0 (pa.toNat + n) = cwordAt m0 (pb.toNat + n))
    (hnf : n + 8 ≤ csa.length) (hn : n ≤ csb.length) : n + 8 ≤ csb.length := by
  rcases Nat.lt_or_ge csb.length (n + 8) with hlt | hge
  · exfalso
    -- lb ∈ [n, n+8): B's byte at lb is the NUL = 0; A's byte at lb is a nonzero char
    have hlbk : csb.length - n < 8 := by omega
    have hAneq : (m0[pa.toNat + csb.length]?).getD 0 = (m0[pb.toNat + csb.length]?).getD 0 := by
      rw [mem_byte_of_word m0 pa n csb.length hn (by omega),
          mem_byte_of_word m0 pb n csb.length hn (by omega), heq]
    have hBnul : (m0[pb.toNat + csb.length]?).getD 0 = (0 : BitVec 8) := by
      rw [cstr_byte_nul m0 hcstrb]; rfl
    have hAchar : (m0[pa.toNat + csb.length]?).getD 0 ≠ (0 : BitVec 8) := by
      obtain ⟨ba, hba, hbane⟩ := cstr_byte_ne m0 hcstra csb.length (by omega)
      rw [hba]; simpa using hbane
    rw [hAneq, hBnul] at hAchar; exact hAchar rfl
  · exact hge

/-- **Continue extends the prefix.** If `csa`/`csb` agree+nonzero on `[0,n)`
(`BytePrefix n`), the two words at offset `n` are EQUAL, and A's word is NUL-free
(`n + 8 ≤ la`), then bytes `[n, n+8)` also agree and are A-nonzero: `BytePrefix (n+8)`. -/
theorem byte_prefix_extend (m0 : Std.ExtHashMap Nat (BitVec 8)) (pa pb : BitVec 64)
    (csa csb : List Char) (hcstra : CStr m0 pa.toNat csa) (hcstrb : CStr m0 pb.toNat csb)
    (n : Nat) (hpre : BytePrefix csa csb n) (hn : n ≤ csb.length)
    (heq : cwordAt m0 (pa.toNat + n) = cwordAt m0 (pb.toNat + n))
    (hnf : n + 8 ≤ csa.length) : BytePrefix csa csb (n+8) := by
  have hnfb : n + 8 ≤ csb.length := word_eq_lb_free m0 pa pb csa csb hcstra hcstrb n heq hnf hn
  intro i hi
  rcases Nat.lt_or_ge i n with hin | hin
  · exact hpre i hin
  have hk : i - n < 8 := by omega
  have hkn : n + (i - n) = i := by omega
  have hilta : i < csa.length := by omega
  have hiltb : i < csb.length := by omega
  obtain ⟨ba, hba, hbane⟩ := cstr_byte_ne m0 hcstra i hilta
  have hbaval : ba.toNat = byteVal csa i := cstr_byteVal m0 pa.toNat csa hcstra i hilta ba hba hbane
  have hAbyte : ((cwordAt m0 (pa.toNat + n)).extractLsb' (8*(i-n)) 8).toNat = byteVal csa i := by
    rw [cword_byte_byteVal m0 pa csa hcstra n (i-n) hk (by omega), hkn]
  have hBbyteVal : ((cwordAt m0 (pb.toNat + n)).extractLsb' (8*(i-n)) 8).toNat = byteVal csb i := by
    rw [cword_byte_byteVal m0 pb csb hcstrb n (i-n) hk (by omega), hkn]
  refine ⟨?_, ?_⟩
  · -- byteVal csa i = byteVal csb i via the equal words
    have h : ((cwordAt m0 (pa.toNat + n)).extractLsb' (8*(i-n)) 8).toNat
           = ((cwordAt m0 (pb.toNat + n)).extractLsb' (8*(i-n)) 8).toNat := by rw [heq]
    rw [hAbyte, hBbyteVal] at h; exact h
  · rw [← hbaval]; exact fun h => hbane (BitVec.eq_of_toNat_eq (by rw [h]; rfl))

/-! ## Word-loop region / alignment side conditions

`StrcmpWRegion p len` bundles the word-loop disjointness facts for a string
`[p, p+len]`: like `StrRegions` (from `StrlenSpec`) the loop reads 8-aligned words
that may extend up to 7 bytes past `p+len`, so we require `p+len+8 ≤ RAM top` and
`8`-alignment of `p` (the aligned-entry guarantee). Disjoint from the strcmp code and
the HTIF window. -/
structure StrcmpWRegion (p : BitVec 64) (len : Nat) : Prop where
  lo : 0x80000000 ≤ p.toNat
  hi : p.toNat + len + 8 ≤ 0x100000000
  nowrap : p.toNat + len + 8 < 2^64
  code : p.toNat + len + 8 ≤ 0x80006ea0 ∨ 0x80006fcc ≤ p.toNat
  htif : p.toNat + len + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ p.toNat
  align : p.toNat % 8 = 0

/-- Bounds the total `ld` at word offset `n` (`n ≤ len`, `n % 8 = 0`) needs: the
address `p+n` is in RAM, 8-aligned, disjoint from HTIF. -/
theorem wcmp_load_bounds (p : BitVec 64) (len n : Nat) (hreg : StrcmpWRegion p len)
    (hn : n ≤ len) (hn8 : n % 8 = 0) :
    (p + BitVec.ofNat 64 n).toNat = p.toNat + n ∧
    0x80000000 ≤ ((p + BitVec.ofNat 64 n) + sign_extend (m := 64) (0x000#12)).toNat ∧
    ((p + BitVec.ofNat 64 n) + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000 ∧
    (((p + BitVec.ofNat 64 n) + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ ((p + BitVec.ofNat 64 n) + sign_extend (m := 64) (0x000#12)).toNat) ∧
    ((p + BitVec.ofNat 64 n) + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0 := by
  have htn : (p + BitVec.ofNat 64 n).toNat = p.toNat + n :=
    ptrN p n (by have := hreg.nowrap; omega)
  have hlo := hreg.lo
  have hhi := hreg.hi
  have hh := hreg.htif
  have halgn := hreg.align
  have htoh : tohostAddr = 0x8001ad00 := rfl
  refine ⟨htn, ?_, ?_, ?_, ?_⟩
  all_goals rw [sext0_add, htn]
  · omega
  · omega
  · rcases hh with h | h
    · left; omega
    · right; omega
  · omega

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

/-- Loop-head observation at `0xeb8`, word iteration `j` (stride 24). -/
structure WHead (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (j : Nat) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrcmpLoaded c.σ.mem
  mem : c.σ.mem = m0
  pc : c.σ.regs.get? Register.PC = some (0x80006eb8#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some (pa + BitVec.ofNat 64 (24*j))
  a1 : c.σ.regs.get? Register.x11 = some (pb + BitVec.ofNat 64 (24*j))
  a5 : c.σ.regs.get? Register.x15 = some magic7f
  t2 : c.σ.regs.get? Register.x7 = some (BitVec.allOnes 64)
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  rega : StrcmpWRegion pa csa.length
  regb : StrcmpWRegion pb csb.length
  cstra : CStr m0 pa.toNat csa
  cstrb : CStr m0 pb.toNat csb
  maskpin : MaskPinned m0
  prefixEq : BytePrefix csa csb (24*j)
  jle : 24*j ≤ csa.length
  hframe : ∀ R : Register, NotWrittenStrcmp R → c.σ.regs.get? R = g R

/-- `((w &&& magic7f) + magic7f) ||| (w ||| magic7f) = strlenWordVal w`
(or-associativity: the site computes `t0|t1`, we want `((..)|w)|m`). -/
theorem strcmpWordVal_eq (w : BitVec 64) :
    (((w &&& magic7f) + magic7f) ||| (w ||| magic7f)) = strlenWordVal w := by
  show _ = (((w &&& magic7f) + magic7f) ||| w) ||| magic7f
  rw [BitVec.or_assoc]

/-- State at `0xed0` (`bne t0,t2`) after group-0 straight-line: `t0 = strlenWordVal wa`,
`a2 = wa`, `a3 = wb`, `t2 = allOnes`, pointers unchanged (`a0 = pa+24j`, `a1 = pb+24j`),
`a5 = magic7f`. `wa`/`wb` are the ghost words at the current offset `24j`. -/
structure WG0mid (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (j : Nat) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrcmpLoaded c.σ.mem
  mem : c.σ.mem = m0
  pc : c.σ.regs.get? Register.PC = some (0x80006ed0#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some (pa + BitVec.ofNat 64 (24*j))
  a1 : c.σ.regs.get? Register.x11 = some (pb + BitVec.ofNat 64 (24*j))
  a2 : c.σ.regs.get? Register.x12 = some (cwordAt m0 (pa.toNat + 24*j))
  a3 : c.σ.regs.get? Register.x13 = some (cwordAt m0 (pb.toNat + 24*j))
  a5 : c.σ.regs.get? Register.x15 = some magic7f
  t0 : c.σ.regs.get? Register.x5 = some (strlenWordVal (cwordAt m0 (pa.toNat + 24*j)))
  t2 : c.σ.regs.get? Register.x7 = some (BitVec.allOnes 64)
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  rega : StrcmpWRegion pa csa.length
  regb : StrcmpWRegion pb csb.length
  cstra : CStr m0 pa.toNat csa
  cstrb : CStr m0 pb.toNat csb
  maskpin : MaskPinned m0
  prefixEq : BytePrefix csa csb (24*j)
  jle : 24*j ≤ csa.length
  hframe : ∀ R : Register, NotWrittenStrcmp R → c.σ.regs.get? R = g R

/-- Group-0 straight-line `0xeb8 → 0xed0`: two `ld`s and the four magic-ALU ops.
Produces `WG0mid` (`t0 = strlenWordVal wa`). -/
theorem wg0_straight (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (j : Nat) :
    Triple (WHead g pa pb r csa csb m0 j) (WG0mid g pa pb r csa csb m0 j) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha1, ha5, ht2, hra, ⟨vmi, hmi⟩, htick,
    hrega, hregb, hcstra, hcstrb, hmaskpin, hpre, hjle, hframe⟩ := hSt
  -- offset-0 load address bounds for A and B
  obtain ⟨htna, hloa, hhia, hhtifa, halgna⟩ := wcmp_load_bounds pa csa.length (24*j) hrega hjle (by omega)
  -- === eb8: ld a2,0(a0) === (total load) → a2 = cwordAt m0 (pa.toNat + 24j)
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006eb8 c.σ c.tick c.steps (0x80006eb8#64) vmi (pa + BitVec.ofNat 64 (24*j))
      hgood hpc hmi ha0 hloaded rfl hloa hhia hhtifa halgna htick
  have hwordA : (sign_extend (m := 64)
      (ldBytesT (afterNextPC (afterPrelude c.σ) (0x80006eb8#64))
        (pa + BitVec.ofNat 64 (24*j) + sign_extend (m := 64) (0x000#12))))
      = cwordAt m0 (pa.toNat + 24*j) := by
    rw [sext64_self, sext0_add, ldBytesT_wordAt, mem_afterNextPC, mem_afterPrelude, hmem, htna]
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006ebc#64 : BitVec 64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x80006eb8#64) 4 = (0x80006ebc#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_alu_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have ha1_1 := obs_alu_other hobs1 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1
  have ha5_1 := obs_alu_other hobs1 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha5
  have ht2_1 := obs_alu_other hobs1 Register.x7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ht2
  have ha2_1 : σ1.regs.get? Register.x12 = some (cwordAt m0 (pa.toNat + 24*j)) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [hwordA] at this
  have hra_1 := obs_alu_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  have hframe_1 : ∀ R, NotWrittenStrcmp R → σ1.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs1 R hR.2.2.2.2.2.1 hR).trans (hframe R hR)
  obtain ⟨vmi1, hmi1'⟩ := obs_alu_minstret hobs1
  -- offset-0 load bounds for B
  have hjleb : 24*j ≤ csb.length := prefix_le_lenb hpre
  obtain ⟨htnb, hlob, hhib, hhtifb, halgnb⟩ := wcmp_load_bounds pb csb.length (24*j) hregb hjleb (by omega)
  -- === ebc: ld a3,0(a1) === → a3 = cwordAt m0 (pb.toNat + 24j)
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006ebc σ1 i1 (c.steps + 1) (0x80006ebc#64) vmi1 (pb + BitVec.ofNat 64 (24*j))
      hG1 hpc1 hmi1' ha1_1 (by rw [hmem1]; exact hloaded) rfl hlob hhib hhtifb halgnb hi1
  have hwordB : (sign_extend (m := 64)
      (ldBytesT (afterNextPC (afterPrelude σ1) (0x80006ebc#64))
        (pb + BitVec.ofNat 64 (24*j) + sign_extend (m := 64) (0x000#12))))
      = cwordAt m0 (pb.toNat + 24*j) := by
    rw [sext64_self, sext0_add, ldBytesT_wordAt, mem_afterNextPC, mem_afterPrelude, hmem1, hmem, htnb]
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006ec0#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006ebc#64) 4 = (0x80006ec0#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_1
  have ha1_2 := obs_alu_other hobs2 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_1
  have ha2_2 := obs_alu_other hobs2 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha2_1
  have ha5_2 := obs_alu_other hobs2 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha5_1
  have ht2_2 := obs_alu_other hobs2 Register.x7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ht2_1
  have ha3_2 : σ2.regs.get? Register.x13 = some (cwordAt m0 (pb.toNat + 24*j)) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [hwordB] at this
  have hra_2 := obs_alu_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
  have hframe_2 : ∀ R, NotWrittenStrcmp R → σ2.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs2 R hR.2.2.2.2.2.2.1 hR).trans (hframe_1 R hR)
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  -- === ec0: and t0,a2,a5 === → t0 = wa &&& magic7f
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80006ec0 σ2 i2 (c.steps + 1 + 1) (0x80006ec0#64) vmi2 (cwordAt m0 (pa.toNat + 24*j)) magic7f
      hG2 hpc2 hmi2' ha2_2 ha5_2 (by rw [hmem2, hmem1]; exact hloaded) rfl hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x80006ec4#64 : BitVec 64) := by
    have := obs_alu_pc hobs3; rwa [show BitVec.addInt (0x80006ec0#64) 4 = (0x80006ec4#64 : BitVec 64) from by decide] at this
  have ha0_3 := obs_alu_other hobs3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_2
  have ha1_3 := obs_alu_other hobs3 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_2
  have ha2_3 := obs_alu_other hobs3 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha2_2
  have ha3_3 := obs_alu_other hobs3 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3_2
  have ha5_3 := obs_alu_other hobs3 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha5_2
  have ht2_3 := obs_alu_other hobs3 Register.x7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ht2_2
  have ht0_3 : σ3.regs.get? Register.x5 = some (cwordAt m0 (pa.toNat + 24*j) &&& magic7f) :=
    obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hra_3 := obs_alu_other hobs3 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_2
  have hframe_3 : ∀ R, NotWrittenStrcmp R → σ3.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs3 R hR.1 hR).trans (hframe_2 R hR)
  obtain ⟨vmi3, hmi3'⟩ := obs_alu_minstret hobs3
  -- === ec4: or t1,a2,a5 === → t1 = wa ||| magic7f
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80006ec4 σ3 i3 (c.steps + 1 + 1 + 1) (0x80006ec4#64) vmi3 (cwordAt m0 (pa.toNat + 24*j)) magic7f
      hG3 hpc3 hmi3' ha2_3 ha5_3 (by rw [hmem3, hmem2, hmem1]; exact hloaded) rfl hi3
  have hpc4 : σ4.regs.get? Register.PC = some (0x80006ec8#64 : BitVec 64) := by
    have := obs_alu_pc hobs4; rwa [show BitVec.addInt (0x80006ec4#64) 4 = (0x80006ec8#64 : BitVec 64) from by decide] at this
  have ha0_4 := obs_alu_other hobs4 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_3
  have ha1_4 := obs_alu_other hobs4 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_3
  have ha2_4 := obs_alu_other hobs4 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha2_3
  have ha3_4 := obs_alu_other hobs4 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3_3
  have ha5_4 := obs_alu_other hobs4 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha5_3
  have ht2_4 := obs_alu_other hobs4 Register.x7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ht2_3
  have ht0_4 := obs_alu_other hobs4 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ht0_3
  have ht1_4 : σ4.regs.get? Register.x6 = some (cwordAt m0 (pa.toNat + 24*j) ||| magic7f) :=
    obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hra_4 := obs_alu_other hobs4 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_3
  have hframe_4 : ∀ R, NotWrittenStrcmp R → σ4.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs4 R hR.2.1 hR).trans (hframe_3 R hR)
  obtain ⟨vmi4, hmi4'⟩ := obs_alu_minstret hobs4
  -- === ec8: add t0,t0,a5 === → t0 = (wa&&&m) + m
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80006ec8 σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x80006ec8#64) vmi4
      (cwordAt m0 (pa.toNat + 24*j) &&& magic7f) magic7f
      hG4 hpc4 hmi4' ht0_4 ha5_4 (by rw [hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi4
  have hpc5 : σ5.regs.get? Register.PC = some (0x80006ecc#64 : BitVec 64) := by
    have := obs_alu_pc hobs5; rwa [show BitVec.addInt (0x80006ec8#64) 4 = (0x80006ecc#64 : BitVec 64) from by decide] at this
  have ha0_5 := obs_alu_other hobs5 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_4
  have ha1_5 := obs_alu_other hobs5 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_4
  have ha2_5 := obs_alu_other hobs5 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha2_4
  have ha3_5 := obs_alu_other hobs5 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3_4
  have ha5_5 := obs_alu_other hobs5 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha5_4
  have ht2_5 := obs_alu_other hobs5 Register.x7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ht2_4
  have ht1_5 := obs_alu_other hobs5 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ht1_4
  have ht0_5 : σ5.regs.get? Register.x5 = some ((cwordAt m0 (pa.toNat + 24*j) &&& magic7f) + magic7f) :=
    obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hra_5 := obs_alu_other hobs5 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_4
  have hframe_5 : ∀ R, NotWrittenStrcmp R → σ5.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs5 R hR.1 hR).trans (hframe_4 R hR)
  obtain ⟨vmi5, hmi5'⟩ := obs_alu_minstret hobs5
  -- === ecc: or t0,t0,t1 === → t0 = ((wa&&&m)+m) ||| (wa|||m) = strlenWordVal wa
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_80006ecc σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x80006ecc#64) vmi5
      ((cwordAt m0 (pa.toNat + 24*j) &&& magic7f) + magic7f) (cwordAt m0 (pa.toNat + 24*j) ||| magic7f)
      hG5 hpc5 hmi5' ht0_5 ht1_5 (by rw [hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi5
  have hpc6 : σ6.regs.get? Register.PC = some (0x80006ed0#64 : BitVec 64) := by
    have := obs_alu_pc hobs6; rwa [show BitVec.addInt (0x80006ecc#64) 4 = (0x80006ed0#64 : BitVec 64) from by decide] at this
  have ha0_6 := obs_alu_other hobs6 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_5
  have ha1_6 := obs_alu_other hobs6 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_5
  have ha2_6 := obs_alu_other hobs6 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha2_5
  have ha3_6 := obs_alu_other hobs6 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3_5
  have ha5_6 := obs_alu_other hobs6 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha5_5
  have ht2_6 := obs_alu_other hobs6 Register.x7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ht2_5
  have ht0_6 : σ6.regs.get? Register.x5 = some (strlenWordVal (cwordAt m0 (pa.toNat + 24*j))) := by
    have := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [strcmpWordVal_eq] at this
  have hra_6 := obs_alu_other hobs6 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_5
  have hframe_6 : ∀ R, NotWrittenStrcmp R → σ6.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs6 R hR.1 hR).trans (hframe_5 R hR)
  obtain ⟨vmi6, hmi6'⟩ := obs_alu_minstret hobs6
  have hmem6eq : σ6.mem = c.σ.mem := by rw [hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]
  refine ⟨⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩,
    (((((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans
      (Steps.single hs4)).trans (Steps.single hs5)).trans (Steps.single hs6), ?_⟩
  exact ⟨hG6, by rw [hmem6eq]; exact hloaded, by rw [hmem6eq]; exact hmem, hpc6, ha0_6, ha1_6,
    ha2_6, ha3_6, ha5_6, ht0_6, ht2_6, hra_6, ⟨vmi6, hmi6'⟩, hi6, hrega, hregb, hcstra, hcstrb,
    hmaskpin, hpre, hjle, hframe_6⟩

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

/-- Lane-compare entry `0xf20`: the two words at group offset `n = 24j + o` differ and
A's word is NUL-free (`n + 8 ≤ la`). `a2 = wa`, `a3 = wb`. The machine's `slli/srli`
probes over `a2`/`a3` isolate the first differing byte. -/
structure WLaneCmp (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (n : Nat) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrcmpLoaded c.σ.mem
  mem : c.σ.mem = m0
  pc : c.σ.regs.get? Register.PC = some (0x80006f20#64 : BitVec 64)
  a2 : c.σ.regs.get? Register.x12 = some (cwordAt m0 (pa.toNat + n))
  a3 : c.σ.regs.get? Register.x13 = some (cwordAt m0 (pb.toNat + n))
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  rega : StrcmpWRegion pa csa.length
  regb : StrcmpWRegion pb csb.length
  cstra : CStr m0 pa.toNat csa
  cstrb : CStr m0 pb.toNat csb
  prefixEq : BytePrefix csa csb n
  nulfree : n + 8 ≤ csa.length
  wne : cwordAt m0 (pa.toNat + n) ≠ cwordAt m0 (pb.toNat + n)
  hframe : ∀ R : Register, NotWrittenStrcmp R → c.σ.regs.get? R = g R

/-- Group-0 three-way dispatch `0xed0 → {0xfac, 0xf20, 0xed8}` from `WG0mid`:
`bne t0,t2` then `bne a2,a3`. Emits: (a) A-word NUL → head at `0xfac` (the group-0
NUL-exit; we surface it as the raw PC-state fact plus the byte-level `la < 24j+8`);
(b) words differ, A NUL-free → `WLaneCmp` at `0xf20`; (c) equal + NUL-free →
`WHead`-successor state at `0xed8` with `BytePrefix (24j+8)`. To keep the interface
uniform we return the disjunction of the three PC-tagged states. -/
theorem wg0_dispatch (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (j : Nat) :
    Triple (WG0mid g pa pb r csa csb m0 j)
      (fun c =>
        -- (a) NUL-exit at 0xfac: A's word has the NUL
        (c.σ.regs.get? Register.PC = some (0x80006fac#64 : BitVec 64) ∧
          csa.length < 24*j + 8 ∧ 24*j ≤ csa.length ∧ c.σ.mem = m0 ∧ GoodState c.σ ∧ c.tick < 2)
        -- (b) lane compare at 0xf20
        ∨ WLaneCmp g pa pb r csa csb m0 (24*j) c
        -- (c) continue: at 0xed8 with prefix extended (surfaced as a raw PC/prefix fact)
        ∨ (c.σ.regs.get? Register.PC = some (0x80006ed8#64 : BitVec 64) ∧
          BytePrefix csa csb (24*j + 8) ∧ 24*j + 8 ≤ csa.length ∧ c.σ.mem = m0 ∧
          GoodState c.σ ∧ c.tick < 2)) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha1, ha2, ha3, ha5, ht0, ht2, hra, ⟨vmi, hmi⟩, htick,
    hrega, hregb, hcstra, hcstrb, hmaskpin, hpre, hjle, hframe⟩ := hSt
  by_cases hnul : strlenWordVal (cwordAt m0 (pa.toNat + 24*j)) = BitVec.allOnes 64
  · -- t0 = allOnes ⇒ A's word is NUL-free (24j+8 ≤ la); bne t0,t2 NOT taken → 0xed4
    have hguard : ((strlenWordVal (cwordAt m0 (pa.toNat + 24*j))) != (BitVec.allOnes 64)) = false := by rw [hnul]; simp
    obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
      site_80006ed0_nottaken c.σ c.tick c.steps (0x80006ed0#64) vmi
        (strlenWordVal (cwordAt m0 (pa.toNat + 24*j))) (BitVec.allOnes 64)
        hgood hpc hmi ht0 ht2 hloaded rfl hguard htick
    have hpc1 : σ1.regs.get? Register.PC = some (0x80006ed4#64 : BitVec 64) := by
      have := obs_bnottaken_pc hobs1; rwa [show BitVec.addInt (0x80006ed0#64) 4 = (0x80006ed4#64 : BitVec 64) from by decide] at this
    have ha2_1 := obs_bnottaken_other hobs1 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha2
    have ha3_1 := obs_bnottaken_other hobs1 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3
    have hra_1 := obs_bnottaken_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
    have hframe_1 : ∀ R, NotWrittenStrcmp R → σ1.regs.get? R = g R :=
      fun R hR => (sframe_bnottaken hobs1 R hR).trans (hframe R hR)
    obtain ⟨vmi1, hmi1'⟩ := obs_bnottaken_minstret hobs1
    have hmem1eq : σ1.mem = c.σ.mem := hmem1
    -- A NUL-free: 24j + 8 ≤ la (else word would contain the NUL, contradicting all-ones)
    have hnf : 24*j + 8 ≤ csa.length := by
      rcases Nat.lt_or_ge csa.length (24*j + 8) with hlt | hge
      · exact absurd hnul (word_has_nul m0 pa csa hcstra (24*j) hjle hlt)
      · exact hge
    by_cases hwordeq : cwordAt m0 (pa.toNat + 24*j) = cwordAt m0 (pb.toNat + 24*j)
    · -- bne a2,a3 NOT taken → 0xed8; extend prefix
      have hguard2 : ((cwordAt m0 (pa.toNat + 24*j)) != (cwordAt m0 (pb.toNat + 24*j))) = false := by rw [hwordeq]; simp
      obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
        site_80006ed4_nottaken σ1 i1 (c.steps + 1) (0x80006ed4#64) vmi1
          (cwordAt m0 (pa.toNat + 24*j)) (cwordAt m0 (pb.toNat + 24*j))
          hG1 hpc1 hmi1' ha2_1 ha3_1 (by rw [hmem1]; exact hloaded) rfl hguard2 hi1
      have hpc2 : σ2.regs.get? Register.PC = some (0x80006ed8#64 : BitVec 64) := by
        have := obs_bnottaken_pc hobs2; rwa [show BitVec.addInt (0x80006ed4#64) 4 = (0x80006ed8#64 : BitVec 64) from by decide] at this
      have hmem2eq : σ2.mem = c.σ.mem := by rw [hmem2, hmem1]
      have hpre1 : BytePrefix csa csb (24*j + 8) :=
        byte_prefix_extend m0 pa pb csa csb hcstra hcstrb (24*j) hpre (prefix_le_lenb hpre) hwordeq hnf
      refine ⟨⟨σ2, i2, c.steps + 1 + 1⟩, (Steps.single hs1).trans (Steps.single hs2), Or.inr (Or.inr ?_)⟩
      exact ⟨hpc2, hpre1, hnf, by rw [hmem2eq]; exact hmem, hG2, hi2⟩
    · -- bne a2,a3 taken → 0xf20 lane compare
      have hguard2 : ((cwordAt m0 (pa.toNat + 24*j)) != (cwordAt m0 (pb.toNat + 24*j))) = true := by rw [bne_iff_ne]; exact hwordeq
      obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
        site_80006ed4_taken σ1 i1 (c.steps + 1) (0x80006ed4#64) vmi1
          (cwordAt m0 (pa.toNat + 24*j)) (cwordAt m0 (pb.toNat + 24*j))
          hG1 hpc1 hmi1' ha2_1 ha3_1 (by rw [hmem1]; exact hloaded) rfl hguard2 hi1
      have hpceq : (0x80006ed4#64 : BitVec 64) + sign_extend (m := 64) (0x004c#13) = (0x80006f20#64 : BitVec 64) := by
        apply BitVec.eq_of_toNat_eq; decide
      have hpc2 : σ2.regs.get? Register.PC = some (0x80006f20#64 : BitVec 64) := by
        rw [obs_btaken_pc hobs2, hpceq]
      have ha2_2 := obs_btaken_other hobs2 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha2_1
      have ha3_2 := obs_btaken_other hobs2 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3_1
      have hra_2 := obs_btaken_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
      have hframe_2 : ∀ R, NotWrittenStrcmp R → σ2.regs.get? R = g R :=
        fun R hR => (sframe_btaken hobs2 R hR).trans (hframe_1 R hR)
      obtain ⟨vmi2, hmi2'⟩ := obs_btaken_minstret hobs2
      have hmem2eq : σ2.mem = c.σ.mem := by rw [hmem2, hmem1]
      refine ⟨⟨σ2, i2, c.steps + 1 + 1⟩, (Steps.single hs1).trans (Steps.single hs2), Or.inr (Or.inl ?_)⟩
      exact ⟨hG2, by rw [hmem2eq]; exact hloaded, by rw [hmem2eq]; exact hmem, hpc2, ha2_2, ha3_2,
        hra_2, ⟨vmi2, hmi2'⟩, hi2, hrega, hregb, hcstra, hcstrb, hpre, hnf, hwordeq, hframe_2⟩
  · -- t0 ≠ allOnes ⇒ A's word has the NUL; bne t0,t2 TAKEN → 0xfac
    have hguard : ((strlenWordVal (cwordAt m0 (pa.toNat + 24*j))) != (BitVec.allOnes 64)) = true := by rw [bne_iff_ne]; exact hnul
    obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
      site_80006ed0_taken c.σ c.tick c.steps (0x80006ed0#64) vmi
        (strlenWordVal (cwordAt m0 (pa.toNat + 24*j))) (BitVec.allOnes 64)
        hgood hpc hmi ht0 ht2 hloaded rfl hguard htick
    have hpceq : (0x80006ed0#64 : BitVec 64) + sign_extend (m := 64) (0x00dc#13) = (0x80006fac#64 : BitVec 64) := by
      apply BitVec.eq_of_toNat_eq; decide
    have hpc1 : σ1.regs.get? Register.PC = some (0x80006fac#64 : BitVec 64) := by
      rw [obs_btaken_pc hobs1, hpceq]
    have hmem1eq : σ1.mem = c.σ.mem := hmem1
    -- A's word has the NUL ⇒ la < 24j + 8
    have hhasnul : csa.length < 24*j + 8 := by
      rcases Nat.lt_or_ge csa.length (24*j + 8) with hlt | hge
      · exact hlt
      · exact absurd (word_nul_free m0 pa csa hcstra (24*j) hge) hnul
    refine ⟨⟨σ1, i1, c.steps + 1⟩, Steps.single hs1, Or.inl ?_⟩
    exact ⟨hpc1, hhasnul, hjle, by rw [hmem1eq]; exact hmem, hG1, hi1⟩

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
