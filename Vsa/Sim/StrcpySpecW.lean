import Vsa.Sim.StrcpySpec
import Vsa.Sim.MemcpySpec2
import Vsa.Sim.MemLoadTotal

/-!
# Layer 3 — `strcpy` aligned word-path spec (`strcpy_word_spec`)

The 8-aligned fast path of newlib `strcpy` (`0x80006dd0 … 0x80006e9c`): builds the
NUL-detection magic constant INLINE (no rodata load — unlike `strcmp`), runs an
8-byte word-copy loop (`sd` only NUL-free words), and finishes with an unrolled
≤7-byte byte tail plus a `sb zero,7(a2)` finisher.

This proves the aligned path in the SAME `Q` shape as `StrcpySpec.strcpy_bytehead_post`
(chars + NUL copied into `[dst, dst+len]`, everything else untouched), so the two
paths unify at the entry dispatch.

## Control flow (from `experiments/disasm.txt`)

```
dc4: or   a5,a0,a1          ; entry
dc8: andi a5,a5,7
dcc: bnez a5,80006e7c       ; misaligned → byte head (NOT this path)
dd0: lui  a5,0x7f7f8        ; a5 = sext 0x7f7f8000
dd4: addi a5,a5,-129        ; a5 = 0x7f7f7f7f   (the 32-bit magic half)
dd8: ld   a4,0(a1)          ; a4 = first source word
ddc: slli a3,a5,0x20        ; a3 = 0x7f7f7f7f00000000
de0: add  a3,a3,a5          ; a3 = 0x7f7f7f7f7f7f7f7f = magic7f
de4: and  a6,a4,a3
de8: add  a6,a6,a3
dec: or   a6,a6,a4
df0: or   a6,a6,a3          ; a6 = strlenWordVal a4
df4: li   a5,-1             ; a5 = allOnes
df8: mv   a2,a0            ; a2 = dst
dfc: bne  a6,a5,80006e24    ; a4 has a NUL byte → byte tail (BEFORE the store)
e00: addi a1,a1,8
e04: sd   a4,0(a2)          ; store the NUL-free word
e08: ld   a4,0(a1)          ; next source word
e0c: addi a2,a2,8
e10..e1c: a5 = strlenWordVal a4  (recompute magic on new word)
e20: beq  a5,a6,80006e00    ; NUL-free (a5 = allOnes = a6) → loop back
                            ; else fall to byte tail 0xe24
e24..e78: unrolled ≤7-byte lbu/sb/beqz byte tail; bnez a4,0xe98; ret
e98: sb zero,7(a2)          ; NUL finisher (writes the NUL at offset 7 of last word)
e9c: ret
```

## TRUE aligned-path dst footprint

The aligned path writes **exactly `len + 1` bytes** `[dst, dst+len]` — the `len`
characters and the terminating NUL, IDENTICAL to the byte-head path. Details:

* The word loop `sd`s only NUL-free words: after `j` completed word iterations,
  `[dst, dst+8j)` holds the first `8j` source bytes and `8j ≤ len` (the word at
  `[src+8j, src+8j+8)` is the one holding the NUL, i.e. `8j ≤ len < 8j+8`).
* The byte tail copies bytes `8j, 8j+1, …` up to and INCLUDING the NUL at `len`.
  Let `t = len - 8j ∈ [0,7]`. For `t ∈ {0,…,6}` the NUL byte is written by one of
  the `sb`s and the following `beqz`/`bnez` falls to `ret`. For `t = 7`, bytes
  `8j…8j+6` (all nonzero) are stored, then `bnez a4` (b6 ≠ 0) is TAKEN to the
  finisher `0xe98: sb zero,7(a2)` which writes the NUL at `dst+8j+7 = dst+len`.
* So the `sb zero,7(a2)` finisher writes **the NUL itself** (`dst+len`), NOT extra
  zero-padding.  The footprint is exactly `[dst, dst+len]` in every case.

## Ghost parameters

Same as the byte-head path: `dst` (x10), `src` (x11), `s : String`
(`CString m0 src s`), `r` (x1, 4-aligned), `m0`, `bs : Nat → BitVec 8` with
`bs k = char k` for `k < len`, `bs len = 0`.  The aligned path additionally requires
`(dst ||| src) % 8 = 0` (both 8-aligned — the real interpreter call sites malloc
16-aligned `dst`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.MemRepr (CStr CString Mem)
open Vsa.Sim.Code (StrcpyLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## 1. The inline magic-constant construction

`lui a5,0x7f7f8` writes `a5 = sext(0x7f7f8 +++ 0x000) = sext 0x7f7f8000`.
`addi a5,a5,-129` (imm `0xf7f`, `sext = -129`) gives `a5 = 0x7f7f7f7f`.
`slli a3,a5,0x20` gives `a3 = 0x7f7f7f7f00000000`.
`add a3,a3,a5` gives `a3 = 0x7f7f7f7f7f7f7f7f = magic7f`.

All pure `BitVec` `decide` facts. -/

/-- `lui`-value: `sext(0x7f7f8 +++ 0x000)` as a concrete 64-bit constant. -/
theorem magicCpw_lui :
    (sign_extend (m := 64) ((0x7f7f8#20) +++ 0x000#12) : BitVec 64) = 0x7f7f8000#64 := by
  apply BitVec.eq_of_toNat_eq; decide

/-- After `addi …,-129`: `0x7f7f8000 + sext 0xf7f = 0x7f7f7f7f` (the 32-bit magic half). -/
theorem magicCpw_addi :
    ((0x7f7f8000#64 : BitVec 64) + sign_extend (m := 64) (0xf7f#12)) = 0x7f7f7f7f#64 := by
  apply BitVec.eq_of_toNat_eq; decide

/-- After `slli …,0x20`: `shift_bits_left 0x7f7f7f7f (0x20 & 0x3f) = 0x7f7f7f7f00000000`. -/
theorem magicCpw_slli :
    shift_bits_left (0x7f7f7f7f#64 : BitVec 64) (Sail.BitVec.extractLsb (0x20#6) 5 0)
      = 0x7f7f7f7f00000000#64 := by
  apply BitVec.eq_of_toNat_eq; decide

/-- After `add a3,a3,a5`: `0x7f7f7f7f00000000 + 0x7f7f7f7f = magic7f`. -/
theorem magicCpw_add :
    ((0x7f7f7f7f00000000#64 : BitVec 64) + (0x7f7f7f7f#64 : BitVec 64)) = magic7f := by
  apply BitVec.eq_of_toNat_eq; decide

/-- The magic-ALU chain `((w &&& magic7f) + magic7f ||| w) ||| magic7f = strlenWordVal w`
(the four ops `and/add/or/or` in the strcpy word block; `strlenWordVal` is
`(((w&&&m)+m) ||| w) ||| m`). -/
theorem strcpyWordVal_eq (w : BitVec 64) :
    (((w &&& magic7f) + magic7f ||| w) ||| magic7f) = strlenWordVal w := rfl

/-! ## 2. `StrBytesW`: source-word/byte ghost for the aligned path

Reuses the byte-head `StrBytes` shape but the aligned path additionally reads whole
8-byte words that may extend up to 7 bytes past the NUL (into unmapped memory).  The
`ld` is the TOTAL load (`ldBytesT`, `getD 0`), so trailing unmapped bytes read `0`.
We only ever CARE about bytes `≤ len` (chars + NUL); `bs k` for `k > len` is
irrelevant.  We reuse `StrBytes` verbatim. -/

/-- The 8-aligned ghost word of `m0` at byte-address `a`, reusing `strlenWordAt`. -/
abbrev cwordAtW (m0 : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) : BitVec 64 :=
  strlenWordAt m0 a

/-- Byte `k < 8` of `cwordAtW m0 a` is the memory byte at `a + k` (little-endian). -/
theorem cwordAtW_byte (m0 : Std.ExtHashMap Nat (BitVec 8)) (a k : Nat) (hk : k < 8) :
    (cwordAtW m0 a).extractLsb' (8*k) 8 = (m0[a + k]?).getD 0 := by
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

/-! ### Magic detection ↔ word NUL-free, specialised to the aligned source.

`StrBytes m0 src len bs` gives, for `k < len`, byte `bs k ≠ 0` at `src+k`, and byte
`0` at `src+len`.  The word covering `[8j, 8j+8)`:
* is NUL-free (all 8 bytes nonzero) iff `8j + 8 ≤ len`;
* contains the NUL iff `8j ≤ len < 8j + 8`.

The magic result `strlenWordVal (word) = allOnes` iff NUL-free (via `detect_all_ones`). -/

/-- Word at `src+8j` is NUL-free ⇒ `strlenWordVal = allOnes`, when `8j + 8 ≤ len`. -/
theorem wordW_nul_free (m0 : Std.ExtHashMap Nat (BitVec 8)) (src : BitVec 64) (len : Nat)
    (bs : Nat → BitVec 8) (hsb : StrBytes m0 src len bs) (j : Nat) (hle : 8*j + 8 ≤ len) :
    strlenWordVal (cwordAtW m0 (src.toNat + 8*j)) = BitVec.allOnes 64 := by
  rw [detect_all_ones]
  intro k hk
  rw [cwordAtW_byte m0 _ k hk]
  have hlt : 8*j + k < len := by omega
  obtain ⟨hb, hbne⟩ := hsb.chars (8*j + k) hlt
  rw [show src.toNat + 8*j + k = src.toNat + (8*j + k) from by omega, hb]
  simpa using hbne

/-- Word at `src+8j` contains the NUL ⇒ `strlenWordVal ≠ allOnes`, when `8j ≤ len < 8j+8`. -/
theorem wordW_has_nul (m0 : Std.ExtHashMap Nat (BitVec 8)) (src : BitVec 64) (len : Nat)
    (bs : Nat → BitVec 8) (hsb : StrBytes m0 src len bs) (j : Nat)
    (hlo : 8*j ≤ len) (hhi : len < 8*j + 8) :
    strlenWordVal (cwordAtW m0 (src.toNat + 8*j)) ≠ BitVec.allOnes 64 := by
  intro hall
  rw [detect_all_ones] at hall
  have hk : len - 8*j < 8 := by omega
  have := hall (len - 8*j) hk
  rw [cwordAtW_byte m0 _ _ hk] at this
  apply this
  have hnul : m0[src.toNat + len]? = some (bs len) := hsb.nul
  rw [show src.toNat + 8*j + (len - 8*j) = src.toNat + len from by omega, hnul, hsb.bs_nul]
  rfl

/-! ## 3. Region bundle and ghost frame for the aligned path

`CpwRegions dst src len` bundles the disjointness / no-wrap facts.  Like the
byte-head `CpyRegions` but the word loop reads/writes whole 8-byte words that may
extend up to 7 bytes past `dst+len` / `src+len` (the NUL word), so we require
`+8` headroom above the RAM/HTIF/wrap bounds and `8`-alignment of both pointers. -/
structure CpwRegions (dst src : BitVec 64) (len : Nat) : Prop where
  dst_nowrap : dst.toNat + len + 8 < 2^64
  src_nowrap : src.toNat + len + 8 < 2^64
  disjoint : dst.toNat + len + 8 ≤ src.toNat ∨ src.toNat + len + 8 ≤ dst.toNat
  code_disjoint : dst.toNat + len + 8 ≤ 0x80006dc4 ∨ 0x80006ea0 ≤ dst.toNat
  dst_lo : 0x80000000 ≤ dst.toNat
  dst_hi : dst.toNat + len + 8 ≤ 0x100000000
  src_lo : 0x80000000 ≤ src.toNat
  src_hi : src.toNat + len + 8 ≤ 0x100000000
  dst_win : tohostAddr + 16 ≤ dst.toNat
  src_win : tohostAddr + 16 ≤ src.toNat
  dst_align : dst.toNat % 8 = 0
  src_align : src.toNat % 8 = 0

/-- The aligned path writes GPRs `{x11,x12,x13,x14,x15,x16}`; `x10` (`a0=dst`) and
`x1` (`ra`) are preserved. -/
abbrev NotWrittenCpw (R : Register) : Prop :=
  (Register.x11 == R) = false ∧ (Register.x12 == R) = false ∧
  (Register.x13 == R) = false ∧ (Register.x14 == R) = false ∧
  (Register.x15 == R) = false ∧ (Register.x16 == R) = false ∧
  (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
  (Register.minstret == R) = false ∧ (Register.minstret_increment == R) = false ∧
  (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
  (Register.mip == R) = false

theorem NotWrittenCpw.x11 {R : Register} (h : NotWrittenCpw R) : (Register.x11 == R) = false := h.1
theorem NotWrittenCpw.x12 {R : Register} (h : NotWrittenCpw R) : (Register.x12 == R) = false := h.2.1
theorem NotWrittenCpw.x13 {R : Register} (h : NotWrittenCpw R) : (Register.x13 == R) = false := h.2.2.1
theorem NotWrittenCpw.x14 {R : Register} (h : NotWrittenCpw R) : (Register.x14 == R) = false := h.2.2.2.1
theorem NotWrittenCpw.x15 {R : Register} (h : NotWrittenCpw R) : (Register.x15 == R) = false := h.2.2.2.2.1
theorem NotWrittenCpw.x16 {R : Register} (h : NotWrittenCpw R) : (Register.x16 == R) = false := h.2.2.2.2.2.1

theorem frame_alu_cpw {σ' σ : MState} {pc vm : BitVec 64} {rd : Register} {v : RegisterType rd}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm rd v)) (R : Register)
    (hrd : (rd == R) = false) (hR : NotWrittenCpw R) :
    σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_alu σ pc vm rd v R hmi hpc hrd hnpc hmii

theorem frame_store_cpw {σ' σ : MState} {pc vm : BitVec 64} {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m')) (R : Register)
    (hR : NotWrittenCpw R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_store σ pc vm m' R hmi hpc hnpc hmii

theorem frame_btaken_cpw {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 13}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_taken σ pc vm imm)) (R : Register)
    (hR : NotWrittenCpw R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_branch_taken σ pc vm imm R hmi hpc hnpc hmii

theorem frame_bnottaken_cpw {σ' σ : MState} {pc vm : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm)) (R : Register)
    (hR : NotWrittenCpw R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_branch_nottaken σ pc vm R hmi hpc hnpc hmii

theorem frame_jr_cpw {σ' σ : MState} {pc vm tgt : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vm tgt)) (R : Register)
    (hR : NotWrittenCpw R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_jump_x0 σ pc vm tgt R hmi hpc hnpc hmii

/-! ## 4. The copied-prefix invariant (reusing `MemcpySpec.MemInv`)

The aligned word loop copies the source into `[dst, …)` exactly like `memcpy`, so we
reuse `MemInv dst src (len+1) bs i` — the copied-prefix / outside-untouched /
source-intact description, over the length `len+1` (chars + NUL region).  Note the
"copied region" is `[dst, dst+len]` (`len+1` bytes) so the invariant length is `len+1`. -/

/-- Build a `memcpy`-style `Regions dst src (len+1)` from `CpwRegions` (`meminv_store8`
consumes `dst_nowrap` and `disjoint` from it; the code-region field is memcpy's, but
`meminv_store8` never reads it, so we satisfy it vacuously with the left disjunct
available from the `+8` headroom — actually we prove it honestly from RAM bounds). -/
theorem cpw_regions (dst src : BitVec 64) (len : Nat) (hreg : CpwRegions dst src len) :
    Regions dst src (len + 1) := by
  have hdw := hreg.dst_win
  have hsw := hreg.src_win
  have htoh : tohostAddr = 0x8001ad00 := rfl
  refine ⟨?_, ?_, ?_, ?_, hreg.dst_lo, ?_, hreg.src_lo, ?_, hreg.dst_win, hreg.src_win⟩
  · have := hreg.dst_nowrap; omega
  · have := hreg.src_nowrap; omega
  · rcases hreg.disjoint with h | h
    · left; omega
    · right; omega
  · -- code_disjoint is about memcpy `[0x80006bc8, 0x80006cf0)`; dst is above 0x80006ea0
    right; rw [htoh] at hdw; omega
  · have := hreg.dst_hi; omega
  · have := hreg.src_hi; omega

/-- The word store at `dst+8j` (`8j+8 ≤ len+1`) extends the copied prefix by 8, from
`MemInv … (8j)` to `MemInv … (8j+8)`, via `meminv_store8`.  The stored word is the
ghost word `ldData8 (bs 8j) … (bs 8j+7)`. -/
theorem cpw_store8 (dst src : BitVec 64) (len : Nat) (bs : Nat → BitVec 8) (j : Nat)
    (m0 mem : Std.ExtHashMap Nat (BitVec 8))
    (hreg : CpwRegions dst src len) (hj : 8 * j + 8 ≤ len + 1)
    (haddr : (dst + BitVec.ofNat 64 (8 * j)).toNat = dst.toNat + 8 * j)
    (hinv : MemInv dst src (len + 1) bs (8 * j) m0 mem) :
    MemInv dst src (len + 1) bs (8 * j + 8) m0
      (sdMem8 mem (dst + BitVec.ofNat 64 (8 * j))
        (sign_extend (m := 64)
          (ldData8 (bs (8*j)) (bs (8*j+1)) (bs (8*j+2)) (bs (8*j+3))
                   (bs (8*j+4)) (bs (8*j+5)) (bs (8*j+6)) (bs (8*j+7))))) :=
  meminv_store8 dst src (len + 1) bs j m0 mem (cpw_regions dst src len hreg) hj haddr hinv

/-- `strlenWordAt m0 a = ldData8` of its eight `getD 0` bytes (same little-endian
`append` nesting). -/
theorem strlenWordAt_ldData8 (m0 : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) :
    strlenWordAt m0 a =
      ldData8 ((m0[a]?).getD 0) ((m0[a+1]?).getD 0) ((m0[a+2]?).getD 0) ((m0[a+3]?).getD 0)
              ((m0[a+4]?).getD 0) ((m0[a+5]?).getD 0) ((m0[a+6]?).getD 0) ((m0[a+7]?).getD 0) := by
  simp only [strlenWordAt, ldData8]

/-- **Loaded NUL-free word = the ghost `ldData8` word.**  When the word `[src+8j, +8)`
is NUL-free (`8j + 8 ≤ len`), `ldBytesT σ (src+8j)` (with `σ.mem = m0`) equals the
ghost `ldData8 (bs 8j) … (bs 8j+7)`.  Each memory byte is the (nonzero) char `bs`. -/
theorem loadedWord_eq_ghost (m0 : Std.ExtHashMap Nat (BitVec 8)) (src : BitVec 64) (len : Nat)
    (bs : Nat → BitVec 8) (hsb : StrBytes m0 src len bs) (j : Nat) (hle : 8*j + 8 ≤ len) :
    strlenWordAt m0 (src.toNat + 8*j) =
      ldData8 (bs (8*j)) (bs (8*j+1)) (bs (8*j+2)) (bs (8*j+3))
              (bs (8*j+4)) (bs (8*j+5)) (bs (8*j+6)) (bs (8*j+7)) := by
  rw [strlenWordAt_ldData8]
  have hb : ∀ k, k < 8 → (m0[src.toNat + 8*j + k]?).getD 0 = bs (8*j + k) := by
    intro k hk
    obtain ⟨hbk, _⟩ := hsb.chars (8*j + k) (by omega)
    rw [show src.toNat + 8*j + k = src.toNat + (8*j + k) from by omega, hbk]; rfl
  have h0 := hb 0 (by omega); have h1 := hb 1 (by omega); have h2 := hb 2 (by omega)
  have h3 := hb 3 (by omega); have h4 := hb 4 (by omega); have h5 := hb 5 (by omega)
  have h6 := hb 6 (by omega); have h7 := hb 7 (by omega)
  simp only [Nat.add_zero] at h0
  rw [h0, h1, h2, h3, h4, h5, h6, h7]

/-- The strcpy `sd` site's post-map `sdMemCpy` is the memcpy `sdMem8` chain (same
`extractLsb vdata 63 0` slices, same 8 inserts). -/
theorem sdMemCpy_eq_sdMem8 (m : Std.ExtHashMap Nat (BitVec 8)) (a vdata : BitVec 64) :
    sdMemCpy m a vdata = sdMem8 m a vdata := rfl

/-! ## 5. The word-loop head state `WHeadCpw` (at `0xe00`, top of the store loop)

The word loop's actual back-edge is `beq a5,a6,0x80006e00` — it re-enters at `0xe00`,
NOT the entry `bne a6,a5` at `0xdfc`.  `a6` holds `allOnes` throughout the loop (the
OLD magic, never recomputed); each iteration recomputes `a5 = strlenWordVal (new word)`
and `beq a5,a6` loops back iff the new word is also NUL-free.

At `0xe00`, word iteration `j`: the CURRENT word `a4 = cwordAtW m0 (src+8j)` is already
known NUL-free (`8j + 8 ≤ len`) — it is about to be stored 8-wide.  Ghosts as before.
`a1 = src+8j`, `a2 = dst+8j`, `a3 = magic7f`, `a6 = allOnes`.  Copied-prefix
`MemInv … (8j)`.  Since the current word is NUL-free, `8j + 8 ≤ len`. -/
structure WHeadCpw (g : (R : Register) → Option (RegisterType R))
    (r dst src : BitVec 64) (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (bs : Nat → BitVec 8) (j : Nat) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrcpyLoaded c.σ.mem
  mem : c.σ.mem = m0
  pc : c.σ.regs.get? Register.PC = some (0x80006e00#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some dst
  a1 : c.σ.regs.get? Register.x11 = some (src + BitVec.ofNat 64 (8*j))
  a2 : c.σ.regs.get? Register.x12 = some (dst + BitVec.ofNat 64 (8*j))
  a3 : c.σ.regs.get? Register.x13 = some magic7f
  a4 : c.σ.regs.get? Register.x14 = some (cwordAtW m0 (src.toNat + 8*j))
  a6 : c.σ.regs.get? Register.x16 = some (BitVec.allOnes 64)
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : CpwRegions dst src len
  strbytes : StrBytes m0 src len bs
  nulfree : 8*j + 8 ≤ len
  meminv : MemInv dst src (len + 1) bs (8*j) m0 c.σ.mem
  hframe : ∀ R : Register, NotWrittenCpw R → c.σ.regs.get? R = g R

/-! `li a5,-1` builds `(0#64) + sext 0xfff = allOnes 64`. -/
theorem liCpw_allOnes : ((0#64 : BitVec 64) + sign_extend (m := 64) (0xfff#12)) = BitVec.allOnes 64 := by
  apply BitVec.eq_of_toNat_eq; decide

/-- `x + sext 0x000 = x`. -/
theorem addCpw_sext0 (x : BitVec 64) : x + sign_extend (m := 64) (0x000#12) = x := by
  rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by
    apply BitVec.eq_of_toNat_eq; decide]
  exact BitVec.add_zero x

/-- `x + sext 0x008 = x + 8` at the pointer level: `src+8j + 8 = src+8(j+1)`. -/
theorem ptrCpw_word_succ (base : BitVec 64) (j : Nat) :
    base + BitVec.ofNat 64 (8 * j) + sign_extend (m := 64) (0x008#12)
      = base + BitVec.ofNat 64 (8 * (j + 1)) :=
  ptr_word_succ base j

/-- `(base + ofNat (8j)).toNat = base.toNat + 8j` (no wrap). -/
theorem ptrCpw_toNat (base : BitVec 64) (j : Nat) (h : base.toNat + 8*j < 2^64) :
    (base + BitVec.ofNat 64 (8*j)).toNat = base.toNat + 8*j := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-! ### The mid-loop state `WStoreMid` (at `0xe20`, the `beq a5,a6` test)

After the straight-line store body `0xe00→0xe20`: the current word has been stored
(`MemInv … (8(j+1))`), `a1 = src+8(j+1)`, `a2 = dst+8(j+1)`, the NEXT word is loaded
`a4 = cwordAtW m0 (src+8(j+1))`, its magic `a5 = strlenWordVal a4`, and `a6 = allOnes`
is unchanged.  `beq a5,a6` then dispatches on whether the next word is NUL-free. -/
structure WStoreMid (g : (R : Register) → Option (RegisterType R))
    (r dst src : BitVec 64) (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (bs : Nat → BitVec 8) (j : Nat) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrcpyLoaded c.σ.mem
  mem : c.σ.mem = m0
  pc : c.σ.regs.get? Register.PC = some (0x80006e20#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some dst
  a1 : c.σ.regs.get? Register.x11 = some (src + BitVec.ofNat 64 (8*(j+1)))
  a2 : c.σ.regs.get? Register.x12 = some (dst + BitVec.ofNat 64 (8*(j+1)))
  a3 : c.σ.regs.get? Register.x13 = some magic7f
  a4 : c.σ.regs.get? Register.x14 = some (cwordAtW m0 (src.toNat + 8*(j+1)))
  a5 : c.σ.regs.get? Register.x15 = some (strlenWordVal (cwordAtW m0 (src.toNat + 8*(j+1))))
  a6 : c.σ.regs.get? Register.x16 = some (BitVec.allOnes 64)
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : CpwRegions dst src len
  strbytes : StrBytes m0 src len bs
  jle : 8*(j+1) ≤ len
  meminv : MemInv dst src (len + 1) bs (8*(j+1)) m0 c.σ.mem
  hframe : ∀ R : Register, NotWrittenCpw R → c.σ.regs.get? R = g R

/-- The word store at `dst+8j` does not disturb the ghost word at `src+8(j+1)`
(disjoint regions), so `cwordAtW` there reads the same value.  Used to identify the
NEXT loaded word after the store. -/
theorem cwordAtW_store_disjoint (dst src : BitVec 64) (len : Nat) (j : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (word : BitVec 64)
    (hreg : CpwRegions dst src len) (hj : 8*(j+1) ≤ len)
    (hdaddr : (dst + BitVec.ofNat 64 (8*j)).toNat = dst.toNat + 8*j) :
    cwordAtW (sdMem8 m0 (dst + BitVec.ofNat 64 (8*j)) word) (src.toNat + 8*(j+1))
      = cwordAtW m0 (src.toNat + 8*(j+1)) := by
  show strlenWordAt (sdMem8 m0 (dst + BitVec.ofNat 64 (8*j)) word) (src.toNat + 8*(j+1))
    = strlenWordAt m0 (src.toNat + 8*(j+1))
  have hkey : ∀ q, src.toNat + 8*(j+1) ≤ q → q < src.toNat + 8*(j+1) + 8 →
      (sdMem8 m0 (dst + BitVec.ofNat 64 (8*j)) word)[q]? = m0[q]? := by
    intro q hlo hhi
    apply sdMem8_outside
    rw [hdaddr]
    rcases hreg.disjoint with hd | hd
    · first | (left; omega) | (right; omega)
    · first | (left; omega) | (right; omega)
  simp only [strlenWordAt]
  rw [hkey (src.toNat + 8*(j+1)) (by omega) (by omega),
      hkey (src.toNat + 8*(j+1) + 1) (by omega) (by omega),
      hkey (src.toNat + 8*(j+1) + 2) (by omega) (by omega),
      hkey (src.toNat + 8*(j+1) + 3) (by omega) (by omega),
      hkey (src.toNat + 8*(j+1) + 4) (by omega) (by omega),
      hkey (src.toNat + 8*(j+1) + 5) (by omega) (by omega),
      hkey (src.toNat + 8*(j+1) + 6) (by omega) (by omega),
      hkey (src.toNat + 8*(j+1) + 7) (by omega) (by omega)]

end Vsa.Sim
