import Vsa.Sim.MemcpySites2
import Vsa.Sim.MemcpySpec
import Vsa.Triple

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

/-- The 8-byte word at `src + 8j` under `MemInv … (8j)` reads `bs 8j … bs 8j+7`. -/
theorem word_src_bytes (dst src : BitVec 64) (n : Nat) (bs : Nat → BitVec 8) (j : Nat)
    (m0 mem : Std.ExtHashMap Nat (BitVec 8))
    (hj : 8 * j + 8 ≤ n)
    (hsrc : (src + BitVec.ofNat 64 (8 * j)).toNat = src.toNat + 8 * j)
    (hinv : MemInv dst src n bs (8 * j) m0 mem) :
    mem[(src + BitVec.ofNat 64 (8 * j)).toNat]? = some (bs (8*j)) ∧
    mem[(src + BitVec.ofNat 64 (8 * j)).toNat + 1]? = some (bs (8*j+1)) ∧
    mem[(src + BitVec.ofNat 64 (8 * j)).toNat + 2]? = some (bs (8*j+2)) ∧
    mem[(src + BitVec.ofNat 64 (8 * j)).toNat + 3]? = some (bs (8*j+3)) ∧
    mem[(src + BitVec.ofNat 64 (8 * j)).toNat + 4]? = some (bs (8*j+4)) ∧
    mem[(src + BitVec.ofNat 64 (8 * j)).toNat + 5]? = some (bs (8*j+5)) ∧
    mem[(src + BitVec.ofNat 64 (8 * j)).toNat + 6]? = some (bs (8*j+6)) ∧
    mem[(src + BitVec.ofNat 64 (8 * j)).toNat + 7]? = some (bs (8*j+7)) := by
  rw [hsrc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (first
      | (have := hinv.src_intact (8*j) (Nat.le_refl _) (by omega); simpa using this)
      | (rw [show src.toNat + 8*j + 1 = src.toNat + (8*j+1) from by omega]
         exact hinv.src_intact (8*j+1) (by omega) (by omega))
      | (rw [show src.toNat + 8*j + 2 = src.toNat + (8*j+2) from by omega]
         exact hinv.src_intact (8*j+2) (by omega) (by omega))
      | (rw [show src.toNat + 8*j + 3 = src.toNat + (8*j+3) from by omega]
         exact hinv.src_intact (8*j+3) (by omega) (by omega))
      | (rw [show src.toNat + 8*j + 4 = src.toNat + (8*j+4) from by omega]
         exact hinv.src_intact (8*j+4) (by omega) (by omega))
      | (rw [show src.toNat + 8*j + 5 = src.toNat + (8*j+5) from by omega]
         exact hinv.src_intact (8*j+5) (by omega) (by omega))
      | (rw [show src.toNat + 8*j + 6 = src.toNat + (8*j+6) from by omega]
         exact hinv.src_intact (8*j+6) (by omega) (by omega))
      | (rw [show src.toNat + 8*j + 7 = src.toNat + (8*j+7) from by omega]
         exact hinv.src_intact (8*j+7) (by omega) (by omega)))

/-! ## `sdData8` of a `sign_extend`-of-`ldData8` word is the plain `ldData8` value

`sdData8 vdata = extractLsb vdata 63 0` is width-preserving on a `BitVec 64`, and
`sign_extend (m := 64)` on a `BitVec 64` argument is the identity. So the stored
byte chain is exactly the loaded little-endian assembly. -/

/-- `sdData8 x` is the identity on a `BitVec 64` (`extractLsb … 63 0`). -/
theorem sdData8_self (x : BitVec 64) : sdData8 x = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [sdData8, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb']
  have key : ∀ W : Nat, W = 64 → (BitVec.ofNat W (x.toNat >>> 0)).toNat = x.toNat := by
    intro W hW; subst hW
    simp only [Nat.shiftRight_zero, BitVec.toNat_ofNat]
    have : x.toNat < 2 ^ 64 := x.isLt; omega
  exact key ((8 *i 8 -i 1).toNat - 0 + 1) (by decide)

/-- `sdData8 (sign_extend (ldData8 …))` equals the plain `ldData8` value (as
`BitVec (8*8)`).  `sign_extend (m := 64)` is identity on a `BitVec 64`; `sdData8`
(`extractLsb … 63 0`) is identity too. -/
theorem sdData8_ldData8 (c0 c1 c2 c3 c4 c5 c6 c7 : BitVec 8) :
    sdData8 (sign_extend (m := 64) (ldData8 c0 c1 c2 c3 c4 c5 c6 c7))
      = ldData8 c0 c1 c2 c3 c4 c5 c6 c7 := by
  rw [show (sign_extend (m := 64) (ldData8 c0 c1 c2 c3 c4 c5 c6 c7) : BitVec 64)
        = ldData8 c0 c1 c2 c3 c4 c5 c6 c7 from by
      simp only [sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq]]
  exact sdData8_self _

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

/-- Read the word-store chain outside its 8-byte footprint. -/
theorem sdMem8_outside (m : Std.ExtHashMap Nat (BitVec 8)) (a : BitVec 64) (word : BitVec 64)
    (q : Nat) (hq : q < a.toNat ∨ a.toNat + 8 ≤ q) :
    (sdMem8 m a word)[q]? = m[q]? := by
  simp only [sdMem8]
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
    Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
    Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
    Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
    Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
    Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
    Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
    Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]

/-- Read the word-store chain at offset `k < 8`: recovers slice `k` of the word. -/
theorem sdMem8_at (m : Std.ExtHashMap Nat (BitVec 8)) (a : BitVec 64) (word : BitVec 64)
    (k : Nat) (hk : k < 8) :
    (sdMem8 m a word)[a.toNat + k]? = some ((sdData8 word).extractLsb' (8 * k) 8) := by
  simp only [sdMem8]
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp only [Std.ExtHashMap.getElem?_insert, beq_iff_eq, Nat.add_zero,
      Nat.add_right_cancel_iff, Nat.add_eq_left, Nat.reduceEqDiff, if_true, if_false,
      Nat.reduceMul, Nat.succ_ne_zero]

/-! ## Word-granularity invariant step (`meminv_store8`)

From `MemInv … (8j) mem` at a word-aligned byte-iteration `8j < n` with a full
remaining word (`8j + 8 ≤ n`), storing the loaded word
`word = sign_extend (ldData8 (bs 8j) … (bs 8j+7))` at `dst + 8j` re-establishes
`MemInv … (8j + 8)` for the map `sdMem8 mem (dst + ofNat 8j) word`.

The stored bytes come from `src_intact` (the loaded word IS `bs 8j … bs 8j+7`), and
the eight slices recover them via `extractLsb'_ldData8`. All key disequalities are
`omega`-shaped from `Regions` + word alignment. -/
theorem meminv_store8 (dst src : BitVec 64) (n : Nat) (bs : Nat → BitVec 8) (j : Nat)
    (m0 mem : Std.ExtHashMap Nat (BitVec 8))
    (hreg : Regions dst src n) (hj : 8 * j + 8 ≤ n)
    (haddr : (dst + BitVec.ofNat 64 (8 * j)).toNat = dst.toNat + 8 * j)
    (hinv : MemInv dst src n bs (8 * j) m0 mem) :
    MemInv dst src n bs (8 * j + 8) m0
      (sdMem8 mem (dst + BitVec.ofNat 64 (8 * j))
        (sign_extend (m := 64)
          (ldData8 (bs (8*j)) (bs (8*j+1)) (bs (8*j+2)) (bs (8*j+3))
                   (bs (8*j+4)) (bs (8*j+5)) (bs (8*j+6)) (bs (8*j+7))))) := by
  -- the stored word and its 8-byte footprint address
  have hword_def : (dst + BitVec.ofNat 64 (8 * j)).toNat = dst.toNat + 8 * j := haddr
  -- each slice of the word is the corresponding source byte
  have hslice : ∀ k, k < 8 →
      (sdData8 (sign_extend (m := 64)
        (ldData8 (bs (8*j)) (bs (8*j+1)) (bs (8*j+2)) (bs (8*j+3))
                 (bs (8*j+4)) (bs (8*j+5)) (bs (8*j+6)) (bs (8*j+7))))).extractLsb' (8 * k) 8
        = bs (8 * j + k) := by
    intro k hk
    rw [sdData8_ldData8]
    apply extractLsb'_ldData8 _ _ _ _ _ _ _ _ k hk
    match k, hk with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.add_zero]
  refine ⟨?_, ?_, ?_⟩
  · -- copied for k < 8j+8
    intro k hk
    by_cases hlt : k < 8 * j
    · -- old prefix, outside the new 8-byte footprint
      rw [sdMem8_outside mem _ _ (dst.toNat + k) (by rw [hword_def]; omega)]
      exact hinv.copied k hlt
    · -- new bytes at offset k - 8j ∈ [0,8)
      have hge : 8 * j ≤ k := by omega
      have hk8 : k - 8 * j < 8 := by omega
      have hkeq : dst.toNat + k = (dst + BitVec.ofNat 64 (8 * j)).toNat + (k - 8 * j) := by
        rw [hword_def]; omega
      rw [hkeq, sdMem8_at mem _ _ (k - 8 * j) hk8, hslice (k - 8 * j) hk8]
      congr 1
      rw [Nat.add_sub_cancel' hge]
  · -- outside [dst, dst+n): untouched (the 8-byte footprint is inside)
    intro q hq
    rw [sdMem8_outside mem _ _ q (by rw [hword_def]; have := hreg.dst_nowrap; omega)]
    exact hinv.outside q hq
  · -- source region [src + (8j+8), src+n) still reads bs (disjoint from the dst footprint)
    intro k hik hkn
    rw [sdMem8_outside mem _ _ (src.toNat + k) (by
      rw [hword_def]; rcases hreg.disjoint with hd | hd <;> omega)]
    exact hinv.src_intact k (by omega) hkn

/-! ## Pointer identities for the word loop

The word loop advances `a3`/`a5` by 8 each iteration. `ptr_word_succ` is the
`+8` increment as a `BitVec` add (`sign_extend 0x008 = 8`); `sdAddrM8_succ` is the
`sd …,-8(a5)` back-offset (`a5` pre-incremented to `dst + 8(j+1)`, the store lands
at `dst + 8j`). -/

/-- `base + ofNat (8j) + sign_extend 0x008 = base + ofNat (8(j+1))` (the `+8`). -/
theorem ptr_word_succ (base : BitVec 64) (j : Nat) :
    base + BitVec.ofNat 64 (8 * j) + sign_extend (m := 64) (0x008#12)
      = base + BitVec.ofNat 64 (8 * (j + 1)) := by
  apply BitVec.eq_of_toNat_eq
  rw [show (sign_extend (m := 64) (0x008#12) : BitVec 64) = 8#64 from by
    apply BitVec.eq_of_toNat_eq; decide]
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- `sdAddrM8 (base + ofNat (8(j+1))) = base + ofNat (8j)`: the `-8` store back-offset
undoes the pre-increment (`+ sext 0xff8 = -8`). -/
theorem sdAddrM8_word_succ (base : BitVec 64) (j : Nat) :
    sdAddrM8 (base + BitVec.ofNat 64 (8 * (j + 1))) = base + BitVec.ofNat 64 (8 * j) := by
  show (base + BitVec.ofNat 64 (8 * (j + 1))) + sign_extend (m := 64) (0xff8#12)
      = base + BitVec.ofNat 64 (8 * j)
  have hsext : (sign_extend (m := 64) (0xff8#12) : BitVec 64) = -(8#64) := by
    apply BitVec.eq_of_toNat_eq; decide
  have hofn : (BitVec.ofNat 64 (8 * (j + 1)) : BitVec 64)
      = BitVec.ofNat 64 (8 * j) + 8#64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have : ((8 : BitVec 64)).toNat = 8 := by decide
    omega
  rw [hsext, hofn]
  generalize BitVec.ofNat 64 (8 * j) = w
  rw [BitVec.add_assoc base (w + 8#64) (-(8#64)), BitVec.add_assoc w (8#64) (-(8#64)),
    show (8#64 + -(8#64) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide,
    BitVec.add_zero]

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

/-- `R` is outside the union of the word-path written GPRs (`x13, x15, x16`) and
every register any hot-path step (ALU / store / tick) can write. -/
abbrev NotWrittenW (R : Register) : Prop :=
  (Register.x13 == R) = false ∧ (Register.x15 == R) = false ∧
  (Register.x16 == R) = false ∧
  (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
  (Register.minstret == R) = false ∧ (Register.minstret_increment == R) = false ∧
  (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
  (Register.mip == R) = false

theorem NotWrittenW.x13 {R : Register} (h : NotWrittenW R) : (Register.x13 == R) = false := h.1
theorem NotWrittenW.x15 {R : Register} (h : NotWrittenW R) : (Register.x15 == R) = false := h.2.1
theorem NotWrittenW.x16 {R : Register} (h : NotWrittenW R) : (Register.x16 == R) = false := h.2.2.1

/-- Generic ALU frame step for the word path. -/
theorem frame_alu_w {σ' σ : MState} {pc vm : BitVec 64} {rd : Register} {v : RegisterType rd}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm rd v)) (R : Register)
    (hrd : (rd == R) = false) (hR : NotWrittenW R) :
    σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_alu σ pc vm rd v R hmi hpc hrd hnpc hmii

/-- Generic STORE frame step for the word path (write-set `PC, minstret, nextPC,
minstret_increment`; NO `rd`). -/
theorem frame_store_w {σ' σ : MState} {pc vm : BitVec 64} {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m')) (R : Register)
    (hR : NotWrittenW R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_store σ pc vm m' R hmi hpc hnpc hmii

/-! ## The word-loop head state and one-iteration Triple

`StW p j r dst src n m0 bs c` is the standing observation at the word-loop head
`0x80006c08`, word-iteration `j`, where `p` is the word count (`a2 = dst + 8p` is
the loop's end bound). It bundles `GoodState`, code loaded, PC at c08, the live
pointers (`a0 = dst`, `a1 = src`, `a2 = dst+8p`, `a3 = src+8j`, `a4 = dst`,
`a5 = dst+8j`, `a7 = dst+n`), `x1 = r`, `minstret` defined, `tick < 2`, the
`Regions` bounds, `8(j+1) ≤ n` (a full word remains and stays in-region), and
`MemInv … (8j)`. Base 8-alignment of `dst`/`src` is carried as fields so the
per-iteration store/load alignment side conditions discharge. -/
structure StW (g : (R : Register) → Option (RegisterType R)) (p j : Nat) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : MemcpyLoaded c.σ.mem
  pc : c.σ.regs.get? Register.PC = some (0x80006c08#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some dst
  a1 : c.σ.regs.get? Register.x11 = some src
  a2 : c.σ.regs.get? Register.x12 = some (dst + BitVec.ofNat 64 (8 * p))
  a3 : c.σ.regs.get? Register.x13 = some (src + BitVec.ofNat 64 (8 * j))
  a4 : c.σ.regs.get? Register.x14 = some dst
  a5 : c.σ.regs.get? Register.x15 = some (dst + BitVec.ofNat 64 (8 * j))
  a7 : c.σ.regs.get? Register.x17 = some (dst + BitVec.ofNat 64 n)
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : Regions dst src n
  dst_align : dst.toNat % 8 = 0
  src_align : src.toNat % 8 = 0
  jlt : 8 * j + 8 ≤ n
  meminv : MemInv dst src n bs (8 * j) m0 c.σ.mem
  hframe : ∀ R : Register, NotWrittenW R → c.σ.regs.get? R = g R

/-- The state at `0x80006c18` (post-body, pre-`bltu`) for word-iteration `j`:
pointers advanced by one word (`a3 = src+8(j+1)`, `a5 = dst+8(j+1)`), and
`MemInv … (8(j+1))`. -/
structure StW18 (g : (R : Register) → Option (RegisterType R)) (p j : Nat) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : MemcpyLoaded c.σ.mem
  pc : c.σ.regs.get? Register.PC = some (0x80006c18#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some dst
  a1 : c.σ.regs.get? Register.x11 = some src
  a2 : c.σ.regs.get? Register.x12 = some (dst + BitVec.ofNat 64 (8 * p))
  a3 : c.σ.regs.get? Register.x13 = some (src + BitVec.ofNat 64 (8 * (j + 1)))
  a4 : c.σ.regs.get? Register.x14 = some dst
  a5 : c.σ.regs.get? Register.x15 = some (dst + BitVec.ofNat 64 (8 * (j + 1)))
  a7 : c.σ.regs.get? Register.x17 = some (dst + BitVec.ofNat 64 n)
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : Regions dst src n
  dst_align : dst.toNat % 8 = 0
  src_align : src.toNat % 8 = 0
  jlt : 8 * j + 8 ≤ n
  meminv : MemInv dst src n bs (8 * (j + 1)) m0 c.σ.mem
  hframe : ∀ R : Register, NotWrittenW R → c.σ.regs.get? R = g R

/-! ### Per-iteration RAM/window bounds for the word pointers -/

/-- The word-store address bounds for `sd …,-8(a5)` with `a5 = dst + 8(j+1)`:
effective address `dst + 8j`, in RAM, above the HTIF window, 8-aligned. -/
theorem word_dst_ptr_bounds (dst src : BitVec 64) (n : Nat) (hreg : Regions dst src n)
    (j : Nat) (hj : 8 * j + 8 ≤ n) (hda : dst.toNat % 8 = 0) :
    (dst + BitVec.ofNat 64 (8 * (j + 1))).toNat = dst.toNat + 8 * (j + 1) ∧
    0x80000000 ≤ (sdAddrM8 (dst + BitVec.ofNat 64 (8 * (j + 1)))).toNat ∧
    (sdAddrM8 (dst + BitVec.ofNat 64 (8 * (j + 1)))).toNat + 8 ≤ 0x100000000 ∧
    tohostAddr + 16 ≤ (sdAddrM8 (dst + BitVec.ofNat 64 (8 * (j + 1)))).toNat ∧
    (sdAddrM8 (dst + BitVec.ofNat 64 (8 * (j + 1)))).toNat % 8 = 0 ∧
    (sdAddrM8 (dst + BitVec.ofNat 64 (8 * (j + 1)))).toNat = dst.toNat + 8 * j := by
  have htn : (dst + BitVec.ofNat 64 (8 * (j + 1))).toNat = dst.toNat + 8 * (j + 1) :=
    ptr_toNat dst (8 * (j + 1)) (by have := hreg.dst_nowrap; omega)
  have hsb : (sdAddrM8 (dst + BitVec.ofNat 64 (8 * (j + 1)))).toNat = dst.toNat + 8 * j := by
    rw [sdAddrM8_word_succ]; exact ptr_toNat dst (8 * j) (by have := hreg.dst_nowrap; omega)
  have hlo := hreg.dst_lo; have hhi := hreg.dst_hi; have hwin := hreg.dst_win
  have htoh : tohostAddr = 0x8001ad00 := rfl
  refine ⟨htn, ?_, ?_, ?_, ?_, hsb⟩
  · rw [hsb]; omega
  · rw [hsb]; omega
  · rw [hsb]; omega
  · rw [hsb]; omega

/-- The source-pointer per-iteration bounds (RAM, HTIF window, 8-aligned) for the
word `ld`. -/
theorem word_src_bounds (dst src : BitVec 64) (n : Nat) (hreg : Regions dst src n)
    (j : Nat) (hj : 8 * j + 8 ≤ n) (hsa : src.toNat % 8 = 0) :
    (src + BitVec.ofNat 64 (8 * j)).toNat = src.toNat + 8 * j ∧
    0x80000000 ≤ (src + BitVec.ofNat 64 (8 * j)).toNat ∧
    (src + BitVec.ofNat 64 (8 * j)).toNat + 8 ≤ 0x100000000 ∧
    ((src + BitVec.ofNat 64 (8 * j)).toNat + 8 ≤ tohostAddr ∨
       tohostAddr + 8 ≤ (src + BitVec.ofNat 64 (8 * j)).toNat) ∧
    (src + BitVec.ofNat 64 (8 * j)).toNat % 8 = 0 := by
  have htn : (src + BitVec.ofNat 64 (8 * j)).toNat = src.toNat + 8 * j :=
    ptr_toNat src (8 * j) (by have := hreg.src_nowrap; omega)
  have hlo := hreg.src_lo; have hhi := hreg.src_hi; have hwin := hreg.src_win
  have htoh : tohostAddr = 0x8001ad00 := rfl
  refine ⟨htn, ?_, ?_, ?_, ?_⟩
  · rw [htn]; omega
  · rw [htn]; omega
  · right; rw [htn]; omega
  · rw [htn]; omega

/-- The word value loaded/stored at word-iteration `j`: the little-endian assembly
of `bs 8j … bs 8j+7` (sign-extended, width-preserving at width 8). -/
abbrev wordAt (bs : Nat → BitVec 8) (j : Nat) : BitVec 64 :=
  sign_extend (m := 64)
    (ldData8 (bs (8*j)) (bs (8*j+1)) (bs (8*j+2)) (bs (8*j+3))
             (bs (8*j+4)) (bs (8*j+5)) (bs (8*j+6)) (bs (8*j+7)))

/-! ## One word-loop body iteration (`0x80006c08 → 0x80006c18`)

Chains `ld a6,0(a3) → addi a5,a5,8 → addi a3,a3,8 → sd a6,-8(a5)`. The `ld` reads
the 8-byte word `bs 8j … bs 8j+7` from `src+8j` (`word_src_bytes` via
`MemInv.src_intact`); the two `addi`s advance `a5`/`a3` by one word; the `sd`
writes that word back at `dst+8j` (`sdAddrM8_word_succ`), and `meminv_store8`
re-establishes `MemInv … (8(j+1))`. -/
theorem iterW (g : (R : Register) → Option (RegisterType R)) (p j : Nat) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) :
    Triple (StW g p j r dst src n m0 bs) (StW18 g p j r dst src n m0 bs) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hpc, ha0, ha1, ha2, ha3, ha4, ha5, ha7, hra, ⟨vmi, hmi⟩, htick,
    hreg, hda, hsa, hjlt, hminv, hframe⟩ := hSt
  obtain ⟨hsrc_tn, hslo, hshi, hshtif, hsalign⟩ := word_src_bounds dst src n hreg j hjlt hsa
  obtain ⟨hdst_tn, hdlo, hdhi, hdwin, hdalign, hsbeq⟩ := word_dst_ptr_bounds dst src n hreg j hjlt hda
  -- the loaded word bytes come from src_intact
  obtain ⟨hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7⟩ :=
    word_src_bytes dst src n bs j m0 c.σ.mem hjlt hsrc_tn hminv
  -- === c08: ld a6,0(a3) ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006c08 c.σ c.tick c.steps (0x80006c08#64) vmi (src + BitVec.ofNat 64 (8 * j))
      (bs (8*j)) (bs (8*j+1)) (bs (8*j+2)) (bs (8*j+3))
      (bs (8*j+4)) (bs (8*j+5)) (bs (8*j+6)) (bs (8*j+7))
      hgood hpc hmi ha3 hloaded rfl hslo hshi hshtif hsalign hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7 htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006c0c#64 : BitVec 64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x80006c08#64) 4 = (0x80006c0c#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_alu_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have ha1_1 := obs_alu_other hobs1 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1
  have ha2_1 := obs_alu_other hobs1 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha2
  have ha3_1 := obs_alu_other hobs1 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3
  have ha4_1 := obs_alu_other hobs1 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4
  have ha5_1 := obs_alu_other hobs1 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha5
  have ha7_1 := obs_alu_other hobs1 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha7
  have hra_1 := obs_alu_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  have ha6_1 : σ1.regs.get? Register.x16 = some (wordAt bs j) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide); exact this
  obtain ⟨vmi1, hmi1'⟩ := obs_alu_minstret hobs1
  -- === c0c: addi a5,a5,8 ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006c0c σ1 i1 (c.steps + 1) (0x80006c0c#64) vmi1 (dst + BitVec.ofNat 64 (8 * j))
      hG1 hpc1 hmi1' ha5_1 (by rw [hmem1]; exact hloaded) rfl hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006c10#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006c0c#64) 4 = (0x80006c10#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_1
  have ha1_2 := obs_alu_other hobs2 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_1
  have ha2_2 := obs_alu_other hobs2 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha2_1
  have ha3_2 := obs_alu_other hobs2 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3_1
  have ha4_2 := obs_alu_other hobs2 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_1
  have ha7_2 := obs_alu_other hobs2 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha7_1
  have hra_2 := obs_alu_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
  have ha6_2 := obs_alu_other hobs2 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha6_1
  have ha5_2 : σ2.regs.get? Register.x15 = some (dst + BitVec.ofNat 64 (8 * (j + 1))) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [ptr_word_succ dst j] at this
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  -- === c10: addi a3,a3,8 ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80006c10 σ2 i2 (c.steps + 1 + 1) (0x80006c10#64) vmi2 (src + BitVec.ofNat 64 (8 * j))
      hG2 hpc2 hmi2' ha3_2 (by rw [hmem2, hmem1]; exact hloaded) rfl hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x80006c14#64 : BitVec 64) := by
    have := obs_alu_pc hobs3; rwa [show BitVec.addInt (0x80006c10#64) 4 = (0x80006c14#64 : BitVec 64) from by decide] at this
  have ha0_3 := obs_alu_other hobs3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_2
  have ha1_3 := obs_alu_other hobs3 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_2
  have ha2_3 := obs_alu_other hobs3 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha2_2
  have ha4_3 := obs_alu_other hobs3 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_2
  have ha5_3 := obs_alu_other hobs3 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha5_2
  have ha7_3 := obs_alu_other hobs3 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha7_2
  have hra_3 := obs_alu_other hobs3 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_2
  have ha6_3 := obs_alu_other hobs3 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha6_2
  have ha3_3 : σ3.regs.get? Register.x13 = some (src + BitVec.ofNat 64 (8 * (j + 1))) := by
    have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [ptr_word_succ src j] at this
  obtain ⟨vmi3, hmi3'⟩ := obs_alu_minstret hobs3
  -- === c14: sd a6,-8(a5) ===  (a5 = dst+8(j+1), a6 = word)
  have hmem3eq : σ3.mem = c.σ.mem := by rw [hmem3, hmem2, hmem1]
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80006c14 σ3 i3 (c.steps + 1 + 1 + 1) (0x80006c14#64) vmi3
      (dst + BitVec.ofNat 64 (8 * (j + 1))) (wordAt bs j)
      hG3 hpc3 hmi3' ha5_3 ha6_3 (by rw [hmem3eq]; exact hloaded) rfl
      hdlo hdhi hdwin hdalign hi3
  -- the store's post map, in the form `meminv_store8` consumes
  have hstore_mem : σ4.mem
      = sdMem8 c.σ.mem (dst + BitVec.ofNat 64 (8 * j)) (wordAt bs j) := by
    rw [hmem4, mem_afterNextPC, hmem3eq, sdAddrM8_word_succ]
  have hsteps : Steps c ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ :=
    (((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans (Steps.single hs4)
  refine ⟨⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩, hsteps, ?_⟩
  · have hpc4 : σ4.regs.get? Register.PC = some (0x80006c18#64 : BitVec 64) := by
      have := obs_store_pc hobs4
      rwa [show BitVec.addInt (0x80006c14#64) 4 = (0x80006c18#64 : BitVec 64) from by decide] at this
    have ha0_4 := obs_store_other hobs4 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_3
    have ha1_4 := obs_store_other hobs4 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_3
    have ha2_4 := obs_store_other hobs4 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha2_3
    have ha3_4 := obs_store_other hobs4 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3_3
    have ha4_4 := obs_store_other hobs4 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_3
    have ha5_4 := obs_store_other hobs4 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha5_3
    have ha7_4 := obs_store_other hobs4 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha7_3
    have hra_4 := obs_store_other hobs4 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_3
    have hmi_4 := obs_store_minstret hobs4
    -- code stays loaded across the 8-byte insert chain (each key outside the code region)
    have hloaded4 : MemcpyLoaded σ4.mem := by
      rw [hstore_mem]
      -- unfold sdMem8 into 8 inserts and apply loaded_insert 8×; keys = dst+8j .. dst+8j+7
      have hbase : (dst + BitVec.ofNat 64 (8 * j)).toNat = dst.toNat + 8 * j :=
        ptr_toNat dst (8 * j) (by have := hreg.dst_nowrap; omega)
      have hcode := hreg.code_disjoint
      have hnw := hreg.dst_nowrap
      simp only [sdMem8]
      refine loaded_insert _ _ _ (by rw [hbase]; omega)
        (loaded_insert _ _ _ (by rw [hbase]; omega)
        (loaded_insert _ _ _ (by rw [hbase]; omega)
        (loaded_insert _ _ _ (by rw [hbase]; omega)
        (loaded_insert _ _ _ (by rw [hbase]; omega)
        (loaded_insert _ _ _ (by rw [hbase]; omega)
        (loaded_insert _ _ _ (by rw [hbase]; omega)
        (loaded_insert _ _ _ (by rw [hbase]; omega) hloaded)))))))
    refine ⟨hG4, hloaded4, hpc4, ha0_4, ha1_4, ha2_4, ha3_4, ha4_4, ha5_4, ha7_4, hra_4,
      hmi_4, hi4, hreg, hda, hsa, hjlt, ?_, ?_⟩
    · -- MemInv … (8(j+1)) via meminv_store8
      rw [hstore_mem]
      exact meminv_store8 dst src n bs j m0 c.σ.mem hreg hjlt
        (ptr_toNat dst (8 * j) (by have := hreg.dst_nowrap; omega)) hminv
    · -- frame: thread g through the 4 body steps (ld x16, addi x15, addi x13, sd)
      intro R hR
      have e1 : σ1.regs.get? R = c.σ.regs.get? R := frame_alu_w hobs1 R hR.x16 hR
      have e2 : σ2.regs.get? R = σ1.regs.get? R := frame_alu_w hobs2 R hR.x15 hR
      have e3 : σ3.regs.get? R = σ2.regs.get? R := frame_alu_w hobs3 R hR.x13 hR
      have e4 : σ4.regs.get? R = σ3.regs.get? R := frame_store_w hobs4 R hR
      rw [e4, e3, e2, e1]; exact hframe R hR

end Vsa.Sim
