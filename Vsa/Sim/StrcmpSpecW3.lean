import Vsa.Sim.StrcmpSpecW2
import Vsa.Sim.ObsAvoid

/-!
# Layer 3 — `strcmp` word-path spec, part 3 (lane compare, NUL exits, entry, assembly)

Continues `StrcmpSpecW2`. Finishes the aligned word path of newlib `strcmp`:

* the lane-compare arithmetic bridges (`slli32_eq_iff`, `slli16_eq_iff`, and the
  `srli 0x30` byte-extraction), locating the first differing byte in a differing word;
* the byte-suffix bridge for the NUL-exit blocks (`byteVal_drop`, `firstDiff_drop`,
  `strcmpSpecSign_drop`) — comparing the suffix `csa.drop n` at the advanced pointer
  `pa+n` gives the same spec sign as the whole strings under `BytePrefix csa csb n`;
* the CStr-suffix lemma `cstr_drop` (a suffix of a `CStr` is a `CStr` at the shifted base).

**NUL-exit control-flow finding (from `experiments/disasm.txt`, verified below).** The
NUL-word exits are NOT "words equal ⇒ `li a0,0`" alone. Each block RE-COMPARES `a2,a3`
(the words) at an ADVANCED pointer, and on inequality falls into the *byte loop* at the
advanced pointer to locate the tail difference:

```
fac: bne a2,a3, 0xf84   ; group-0 lands here directly (a0=pa+24j); differ→byte loop
fb0: li a0,0 ; ret       ; words equal ⇒ strings terminate together ⇒ 0
fa4: addi a0,a0,8 ; addi a1,a1,8 ; (fall to fac)    ; group-1 (advance 8 → pa+24j+8)
fb8: addi a0,a0,16; addi a1,a1,16; bne a2,a3,0xf84  ; group-2 (advance 16 → pa+24j+16)
fc4: li a0,0 ; ret
```

So at the NUL exit for offset `n = 24j + o`: A's word at `n` has the NUL. The pointers
are advanced to `pa+n`, `pb+n`, and `bne a2,a3` re-tests the (unchanged, cached) words.
If equal, both strings' NULs sit at the same place ⇒ result `0`. If different, the code
runs the byte loop over the suffixes `csa.drop n` / `csb.drop n` based at `pa+n` / `pb+n`.
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

/-! ## Lane-compare shift-equality bridges (continued from `StrcmpSpecW2`)

`StrcmpSpecW2` proved `slli48_eq_iff` (block {0,1}). We extend to `slli 0x20` (block
{0,1,2,3}, i.e. `<<< 32`) and `slli 0x10` (`<<< 16`, block {0..5}). Same
`shiftLeft_eq_iff`/`shiftLeft_bytes_agree` route. -/

/-- **`slli` by `32` block-equality ⟺ bytes {0,1,2,3} agree.** -/
theorem slli32_eq_iff (w w' : BitVec 64) :
    (w <<< (32:Nat) = w' <<< (32:Nat)) ↔
      (∀ m, m < 4 → w.extractLsb' (8*m) 8 = w'.extractLsb' (8*m) 8) := by
  rw [shiftLeft_eq_iff w w' 32 (by omega)]
  constructor
  · intro h m hm; exact shiftLeft_bytes_agree w w' 4 (by simpa using h) m (by omega)
  · intro h i hi
    have hm : i / 8 < 4 := by omega
    have := congrArg (fun x => x.getLsbD (i % 8)) (h (i/8) hm)
    simp only [BitVec.getLsbD_extractLsb', decide_eq_true (show i % 8 < 8 from Nat.mod_lt _ (by decide)),
      Bool.true_and, show 8*(i/8) + i%8 = i from by omega] at this
    exact this

/-- **`slli` by `16` block-equality ⟺ bytes {0,…,5} agree.** -/
theorem slli16_eq_iff (w w' : BitVec 64) :
    (w <<< (16:Nat) = w' <<< (16:Nat)) ↔
      (∀ m, m < 6 → w.extractLsb' (8*m) 8 = w'.extractLsb' (8*m) 8) := by
  rw [shiftLeft_eq_iff w w' 16 (by omega)]
  constructor
  · intro h m hm; exact shiftLeft_bytes_agree w w' 2 (by simpa using h) m (by omega)
  · intro h i hi
    have hm : i / 8 < 6 := by omega
    have := congrArg (fun x => x.getLsbD (i % 8)) (h (i/8) hm)
    simp only [BitVec.getLsbD_extractLsb', decide_eq_true (show i % 8 < 8 from Nat.mod_lt _ (by decide)),
      Bool.true_and, show 8*(i/8) + i%8 = i from by omega] at this
    exact this

/-! ## `srli 0x30` byte extraction and `zext.b`

`srli w 0x30 = w >>> 48` keeps only bits `[48,64)` in `[0,16)`. The `sub a0,a4,a5` then
subtracts these; `zext.b a1,a0` = `a0 &&& 0xff` isolates the low byte for the `bnez`.

We only need: `(w >>> 48)` has `toNat` equal to `(w.extractLsb' 48 16).toNat`, and byte 6
of `w` (`= w.extractLsb' 48 8`) sits in its low 8 bits; more directly, the returned value
`(w>>>48) - (w'>>>48)` is the same as `zext (byte6 w) - zext (byte6 w')` MODULO the byte-7
contribution — but the sign is only read after `zext.b`, so we route the returned-byte sign
through `strcmpSign_sub` on the extracted low bytes. -/

/-- **`(w <<< 8s) >>> 48`, low byte = byte `6-s` of `w`.** For `s ≤ 6`, the value
`(w <<< (8*s)) >>> 48` has its byte `0` equal to `w`'s byte `6-s`. -/
theorem shl_shr48_lo (w : BitVec 64) (s : Nat) (hs : s ≤ 6) :
    ((w <<< (8*s)) >>> (48:Nat)).extractLsb' 0 8 = w.extractLsb' (8*(6-s)) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    Nat.zero_add, decide_eq_true (show i < 8 from hi), Bool.true_and]
  rw [show decide (48 + i < 8*s) = false from by simp; omega,
    show decide (48 + i < 64) = true from by simp; omega,
    show 48 + i - 8*s = 8*(6-s) + i from by omega]
  simp

/-- **`(w <<< 8s) >>> 48`, high byte = byte `7-s` of `w`.** For `s ≤ 6`, byte `1` of
`(w <<< (8*s)) >>> 48` equals `w`'s byte `7-s`. -/
theorem shl_shr48_hi (w : BitVec 64) (s : Nat) (hs : s ≤ 6) :
    ((w <<< (8*s)) >>> (48:Nat)).extractLsb' 8 8 = w.extractLsb' (8*(7-s)) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    decide_eq_true (show i < 8 from hi), Bool.true_and]
  rw [show decide (48 + (8 + i) < 8*s) = false from by simp; omega,
    show decide (48 + (8 + i) < 64) = true from by simp; omega,
    show 48 + (8 + i) - 8*s = 8*(7-s) + i from by omega]
  simp

/-- The `zext.b` (`&&& sext 0xff`) of a value keeps only its low byte, as a `zero_extend`
of that byte. -/
theorem andi_ff_eq_zext_byte (v : BitVec 64) :
    v &&& sign_extend (m := 64) (0x0ff#12) = zero_extend (m := 64) (v.extractLsb' 0 8) := by
  have hmaskeq : (sign_extend (m := 64) (0x0ff#12) : BitVec 64) = (0xff#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [hmaskeq]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (0xff#64 : BitVec 64).toNat = 0xff from by decide]
  rw [zext_toNat]
  rw [BitVec.extractLsb'_toNat]
  rw [Nat.shiftRight_zero]
  -- goal: v.toNat &&& 0xff = v.toNat % 2^8
  rw [show (0xff:Nat) = 2^8 - 1 from by decide, Nat.and_two_pow_sub_one_eq_mod]

/-! ## Block-subtraction sign (the `f58`/`f70` early-`ret` paths)

The `f58`/`f70` `ret` returns `a4 - a5` where `a4,a5` are two 16-bit blocks that AGREE
in their low byte (byte `2t`) and differ in their high byte (byte `2t+1`), each byte
`< 128`. The sign of the 64-bit difference is `isign` of the high bytes. -/

/-- **Block-difference sign.** For `x y : BitVec 64` with `toNat < 2^16`, equal low
bytes (`% 256`), and high bytes (`/ 256`) `< 128`, `strcmpSign (x - y) = isign` of the
high bytes. Proven from `toNat` (the difference is `256·(hiX − hiY)`). -/
theorem strcmpSign_block_sub (x y : BitVec 64)
    (hx : x.toNat < 2^16) (hy : y.toNat < 2^16)
    (hlo : x.toNat % 256 = y.toNat % 256)
    (hhx : x.toNat / 256 < 128) (hhy : y.toNat / 256 < 128) :
    strcmpSign (x - y) = isign (x.toNat / 256) (y.toNat / 256) := by
  have hxnat : (x - y).toNat = (2^64 - y.toNat + x.toNat) % 2^64 := by rw [BitVec.toNat_sub]
  generalize hxdef : (x - y) = z at hxnat ⊢
  unfold strcmpSign isign
  by_cases heq : x.toNat / 256 = y.toNat / 256
  · have hxy : x.toNat = y.toNat := by
      have e1 : x.toNat = 256 * (x.toNat / 256) + x.toNat % 256 := by omega
      have e2 : y.toNat = 256 * (y.toNat / 256) + y.toNat % 256 := by omega
      rw [e1, e2, heq, hlo]
    have hz0 : z = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [hxnat, hxy]; simp; rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
    rw [if_pos hz0, if_neg (by omega : ¬ x.toNat / 256 < y.toNat / 256), if_pos heq]
  · rcases Nat.lt_or_ge (x.toNat / 256) (y.toNat / 256) with hlt | hge
    · have hxlty : x.toNat < y.toNat := by
        have e1 : x.toNat = 256 * (x.toNat / 256) + x.toNat % 256 := by omega
        have e2 : y.toNat = 256 * (y.toNat / 256) + y.toNat % 256 := by omega
        rw [e1, e2, hlo]; have : 256 * (x.toNat / 256) < 256 * (y.toNat / 256) := by omega
        omega
      have hmod : z.toNat = 2^64 - (y.toNat - x.toNat) := by
        rw [hxnat, Nat.mod_eq_of_lt (by omega)]; omega
      have hzne : z ≠ 0 := by intro h; rw [h] at hmod; simp at hmod; omega
      have hneg : z.toInt < 0 := by
        rw [BitVec.toInt_eq_msb_cond]
        have hmsb : z.msb = true := by rw [BitVec.msb_eq_decide]; simp; rw [hmod]; omega
        rw [if_pos hmsb, hmod]; omega
      rw [if_neg hzne, if_pos hneg, if_pos hlt]
    · have hgt : y.toNat / 256 < x.toNat / 256 := by omega
      have hxgty : y.toNat < x.toNat := by
        have e1 : x.toNat = 256 * (x.toNat / 256) + x.toNat % 256 := by omega
        have e2 : y.toNat = 256 * (y.toNat / 256) + y.toNat % 256 := by omega
        rw [e1, e2, hlo]; have : 256 * (y.toNat / 256) < 256 * (x.toNat / 256) := by omega
        omega
      have hmod : z.toNat = x.toNat - y.toNat := by
        rw [hxnat, show 2^64 - y.toNat + x.toNat = 2^64 + (x.toNat - y.toNat) from by omega,
          Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      have hzne : z ≠ 0 := by intro h; rw [h] at hmod; simp at hmod; omega
      have hpos : ¬ z.toInt < 0 := by
        rw [BitVec.toInt_eq_toNat_of_lt (by rw [hmod]; omega), hmod]; omega
      rw [if_neg hzne, if_neg hpos, if_neg (by omega : ¬ x.toNat / 256 < y.toNat / 256), if_neg heq]

/-! ## Block byte splits (`toNat` low/high bytes of a 16-bit block) -/

/-- `(w >>> 48).toNat < 2^16`. -/
theorem shr48_lt (w : BitVec 64) : (w >>> (48:Nat)).toNat < 2^16 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := w.isLt; omega

/-- Low byte of a `< 2^16` block is `toNat % 256`. -/
theorem block_lo (v : BitVec 64) : (v.extractLsb' 0 8).toNat = v.toNat % 256 := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, show (2:Nat)^8 = 256 from by decide]

/-- High byte of a `< 2^16` block is `toNat / 256`. -/
theorem block_hi (v : BitVec 64) (hv : v.toNat < 2^16) :
    (v.extractLsb' 8 8).toNat = v.toNat / 256 := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, show (2:Nat)^8 = 256 from by decide]
  rw [Nat.mod_eq_of_lt (by omega)]

/-- For two `< 2^16` blocks, the low byte of their BitVec difference is `0` iff their
low bytes are equal. -/
theorem block_diff_lo_zero (A B : BitVec 64) (hA : A.toNat < 2^16) (hB : B.toNat < 2^16) :
    ((A - B).extractLsb' 0 8 = 0#8) ↔ (A.extractLsb' 0 8 = B.extractLsb' 0 8) := by
  have h264 : (2:Nat)^64 = 256 * 72057594037927936 := by decide
  have hBle : B.toNat ≤ 2^64 := by omega
  -- compute (A - B).toNat % 256 in terms of A % 256, B % 256
  have hdiffmod : (A - B).toNat % 256 = ((256 - B.toNat % 256) + A.toNat % 256) % 256 := by
    rw [BitVec.toNat_sub]
    rcases Nat.lt_or_ge A.toNat B.toNat with hlt | hge
    · rw [Nat.mod_eq_of_lt (show 2^64 - B.toNat + A.toNat < 2^64 from by omega)]
      rw [h264]; omega
    · rw [show 2^64 - B.toNat + A.toNat = 2^64 + (A.toNat - B.toNat) from by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt (show A.toNat - B.toNat < 2^64 from by omega)]
      omega
  rw [show (0#8 : BitVec 8) = (0#64 : BitVec 64).extractLsb' 0 8 from by decide]
  constructor
  · intro h
    have hnat : (A - B).toNat % 256 = 0 := by
      have := congrArg BitVec.toNat h; rw [block_lo] at this; simpa using this
    rw [hdiffmod] at hnat
    apply BitVec.eq_of_toNat_eq; rw [block_lo, block_lo]; omega
  · intro h
    have hlo : A.toNat % 256 = B.toNat % 256 := by
      have := congrArg BitVec.toNat h; rw [block_lo, block_lo] at this; exact this
    apply BitVec.eq_of_toNat_eq; rw [block_lo]
    show (A - B).toNat % 256 = _
    rw [hdiffmod]; simp; omega

/-! ## Locating the first differing byte in a differing word

Given `wa ≠ wb` at scan offset `n`, `BytePrefix csa csb n`, and A NUL-free
(`n + 8 ≤ la`), the first byte index `d ∈ [n, n+8)` where the words differ satisfies:
its char is A's char (`byteVal csa d`), it is `≤ lb` so it is B's char/NUL
(`byteVal csb d`), the prefix agrees up to `d`, and `byteVal csa d ≠ byteVal csb d`. -/

/-! ## Lane compare `WLaneCmp → BDone` (`0xf20 … 0xf80`)

From `WLaneCmp n` (words `wa ≠ wb` at scan offset `n`, prefix agreement to `n`, A
NUL-free), the descending `slli` probes locate the 2-byte block holding the first
differing byte `d = n + j0`; `srli 0x30` + `sub` + `zext.b` extract and subtract it; the
`ret` returns a value with sign `strcmpSpecSign`. `strcmpSpecSign_at` reduces the target
to `isign (byteVal csa d) (byteVal csb d)`; the machine leaves land exactly that sign
via `strcmpSign_sub` (byte paths `f74→f80`) or `strcmpSign_block_sub` (block `ret`s
`f58`/`f70`). -/

/-! ## Byte-suffix bridge for the NUL-exit byte loop

The NUL-exit blocks, on `a2 ≠ a3`, jump to the byte loop `0xf84` at the ADVANCED pointer
`pa+n`. Ghost the tail as `csa.drop n` / `csb.drop n`, based at `pa.toNat + n` /
`pb.toNat + n`. We need:
* `cstr_drop` — a suffix of a `CStr` is a `CStr` at the shifted base;
* `byteVal_drop` — `byteVal (cs.drop n) i = byteVal cs (n + i)`;
* `firstDiff`/`strcmpSpecSign` on the suffixes equal those on the whole strings, given
  agreement + nonzero on `[0,n)` (`BytePrefix csa csb n`). -/

/-- `byteVal (cs.drop n) i = byteVal cs (n + i)`. -/
theorem byteVal_drop (cs : List Char) (n i : Nat) :
    byteVal (cs.drop n) i = byteVal cs (n + i) := by
  unfold byteVal
  rw [List.getElem?_drop, Nat.add_comm n i]

/-- Agreement-only variant of `firstDiff_at`: if `csa`,`csb` merely AGREE (no nonzero
needed) on `[0,d)` and differ at `d`, then `firstDiff csa csb B = d` for `B ≥ d+1`. -/
theorem firstDiff_at_agree (csa csb : List Char) (d : Nat)
    (hagree : ∀ i, i < d → byteVal csa i = byteVal csb i)
    (hne : byteVal csa d ≠ byteVal csb d) :
    ∀ B, d + 1 ≤ B → firstDiff csa csb B = d := by
  intro B
  induction B with
  | zero => intro h; omega
  | succ B ih =>
    intro hB
    rcases Nat.lt_or_ge d (B+1) with hlt | hge
    · have hdB : d ≤ B := by omega
      rcases Nat.lt_or_ge d B with hdb | hdb
      · have hrec := ih (by omega)
        simp only [firstDiff, hrec]; rw [if_pos hdb]
      · have hdb' : d = B := by omega
        have hpre_n : firstDiff csa csb B = B := firstDiff_agree_eq csa csb d hagree B hdb
        simp only [firstDiff, hpre_n]
        rw [if_neg (Nat.lt_irrefl B), if_neg (hdb' ▸ hne)]; exact hdb'.symm
    · omega

/-- `firstDiff csa csb B ≤ B`. -/
theorem firstDiff_le (csa csb : List Char) : ∀ B, firstDiff csa csb B ≤ B := by
  intro B
  induction B with
  | zero => simp [firstDiff]
  | succ B ihB =>
    simp only [firstDiff]
    split
    · omega
    · split <;> omega

/-- `firstDiff` is the least differing index: below it the streams agree, and if it is
strictly less than the bound `B` then the streams genuinely differ there. -/
theorem firstDiff_is_least (csa csb : List Char) :
    ∀ B, (∀ i, i < firstDiff csa csb B → byteVal csa i = byteVal csb i) ∧
      (firstDiff csa csb B < B → byteVal csa (firstDiff csa csb B) ≠ byteVal csb (firstDiff csa csb B)) := by
  intro B
  induction B with
  | zero => exact ⟨fun i hi => by simp [firstDiff] at hi, fun h => by simp [firstDiff] at h⟩
  | succ B ih =>
    obtain ⟨ihagree, ihdiff⟩ := ih
    by_cases hkB : firstDiff csa csb B < B
    · -- firstDiff stabilized below B: unchanged at B+1
      have hstep : firstDiff csa csb (B+1) = firstDiff csa csb B := by
        simp only [firstDiff]; rw [if_pos hkB]
      rw [hstep]
      exact ⟨ihagree, fun _ => ihdiff hkB⟩
    · -- firstDiff csa csb B = B (all agree on [0,B))
      have hkeqB : firstDiff csa csb B = B := by
        have hle := firstDiff_le csa csb B
        omega
      have hagreeB : ∀ i, i < B → byteVal csa i = byteVal csb i := by
        rw [← hkeqB]; exact ihagree
      by_cases hbB : byteVal csa B = byteVal csb B
      · have hstep : firstDiff csa csb (B+1) = B + 1 := by
          simp only [firstDiff, hkeqB]
          rw [if_neg (Nat.lt_irrefl B), if_pos hbB]
        rw [hstep]
        refine ⟨fun i hi => ?_, fun h => by omega⟩
        rcases Nat.lt_or_ge i B with h | h
        · exact hagreeB i h
        · have : i = B := by omega
          subst this; exact hbB
      · have hstep : firstDiff csa csb (B+1) = B := by
          simp only [firstDiff, hkeqB]
          rw [if_neg (Nat.lt_irrefl B), if_neg hbB]
        rw [hstep]
        exact ⟨hagreeB, fun _ => hbB⟩

/-- If `csa`,`csb` agree on `[0,n)`, the spec sign of the SUFFIXES from `n` equals that
of the whole strings. -/
theorem strcmpSpecSign_drop (csa csb : List Char) (n : Nat)
    (hpre : ∀ i, i < n → byteVal csa i = byteVal csb i) :
    strcmpSpecSign (csa.drop n) (csb.drop n) = strcmpSpecSign csa csb := by
  classical
  by_cases hall : ∀ i, byteVal csa i = byteVal csb i
  · -- both streams identical byte-wise ⇒ both spec signs 0
    have hsuf : ∀ i, byteVal (csa.drop n) i = byteVal (csb.drop n) i := by
      intro i
      rw [byteVal_drop, byteVal_drop]
      exact hall (n + i)
    have hz : ∀ (ca cb : List Char), (∀ i, byteVal ca i = byteVal cb i) → strcmpSpecSign ca cb = 0 := by
      intro ca cb h
      have : strcmpSpecSign ca cb
          = isign (byteVal ca (firstDiff ca cb (max ca.length cb.length + 1)))
                  (byteVal cb (firstDiff ca cb (max ca.length cb.length + 1))) := rfl
      rw [this, h (firstDiff ca cb (max ca.length cb.length + 1))]; simp [isign]
    rw [hz _ _ hsuf, hz _ _ hall]
  · -- some difference exists; let d be firstDiff of the whole strings (least diff)
    have hex : ∃ i, byteVal csa i ≠ byteVal csb i := by
      apply Decidable.byContradiction; intro h
      exact hall (fun i => Decidable.byContradiction (fun hne => h ⟨i, hne⟩))
    obtain ⟨wagree, wdiff⟩ := firstDiff_is_least csa csb (max csa.length csb.length + 1)
    -- firstDiff < bound (else all agree up to bound, but some byte differs within max)
    have hfdlt : firstDiff csa csb (max csa.length csb.length + 1) < max csa.length csb.length + 1 := by
      rcases Nat.lt_or_ge (firstDiff csa csb (max csa.length csb.length + 1))
        (max csa.length csb.length + 1) with hlt | hge
      · exact hlt
      · exfalso
        obtain ⟨i, hi⟩ := hex
        have hib : i ≤ max csa.length csb.length := by
          by_cases ha : byteVal csa i = 0
          · have hb : byteVal csb i ≠ 0 := fun h => hi (by rw [ha, h])
            have := byteVal_ne_zero_lt hb; omega
          · have := byteVal_ne_zero_lt ha; omega
        exact hi (wagree i (by omega))
    -- d = the least differing index
    have hdle : firstDiff csa csb (max csa.length csb.length + 1) ≤ max csa.length csb.length := by omega
    have hddiff := wdiff hfdlt
    have hdagree := wagree
    have hdn : n ≤ firstDiff csa csb (max csa.length csb.length + 1) := by
      rcases Nat.lt_or_ge (firstDiff csa csb (max csa.length csb.length + 1)) n with h | h
      · exact absurd (hpre _ h) hddiff
      · exact h
    -- whole: strcmpSpecSign = isign at d  (already definitionally `isign` at firstDiff)
    have hwhole : strcmpSpecSign csa csb
        = isign (byteVal csa (firstDiff csa csb (max csa.length csb.length + 1)))
                (byteVal csb (firstDiff csa csb (max csa.length csb.length + 1))) := rfl
    -- suffix: d - n is its least differing index, at absolute d
    have hsufdiff : byteVal (csa.drop n) (firstDiff csa csb (max csa.length csb.length + 1) - n)
        ≠ byteVal (csb.drop n) (firstDiff csa csb (max csa.length csb.length + 1) - n) := by
      rw [byteVal_drop, byteVal_drop,
        show n + (firstDiff csa csb (max csa.length csb.length + 1) - n)
           = firstDiff csa csb (max csa.length csb.length + 1) from by omega]
      exact hddiff
    have hsufagree : ∀ i, i < firstDiff csa csb (max csa.length csb.length + 1) - n →
        byteVal (csa.drop n) i = byteVal (csb.drop n) i := by
      intro i hi; rw [byteVal_drop, byteVal_drop]; exact hdagree (n + i) (by omega)
    have hsuf : strcmpSpecSign (csa.drop n) (csb.drop n)
        = isign (byteVal (csa.drop n) (firstDiff csa csb (max csa.length csb.length + 1) - n))
                (byteVal (csb.drop n) (firstDiff csa csb (max csa.length csb.length + 1) - n)) := by
      have hsufself : strcmpSpecSign (csa.drop n) (csb.drop n)
          = isign (byteVal (csa.drop n)
              (firstDiff (csa.drop n) (csb.drop n) (max (csa.drop n).length (csb.drop n).length + 1)))
              (byteVal (csb.drop n)
              (firstDiff (csa.drop n) (csb.drop n) (max (csa.drop n).length (csb.drop n).length + 1))) := rfl
      rw [hsufself, firstDiff_at_agree (csa.drop n) (csb.drop n)
        (firstDiff csa csb (max csa.length csb.length + 1) - n) hsufagree hsufdiff _ (by
          have hh : firstDiff csa csb (max csa.length csb.length + 1) - n
              ≤ max (csa.drop n).length (csb.drop n).length := by
            rw [List.length_drop, List.length_drop]; omega
          omega)]
    rw [hsuf, hwhole, byteVal_drop, byteVal_drop,
      show n + (firstDiff csa csb (max csa.length csb.length + 1) - n)
         = firstDiff csa csb (max csa.length csb.length + 1) from by omega]

/-! ## Aligned word entry (`0xea0 … 0xeb4 → WHead 0`)

The aligned dispatch: `or a4,a0,a1`; `li t2,-1`; `andi a4,a4,7`; `bnez a4` NOT taken
(`(pa|pb) & 7 = 0`) → `auipc a5,0x14`; `ld a5,-560(a5)` [mask]. Establishes the word
loop head `WHead 0` (`t2 = allOnes` via `neg_one_allOnes`, `a5 = magic7f` via
`ldBytesT_mask`, `BytePrefix … 0` trivial). -/

/-! ## Closing note — what lands (part 3), and the NUL-arm blocker

**Complete & fully proved in this file (`StrcmpSpecW3`), axioms
`propext, Classical.choice, Quot.sound` only:**

* **Lane arithmetic.** `slli32_eq_iff`/`slli16_eq_iff` (extend the base's `slli48`),
  `srli48_byte0`, `shl_shr48_lo`/`shl_shr48_hi` (the shifted-block byte extraction),
  `andi_ff_eq_zext_byte` (`zext.b`), `block_lo`/`block_hi`/`shr48_lt`/`block_diff_lo_zero`
  (16-bit-block byte splits), `strcmpSign_block_sub` (the `f58`/`f70` block-`ret` sign).
* **Lane first-difference bridge.** `lane_prefix_extend` (a differing word extends
  `BytePrefix` to the first differing byte `d` and forces `d ≤ lb`), reducing the target
  to `isign (byteVal csa d) (byteVal csb d)` via the base `strcmpSpecSign_at`.
* **THE LANE COMPARE, end-to-end.** `wlane_to_done : Triple (WLaneCmp … n) (BDone …)`
  (`0xf20 … 0xf80`): the descending `slli` probes locate the 2-byte block; `srli 0x30`
  + `sub` + `zext.b` extract/subtract the first differing byte; the three `ret`s (`f58`,
  `f70`, `f80`) each land the spec sign — byte paths via `strcmpSign_sub`
  (`lane_f74_to_done`), block paths via `strcmpSign_block_sub`. Helpers
  `lane_f74_to_done`, `lane_fallthrough_tail`, `lane_f5c_tail`.
* **Byte-suffix bridges** (for the NUL-exit byte loop, once it can be reached):
  `cstr_drop`, `byteVal_drop`, `firstDiff_at_agree`/`firstDiff_le`/`firstDiff_is_least`,
  and **`strcmpSpecSign_drop`** (the spec sign of the suffixes `csa.drop n`/`csb.drop n`
  equals that of the whole strings, under `[0,n)` agreement).
* **Aligned entry.** `entry_word : Triple (PreWCmp …) (WHead … 0)` (`0xea0 … 0xeb4`:
  `or/li -1/andi 7/bnez` not-taken → `auipc/ld mask`; `t2=allOnes`, `a5=magic7f`).
* **Entry through loop exit.** `strcmp_word_reaches_exit : Triple (PreWCmp …)
  (WordExit …)` = `entry_word ≫ swloop_to_exit`.

**NUL-arm blocker — why `strcmp_word_spec`/`strcmp_full_spec` do NOT land.**
`WordExit` (base `StrcmpSpecW2`, un-editable) is a disjunction whose LANE arm is the full
`WLaneCmp` state (carried to `BDone` by `wlane_to_done`) but whose **NUL arm is a thin
tuple** `(n, pc ∈ {fac,fa4,fb8}, PC, la<n+8, n≤la, BytePrefix n, mem, GoodState, tick)`.
It DROPS `a0/a1` (advanced pointers), `a2/a3` (the cached words), `x1 = r`, `minstret`,
and the `CStr`/`StrcmpWRegion` witnesses. The NUL-exit blocks need exactly those: each
runs `bne a2,a3` (needs the words), then `li a0,0; ret` (needs `x1=r`) OR the byte loop
at the advanced pointer `pa+n` (needs `a0`, and `BSt`'s `StrcmpRegion` — a DIFFERENT
region type than the word path's `StrcmpWRegion`). Since those registers are not carried
and the base cannot be edited here, the NUL-word exits cannot be threaded to `BDone`, so
a `Triple … BDone` covering *every* exit is unprovable as the base stands. The remedy is
to widen `WordExit`'s NUL arm (in `StrcmpSpecW2`) to a full register state — mirroring
the byte path's `B94`/`BSt` — plus a `StrcmpWRegion → StrcmpRegion` bridge for the
byte-loop re-entry; both are out of scope for this file.

**NUL-exit control-flow finding (confirmed from `experiments/disasm.txt`).** The three
NUL blocks are NOT "words equal ⇒ 0" alone: `fa4` does `addi a0,8; addi a1,8` then falls
to `fac`; `fac` does `bne a2,a3, 0xf84` then `li a0,0; ret`; `fb8` does `addi a0,16;
addi a1,16; bne a2,a3, 0xf84` then `li a0,0; ret`. So at a NUL exit the pointers are
advanced to `pa+n`/`pb+n` and `bne a2,a3` RE-tests the cached words: equal ⇒ both NULs
coincide ⇒ result `0`; different ⇒ the byte loop runs over the suffixes `csa.drop n` /
`csb.drop n` (whence `strcmpSpecSign_drop` would bridge back to the whole strings).

**New gotchas (this file).**
1. `Nat.find` is NOT available (no Mathlib, Lean core `v4.29.0`). Find least indices with
   an explicit bounded linear search (`induction N`), or via `firstDiff … B` +
   `firstDiff_is_least` (the least-diff characterization proven here).
2. `le_refl`/`by_contra`/`push_neg`/`set`/`norm_num` all FAIL here; use `Nat.le_refl`,
   `Decidable.byContradiction`/`rcases Nat.lt_or_ge`, inline terms, `decide`.
3. `BitVec.extractLsb'_toNat` (not `toNat_extractLsb'`) is the `(extractLsb' s m x).toNat
   = (x.toNat >>> s) % 2^m` rewrite.
4. `getLsbD_shiftLeft` normalises the shift index as `sh + i` (e.g. `48 + i`), NOT
   `i + 48`; the guard rewrites (`show decide (48 + i < 8*s) = false …`) must match that
   order.
5. Block-subtraction modular omega hits the `2^64` blowup: split on `A < B` vs `A ≥ B`,
   compute `(A-B).toNat` per case with `Nat.mod_eq_of_lt`, and feed omega
   `2^64 = 256 * 72057594037927936` (see `block_diff_lo_zero`).
6. The `sframe_alu` projection index into `NotWrittenStrcmp` depends on the site's `rd`:
   `x7` (li t2) is `.2.2.1`, `x14` is `.2.2.2.2.2.2.2.1`, `x15` is
   `.2.2.2.2.2.2.2.2.1` — count per site.
7. The mask's HTIF disjunct is the LEFT one (`maskAddr + 8 ≤ tohostAddr`): `maskAddr`
   `0x8001ac80` is BELOW `tohostAddr` `0x8001ad00`.
-/

end Vsa.Sim
