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

/-- `(w >>> 48).extractLsb' 0 8 = w.extractLsb' 48 8` (byte 6 of `w`). -/
theorem srli48_byte0 (w : BitVec 64) :
    (w >>> (48:Nat)).extractLsb' 0 8 = w.extractLsb' (48) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, Nat.zero_add,
    decide_eq_true (show i < 8 from hi), Bool.true_and]

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

/-- The two words agreeing on bytes `[n, d)` extends the `BytePrefix` to `d`, and forces
`d ≤ lb`. Here `d` is any index in `[n, n+8]` with A-word/B-word byte agreement on
`[n, d)`. -/
theorem lane_prefix_extend (m0 : Std.ExtHashMap Nat (BitVec 8)) (pa pb : BitVec 64)
    (csa csb : List Char) (hcstra : CStr m0 pa.toNat csa) (hcstrb : CStr m0 pb.toNat csb)
    (n d : Nat) (hpre : BytePrefix csa csb n) (hnd : n ≤ d) (hd8 : d ≤ n + 8)
    (hnf : n + 8 ≤ csa.length)
    (hagree : ∀ j, n ≤ j → j < d →
      (cwordAt m0 (pa.toNat + n)).extractLsb' (8*(j-n)) 8
        = (cwordAt m0 (pb.toNat + n)).extractLsb' (8*(j-n)) 8) :
    BytePrefix csa csb d ∧ d ≤ csb.length := by
  -- Step 1: d ≤ lb. Suppose lb < d; then n ≤ lb (else hpre nonzero at lb fails), so
  -- lb ∈ [n,d): words agree at byte lb, but B's byte there is the NUL (0) and A's is a
  -- nonzero char — contradiction.
  have hdlb : d ≤ csb.length := by
    rcases Nat.lt_or_ge csb.length d with hlt | hge
    · exfalso
      have hbzlen : byteVal csb csb.length = 0 := by
        unfold byteVal; have : csb[csb.length]? = none := by simp
        rw [this]
      have hnlb : n ≤ csb.length := by
        rcases Nat.lt_or_ge csb.length n with h | h
        · exact absurd ((hpre csb.length h).1.trans hbzlen) (hpre csb.length h).2
        · exact h
      -- byte lb: A char nonzero, B NUL zero, words agree ⇒ contradiction
      have hj8 : csb.length - n < 8 := by omega
      have hlbla : csb.length < csa.length := by omega
      have hAval : ((cwordAt m0 (pa.toNat + n)).extractLsb' (8*(csb.length-n)) 8).toNat
          = byteVal csa csb.length := by
        rw [cword_byte_byteVal m0 pa csa hcstra n (csb.length-n) hj8 (by omega),
          show n + (csb.length - n) = csb.length from by omega]
      have hane : byteVal csa csb.length ≠ 0 := by
        obtain ⟨ba, hba, hbane⟩ := cstr_byte_ne m0 hcstra csb.length hlbla
        rw [← cstr_byteVal m0 pa.toNat csa hcstra csb.length hlbla ba hba hbane]
        exact fun h => hbane (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
      have hBnul : ((cwordAt m0 (pb.toNat + n)).extractLsb' (8*(csb.length-n)) 8) = (0 : BitVec 8) := by
        rw [← mem_byte_of_word m0 pb n csb.length hnlb (by omega), cstr_byte_nul m0 hcstrb]; rfl
      have heqw := hagree csb.length hnlb hlt
      rw [hBnul] at heqw
      -- heqw : A-word-byte = 0#8; so byteVal csa lb = 0, contra hane
      rw [heqw] at hAval
      exact hane (by simpa using hAval.symm)
    · exact hge
  -- Step 2: BytePrefix csa csb d, using i < d ≤ lb so both bytes are chars.
  have hpred : BytePrefix csa csb d := by
    intro i hi
    rcases Nat.lt_or_ge i n with hin | hin
    · exact hpre i hin
    · have hj8 : i - n < 8 := by omega
      have hle : n + (i - n) = i := by omega
      have hilta : i < csa.length := by omega
      have hiltb : n + (i - n) ≤ csb.length := by omega
      have hAval : ((cwordAt m0 (pa.toNat + n)).extractLsb' (8*(i-n)) 8).toNat = byteVal csa i := by
        rw [cword_byte_byteVal m0 pa csa hcstra n (i-n) hj8 (by omega), hle]
      have hBval : ((cwordAt m0 (pb.toNat + n)).extractLsb' (8*(i-n)) 8).toNat = byteVal csb i := by
        rw [cword_byte_byteVal m0 pb csb hcstrb n (i-n) hj8 hiltb, hle]
      have hane : byteVal csa i ≠ 0 := by
        obtain ⟨ba, hba, hbane⟩ := cstr_byte_ne m0 hcstra i hilta
        rw [← cstr_byteVal m0 pa.toNat csa hcstra i hilta ba hba hbane]
        exact fun h => hbane (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
      refine ⟨?_, hane⟩
      have := congrArg BitVec.toNat (hagree i hin hi); rw [hAval, hBval] at this; exact this
  exact ⟨hpred, hdlb⟩

/-! ## Lane compare `WLaneCmp → BDone` (`0xf20 … 0xf80`)

From `WLaneCmp n` (words `wa ≠ wb` at scan offset `n`, prefix agreement to `n`, A
NUL-free), the descending `slli` probes locate the 2-byte block holding the first
differing byte `d = n + j0`; `srli 0x30` + `sub` + `zext.b` extract and subtract it; the
`ret` returns a value with sign `strcmpSpecSign`. `strcmpSpecSign_at` reduces the target
to `isign (byteVal csa d) (byteVal csb d)`; the machine leaves land exactly that sign
via `strcmpSign_sub` (byte paths `f74→f80`) or `strcmpSign_block_sub` (block `ret`s
`f58`/`f70`). -/

/-- **`f74 → f80` byte tail.** At `0xf74` with `a4 = v4`, `a5 = v5`, `a1 = r`, where the
low bytes `ba = v4.extractLsb' 0 8`, `bb = v5.extractLsb' 0 8` are `< 128` and whose
`isign` is the spec sign, the `zext.b`/`zext.b`/`sub`/`ret` returns to `r` with the
correct result sign. -/
theorem lane_f74_to_done (g : (R : Register) → Option (RegisterType R))
    (r v4 v5 : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (halignr : r.toNat % 4 = 0)
    (hba128 : (v4.extractLsb' 0 8).toNat < 128) (hbb128 : (v5.extractLsb' 0 8).toNat < 128)
    (hsign : isign (v4.extractLsb' 0 8).toNat (v5.extractLsb' 0 8).toNat = strcmpSpecSign csa csb)
    (c : Config)
    (hgood : GoodState c.σ) (hloaded : StrcmpLoaded c.σ.mem) (hmem : c.σ.mem = m0)
    (hout : c.σ.sailOutput = o)
    (hpc : c.σ.regs.get? Register.PC = some (0x80006f74#64 : BitVec 64))
    (ha4 : c.σ.regs.get? Register.x14 = some v4) (ha5 : c.σ.regs.get? Register.x15 = some v5)
    (hra : c.σ.regs.get? Register.x1 = some r)
    (hmi : ∃ v, c.σ.regs.get? Register.minstret = some v) (htick : c.tick < 2)
    (hframe : ∀ R : Register, NotWrittenStrcmp R → c.σ.regs.get? R = g R) :
    ∃ c', Steps c c' ∧ BDone g r csa csb m0 o c' := by
  obtain ⟨vmi, hmi⟩ := hmi
  -- f74: a4 = v4 & 0xff
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006f74 c.σ c.tick c.steps (0x80006f74#64) vmi v4 hgood hpc hmi ha4 hloaded rfl htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006f78#64 : BitVec 64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x80006f74#64) 4 = (0x80006f78#64 : BitVec 64) from by decide] at this
  have ha5_1 := obs_alu_other' hobs1 Register.x15 (by decide) ha5
  have hra_1 := obs_alu_other' hobs1 Register.x1 (by decide) hra
  have ha4_1 : σ1.regs.get? Register.x14 = some (zero_extend (m := 64) (v4.extractLsb' 0 8)) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [andi_ff_eq_zext_byte] at this
  have hframe_1 : ∀ R, NotWrittenStrcmp R → σ1.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs1 R hR.2.2.2.2.2.2.2.1 hR).trans (hframe R hR)
  obtain ⟨vmi1, hmi1'⟩ := obs_alu_minstret hobs1
  -- f78: a5 = v5 & 0xff
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006f78 σ1 i1 (c.steps + 1) (0x80006f78#64) vmi1 v5 hG1 hpc1 hmi1' ha5_1 (by rw [hmem1]; exact hloaded) rfl hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006f7c#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006f78#64) 4 = (0x80006f7c#64 : BitVec 64) from by decide] at this
  have ha4_2 := obs_alu_other' hobs2 Register.x14 (by decide) ha4_1
  have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  have ha5_2 : σ2.regs.get? Register.x15 = some (zero_extend (m := 64) (v5.extractLsb' 0 8)) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [andi_ff_eq_zext_byte] at this
  have hframe_2 : ∀ R, NotWrittenStrcmp R → σ2.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs2 R hR.2.2.2.2.2.2.2.2.1 hR).trans (hframe_1 R hR)
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  -- f7c: a0 = a4 - a5
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80006f7c σ2 i2 (c.steps + 1 + 1) (0x80006f7c#64) vmi2
      (zero_extend (m := 64) (v4.extractLsb' 0 8)) (zero_extend (m := 64) (v5.extractLsb' 0 8))
      hG2 hpc2 hmi2' ha4_2 ha5_2 (by rw [hmem2, hmem1]; exact hloaded) rfl hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x80006f80#64 : BitVec 64) := by
    have := obs_alu_pc hobs3; rwa [show BitVec.addInt (0x80006f7c#64) 4 = (0x80006f80#64 : BitVec 64) from by decide] at this
  have ha0_3 : σ3.regs.get? Register.x10
      = some (zero_extend (m := 64) (v4.extractLsb' 0 8) - zero_extend (m := 64) (v5.extractLsb' 0 8)) :=
    obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hra_3 := obs_alu_other' hobs3 Register.x1 (by decide) hra_2
  have hframe_3 : ∀ R, NotWrittenStrcmp R → σ3.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs3 R hR.2.2.2.1 hR).trans (hframe_2 R hR)
  obtain ⟨vmi3, hmi3'⟩ := obs_alu_minstret hobs3
  -- f80: ret
  have htgt : (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
    rw [ret_tgt r halignr]; exact halignr
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80006f80 σ3 i3 (c.steps + 1 + 1 + 1) (0x80006f80#64) vmi3 r
      hG3 hpc3 hmi3' hra_3 (by rw [hmem3, hmem2, hmem1]; exact hloaded) rfl htgt hi3
  have hpc4 : σ4.regs.get? Register.PC = some r := by rw [obs_jr_pc hobs4, ret_tgt r halignr]
  have ha0_4 := obs_jr_other' hobs4 Register.x10 (by decide) ha0_3
  have hra_4 := obs_jr_other' hobs4 Register.x1 (by decide) hra_3
  have hframe_4 : ∀ R, NotWrittenStrcmp R → σ4.regs.get? R = g R :=
    fun R hR => (sframe_jr hobs4 R hR).trans (hframe_3 R hR)
  have hmem4eq : σ4.mem = c.σ.mem := by rw [hmem4, hmem3, hmem2, hmem1]
  have hout4 : σ4.sailOutput = o :=
    (by chain_out [hobs1, hobs2, hobs3, hobs4] : σ4.sailOutput = c.σ.sailOutput).trans hout
  refine ⟨⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩,
    (((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans (Steps.single hs4), ?_⟩
  refine ⟨hG4, hpc4, hra_4, by rw [hmem4eq]; exact hmem, hout4, hi4, ?_, hframe_4⟩
  refine ⟨_, ha0_4, ?_⟩
  rw [strcmpSign_sub (v4.extractLsb' 0 8) (v5.extractLsb' 0 8) hba128 hbb128]; exact hsign

/-- **`f5c → f80` block tail** (a `slli` probe fired; block `{6-s',7-s'}` first differs,
`s' ∈ {2,4,6}`). At `0xf5c` with `a4 = wa <<< 8s'`, `a5 = wb <<< 8s'`, `a1 = r`: `srli
0x30` re-extracts the block, then `sub`/`zext.b`/`bnez` to `f74` (low byte `6-s'`
differs, `j0 = 6-s'`) or `f70` ret (block diff, `j0 = 7-s'`). -/
theorem lane_f5c_tail (g : (R : Register) → Option (RegisterType R))
    (r wa wb : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (n j0 s' : Nat) (halignr : r.toNat % 4 = 0)
    (hs' : s' = 2 ∨ s' = 4 ∨ s' = 6) (hj0lo : j0 = 6 - s' ∨ j0 = 7 - s')
    (hlop : wa.extractLsb' (8*(6-s')) 8 = wb.extractLsb' (8*(6-s')) 8 ∨ j0 = 6 - s')
    (hbytelo_ne : j0 = 6 - s' → wa.extractLsb' (8*(6-s')) 8 ≠ wb.extractLsb' (8*(6-s')) 8)
    (hba128 : (wa.extractLsb' (8*j0) 8).toNat < 128) (hbb128 : (wb.extractLsb' (8*j0) 8).toNat < 128)
    (hsign : isign (wa.extractLsb' (8*j0) 8).toNat (wb.extractLsb' (8*j0) 8).toNat = strcmpSpecSign csa csb)
    (c : Config)
    (hgood : GoodState c.σ) (hloaded : StrcmpLoaded c.σ.mem) (hmem : c.σ.mem = m0)
    (hout : c.σ.sailOutput = o)
    (hpc : c.σ.regs.get? Register.PC = some (0x80006f5c#64 : BitVec 64))
    (ha4 : c.σ.regs.get? Register.x14 = some (wa <<< (8*s'))) (ha5 : c.σ.regs.get? Register.x15 = some (wb <<< (8*s')))
    (hra : c.σ.regs.get? Register.x1 = some r)
    (hmi : ∃ v, c.σ.regs.get? Register.minstret = some v) (htick : c.tick < 2)
    (hframe : ∀ R : Register, NotWrittenStrcmp R → c.σ.regs.get? R = g R) :
    ∃ c', Steps c c' ∧ BDone g r csa csb m0 o c' := by
  obtain ⟨vmi, hmi⟩ := hmi
  have hs'6 : s' ≤ 6 := by rcases hs' with h|h|h <;> omega
  -- block value blk = (w <<< 8s') >>> 48; low byte = byte (6-s'), high byte = byte (7-s')
  have hblkAlt : ((wa <<< (8*s')) >>> (48:Nat)).toNat < 2^16 := shr48_lt _
  have hblkBlt : ((wb <<< (8*s')) >>> (48:Nat)).toNat < 2^16 := shr48_lt _
  have hloA : ((wa <<< (8*s')) >>> (48:Nat)).extractLsb' 0 8 = wa.extractLsb' (8*(6-s')) 8 := shl_shr48_lo wa s' hs'6
  have hloB : ((wb <<< (8*s')) >>> (48:Nat)).extractLsb' 0 8 = wb.extractLsb' (8*(6-s')) 8 := shl_shr48_lo wb s' hs'6
  have hhiA : ((wa <<< (8*s')) >>> (48:Nat)).extractLsb' 8 8 = wa.extractLsb' (8*(7-s')) 8 := shl_shr48_hi wa s' hs'6
  have hhiB : ((wb <<< (8*s')) >>> (48:Nat)).extractLsb' 8 8 = wb.extractLsb' (8*(7-s')) 8 := shl_shr48_hi wb s' hs'6
  -- f5c: a4 = (wa<<<8s') >>> 48
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006f5c c.σ c.tick c.steps (0x80006f5c#64) vmi (wa <<< (8*s')) hgood hpc hmi ha4 hloaded rfl htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006f60#64 : BitVec 64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x80006f5c#64) 4 = (0x80006f60#64 : BitVec 64) from by decide] at this
  have ha5_1 := obs_alu_other' hobs1 Register.x15 (by decide) ha5
  have hra_1 := obs_alu_other' hobs1 Register.x1 (by decide) hra
  have ha4_1 : σ1.regs.get? Register.x14 = some ((wa <<< (8*s')) >>> (48:Nat)) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [shr_48] at this
  have hframe_1 : ∀ R, NotWrittenStrcmp R → σ1.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs1 R hR.2.2.2.2.2.2.2.1 hR).trans (hframe R hR)
  obtain ⟨vmi1, hmi1'⟩ := obs_alu_minstret hobs1
  -- f60: a5 = (wb<<<8s') >>> 48
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006f60 σ1 i1 (c.steps + 1) (0x80006f60#64) vmi1 (wb <<< (8*s')) hG1 hpc1 hmi1' ha5_1 (by rw [hmem1]; exact hloaded) rfl hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006f64#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006f60#64) 4 = (0x80006f64#64 : BitVec 64) from by decide] at this
  have ha4_2 := obs_alu_other' hobs2 Register.x14 (by decide) ha4_1
  have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  have ha5_2 : σ2.regs.get? Register.x15 = some ((wb <<< (8*s')) >>> (48:Nat)) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [shr_48] at this
  have hframe_2 : ∀ R, NotWrittenStrcmp R → σ2.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs2 R hR.2.2.2.2.2.2.2.2.1 hR).trans (hframe_1 R hR)
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  -- f64: a0 = a4 - a5
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80006f64 σ2 i2 (c.steps + 1 + 1) (0x80006f64#64) vmi2 ((wa <<< (8*s')) >>> (48:Nat)) ((wb <<< (8*s')) >>> (48:Nat))
      hG2 hpc2 hmi2' ha4_2 ha5_2 (by rw [hmem2, hmem1]; exact hloaded) rfl hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x80006f68#64 : BitVec 64) := by
    have := obs_alu_pc hobs3; rwa [show BitVec.addInt (0x80006f64#64) 4 = (0x80006f68#64 : BitVec 64) from by decide] at this
  have ha4_3 := obs_alu_other' hobs3 Register.x14 (by decide) ha4_2
  have ha5_3 := obs_alu_other' hobs3 Register.x15 (by decide) ha5_2
  have hra_3 := obs_alu_other' hobs3 Register.x1 (by decide) hra_2
  have ha0_3 : σ3.regs.get? Register.x10 = some ((wa <<< (8*s')) >>> (48:Nat) - (wb <<< (8*s')) >>> (48:Nat)) :=
    obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hframe_3 : ∀ R, NotWrittenStrcmp R → σ3.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs3 R hR.2.2.2.1 hR).trans (hframe_2 R hR)
  obtain ⟨vmi3, hmi3'⟩ := obs_alu_minstret hobs3
  -- f68: a1 = a0 & 0xff
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80006f68 σ3 i3 (c.steps + 1 + 1 + 1) (0x80006f68#64) vmi3 ((wa <<< (8*s')) >>> (48:Nat) - (wb <<< (8*s')) >>> (48:Nat))
      hG3 hpc3 hmi3' ha0_3 (by rw [hmem3, hmem2, hmem1]; exact hloaded) rfl hi3
  have hpc4 : σ4.regs.get? Register.PC = some (0x80006f6c#64 : BitVec 64) := by
    have := obs_alu_pc hobs4; rwa [show BitVec.addInt (0x80006f68#64) 4 = (0x80006f6c#64 : BitVec 64) from by decide] at this
  have ha4_4 := obs_alu_other' hobs4 Register.x14 (by decide) ha4_3
  have ha5_4 := obs_alu_other' hobs4 Register.x15 (by decide) ha5_3
  have hra_4 := obs_alu_other' hobs4 Register.x1 (by decide) hra_3
  have ha0_4 := obs_alu_other' hobs4 Register.x10 (by decide) ha0_3
  have ha1_4 : σ4.regs.get? Register.x11
      = some (((wa <<< (8*s')) >>> (48:Nat) - (wb <<< (8*s')) >>> (48:Nat)) &&& sign_extend (m := 64) (0x0ff#12)) :=
    obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hframe_4 : ∀ R, NotWrittenStrcmp R → σ4.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs4 R hR.2.2.2.2.1 hR).trans (hframe_3 R hR)
  obtain ⟨vmi4, hmi4'⟩ := obs_alu_minstret hobs4
  by_cases hbnez : (((wa <<< (8*s')) >>> (48:Nat) - (wb <<< (8*s')) >>> (48:Nat)) &&& sign_extend (m := 64) (0x0ff#12)) = 0#64
  · -- f70 ret: block diff, low byte agrees ⇒ j0 = 7-s'
    have hguard : ((((wa <<< (8*s')) >>> (48:Nat) - (wb <<< (8*s')) >>> (48:Nat)) &&& sign_extend (m := 64) (0x0ff#12)) != (0#64)) = false := by
      rw [hbnez]; simp
    obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
      site_80006f6c_nottaken σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x80006f6c#64) vmi4
        (((wa <<< (8*s')) >>> (48:Nat) - (wb <<< (8*s')) >>> (48:Nat)) &&& sign_extend (m := 64) (0x0ff#12))
        hG4 hpc4 hmi4' ha1_4 (by rw [hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hguard hi4
    have hpc5 : σ5.regs.get? Register.PC = some (0x80006f70#64 : BitVec 64) := by
      have := obs_bnottaken_pc hobs5; rwa [show BitVec.addInt (0x80006f6c#64) 4 = (0x80006f70#64 : BitVec 64) from by decide] at this
    have ha0_5 := obs_bnottaken_other' hobs5 Register.x10 (by decide) ha0_4
    have hra_5 := obs_bnottaken_other' hobs5 Register.x1 (by decide) hra_4
    have hframe_5 : ∀ R, NotWrittenStrcmp R → σ5.regs.get? R = g R :=
      fun R hR => (sframe_bnottaken hobs5 R hR).trans (hframe_4 R hR)
    obtain ⟨vmi5, hmi5'⟩ := obs_bnottaken_minstret hobs5
    -- low bytes agree ⇒ j0 = 7-s'
    have hlodiff : ((wa <<< (8*s')) >>> (48:Nat) - (wb <<< (8*s')) >>> (48:Nat)).extractLsb' 0 8 = 0#8 := by
      have hz : ((((wa <<< (8*s')) >>> (48:Nat) - (wb <<< (8*s')) >>> (48:Nat)) &&& sign_extend (m := 64) (0x0ff#12)).extractLsb' 0 8) = 0#8 := by
        rw [hbnez]; apply BitVec.eq_of_toNat_eq; decide
      rw [andi_ff_eq_zext_byte] at hz
      apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat hz
      rw [BitVec.extractLsb'_toNat, zext_toNat] at this
      simpa using this
    have hlobyteeq : wa.extractLsb' (8*(6-s')) 8 = wb.extractLsb' (8*(6-s')) 8 := by
      have := (block_diff_lo_zero _ _ hblkAlt hblkBlt).mp hlodiff
      rw [hloA, hloB] at this; exact this
    have hj0hi : j0 = 7 - s' := by
      rcases hj0lo with h | h
      · exact absurd hlobyteeq (hbytelo_ne h)
      · exact h
    -- f70: ret; block diff sign = isign (byte (7-s')) = strcmpSpecSign
    have htgt : (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
      rw [ret_tgt r halignr]; exact halignr
    obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
      site_80006f70 σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x80006f70#64) vmi5 r
        hG5 hpc5 hmi5' hra_5 (by rw [hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl htgt hi5
    have hpc6 : σ6.regs.get? Register.PC = some r := by rw [obs_jr_pc hobs6, ret_tgt r halignr]
    have ha0_6 := obs_jr_other' hobs6 Register.x10 (by decide) ha0_5
    have hra_6 := obs_jr_other' hobs6 Register.x1 (by decide) hra_5
    have hframe_6 : ∀ R, NotWrittenStrcmp R → σ6.regs.get? R = g R :=
      fun R hR => (sframe_jr hobs6 R hR).trans (hframe_5 R hR)
    have hmem6eq : σ6.mem = c.σ.mem := by rw [hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]
    have hout6 : σ6.sailOutput = o :=
      (by chain_out [hobs1, hobs2, hobs3, hobs4, hobs5, hobs6] :
        σ6.sailOutput = c.σ.sailOutput).trans hout
    refine ⟨⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩,
      (((((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans
        (Steps.single hs4)).trans (Steps.single hs5)).trans (Steps.single hs6), ?_⟩
    refine ⟨hG6, hpc6, hra_6, by rw [hmem6eq]; exact hmem, hout6, hi6, ?_, hframe_6⟩
    refine ⟨_, ha0_6, ?_⟩
    have hlomatch : ((wa <<< (8*s')) >>> (48:Nat)).toNat % 256 = ((wb <<< (8*s')) >>> (48:Nat)).toNat % 256 := by
      have := congrArg BitVec.toNat (hloA.trans (hlobyteeq.trans hloB.symm)); rw [block_lo, block_lo] at this; exact this
    have hhiAeq : ((wa <<< (8*s')) >>> (48:Nat)).toNat / 256 = (wa.extractLsb' (8*j0) 8).toNat := by
      rw [← block_hi _ hblkAlt, hhiA, hj0hi]
    have hhiBeq : ((wb <<< (8*s')) >>> (48:Nat)).toNat / 256 = (wb.extractLsb' (8*j0) 8).toNat := by
      rw [← block_hi _ hblkBlt, hhiB, hj0hi]
    rw [strcmpSign_block_sub _ _ hblkAlt hblkBlt hlomatch (by rw [hhiAeq]; exact hba128) (by rw [hhiBeq]; exact hbb128)]
    rw [hhiAeq, hhiBeq]; exact hsign
  · -- f74: low byte differs ⇒ j0 = 6-s'
    have hguard : ((((wa <<< (8*s')) >>> (48:Nat) - (wb <<< (8*s')) >>> (48:Nat)) &&& sign_extend (m := 64) (0x0ff#12)) != (0#64)) = true := by
      rw [bne_iff_ne]; exact hbnez
    obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
      site_80006f6c_taken σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x80006f6c#64) vmi4
        (((wa <<< (8*s')) >>> (48:Nat) - (wb <<< (8*s')) >>> (48:Nat)) &&& sign_extend (m := 64) (0x0ff#12))
        hG4 hpc4 hmi4' ha1_4 (by rw [hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hguard hi4
    have hpceq : (0x80006f6c#64 : BitVec 64) + sign_extend (m := 64) (0x0008#13) = (0x80006f74#64 : BitVec 64) := by
      apply BitVec.eq_of_toNat_eq; decide
    have hpc5 : σ5.regs.get? Register.PC = some (0x80006f74#64 : BitVec 64) := by rw [obs_btaken_pc hobs5, hpceq]
    have ha4_5 := obs_btaken_other' hobs5 Register.x14 (by decide) ha4_4
    have ha5_5 := obs_btaken_other' hobs5 Register.x15 (by decide) ha5_4
    have hra_5 := obs_btaken_other' hobs5 Register.x1 (by decide) hra_4
    have hframe_5 : ∀ R, NotWrittenStrcmp R → σ5.regs.get? R = g R :=
      fun R hR => (sframe_btaken hobs5 R hR).trans (hframe_4 R hR)
    obtain ⟨vmi5, hmi5'⟩ := obs_btaken_minstret hobs5
    have hj0lo6 : j0 = 6 - s' := by
      rcases hj0lo with h | h
      · exact h
      · -- j0 = 7-s' would mean low byte agrees ⇒ block diff low byte 0 ⇒ contra hbnez
        exfalso; apply hbnez
        rcases hlop with hlo | hlo
        · have hd := (block_diff_lo_zero _ _ hblkAlt hblkBlt).mpr (by rw [hloA, hloB]; exact hlo)
          rw [andi_ff_eq_zext_byte]; apply BitVec.eq_of_toNat_eq; rw [zext_toNat, hd]; rfl
        · omega
    have hlowA : ((wa <<< (8*s')) >>> (48:Nat)).extractLsb' 0 8 = wa.extractLsb' (8*j0) 8 := by rw [hloA, hj0lo6]
    have hlowB : ((wb <<< (8*s')) >>> (48:Nat)).extractLsb' 0 8 = wb.extractLsb' (8*j0) 8 := by rw [hloB, hj0lo6]
    obtain ⟨c', hsteps', hDone'⟩ := lane_f74_to_done g r ((wa <<< (8*s')) >>> (48:Nat)) ((wb <<< (8*s')) >>> (48:Nat)) csa csb m0 o halignr
      (by rw [hlowA]; exact hba128) (by rw [hlowB]; exact hbb128)
      (by rw [hlowA, hlowB]; exact hsign)
      ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩
      hG5 (by rw [hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) (by rw [hmem5, hmem4, hmem3, hmem2, hmem1]; exact hmem)
      ((by chain_out [hobs1, hobs2, hobs3, hobs4, hobs5] : σ5.sailOutput = c.σ.sailOutput).trans hout)
      hpc5 ha4_5 ha5_5 hra_5 ⟨vmi5, hmi5'⟩ hi5 hframe_5
    exact ⟨c', ((((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans
      (Steps.single hs4)).trans ((Steps.single hs5).trans hsteps'), hDone'⟩

/-- **`f44 → f80` fall-through tail** (bytes {0..5} agree, `j0 ∈ {6,7}`). At `0xf44`
with `a2 = wa`, `a3 = wb`, `a1 = r`: `srli 0x30` extracts the {6,7} block; `sub`;
`zext.b`; `bnez` routes to `f74` (byte 6 differs, `j0=6`) or `f58` ret (block diff,
`j0=7`). The provided sign facts land `BDone`. -/
theorem lane_fallthrough_tail (g : (R : Register) → Option (RegisterType R))
    (r wa wb : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (n j0 : Nat) (halignr : r.toNat % 4 = 0)
    (hj0 : 6 ≤ j0) (hj0lt : j0 < 8)
    (hlo6 : wa.extractLsb' (8*6) 8 = wb.extractLsb' (8*6) 8 ∨ j0 = 6)
    (hbyte6ne : j0 = 6 → wa.extractLsb' (8*6) 8 ≠ wb.extractLsb' (8*6) 8)
    (hba128 : (wa.extractLsb' (8*j0) 8).toNat < 128) (hbb128 : (wb.extractLsb' (8*j0) 8).toNat < 128)
    (hsign : isign (wa.extractLsb' (8*j0) 8).toNat (wb.extractLsb' (8*j0) 8).toNat = strcmpSpecSign csa csb)
    (c : Config)
    (hgood : GoodState c.σ) (hloaded : StrcmpLoaded c.σ.mem) (hmem : c.σ.mem = m0)
    (hout : c.σ.sailOutput = o)
    (hpc : c.σ.regs.get? Register.PC = some (0x80006f44#64 : BitVec 64))
    (ha2 : c.σ.regs.get? Register.x12 = some wa) (ha3 : c.σ.regs.get? Register.x13 = some wb)
    (hra : c.σ.regs.get? Register.x1 = some r)
    (hmi : ∃ v, c.σ.regs.get? Register.minstret = some v) (htick : c.tick < 2)
    (hframe : ∀ R : Register, NotWrittenStrcmp R → c.σ.regs.get? R = g R) :
    ∃ c', Steps c c' ∧ BDone g r csa csb m0 o c' := by
  obtain ⟨vmi, hmi⟩ := hmi
  -- f44: a4 = wa >>> 48
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006f44 c.σ c.tick c.steps (0x80006f44#64) vmi wa hgood hpc hmi ha2 hloaded rfl htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006f48#64 : BitVec 64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x80006f44#64) 4 = (0x80006f48#64 : BitVec 64) from by decide] at this
  have ha2_1 := obs_alu_other' hobs1 Register.x12 (by decide) ha2
  have ha3_1 := obs_alu_other' hobs1 Register.x13 (by decide) ha3
  have hra_1 := obs_alu_other' hobs1 Register.x1 (by decide) hra
  have ha4_1 : σ1.regs.get? Register.x14 = some (wa >>> (48:Nat)) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [shr_48] at this
  have hframe_1 : ∀ R, NotWrittenStrcmp R → σ1.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs1 R hR.2.2.2.2.2.2.2.1 hR).trans (hframe R hR)
  obtain ⟨vmi1, hmi1'⟩ := obs_alu_minstret hobs1
  -- f48: a5 = wb >>> 48
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006f48 σ1 i1 (c.steps + 1) (0x80006f48#64) vmi1 wb hG1 hpc1 hmi1' ha3_1 (by rw [hmem1]; exact hloaded) rfl hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006f4c#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006f48#64) 4 = (0x80006f4c#64 : BitVec 64) from by decide] at this
  have ha4_2 := obs_alu_other' hobs2 Register.x14 (by decide) ha4_1
  have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  have ha5_2 : σ2.regs.get? Register.x15 = some (wb >>> (48:Nat)) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [shr_48] at this
  have hframe_2 : ∀ R, NotWrittenStrcmp R → σ2.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs2 R hR.2.2.2.2.2.2.2.2.1 hR).trans (hframe_1 R hR)
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  -- f4c: a0 = a4 - a5
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80006f4c σ2 i2 (c.steps + 1 + 1) (0x80006f4c#64) vmi2 (wa >>> (48:Nat)) (wb >>> (48:Nat))
      hG2 hpc2 hmi2' ha4_2 ha5_2 (by rw [hmem2, hmem1]; exact hloaded) rfl hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x80006f50#64 : BitVec 64) := by
    have := obs_alu_pc hobs3; rwa [show BitVec.addInt (0x80006f4c#64) 4 = (0x80006f50#64 : BitVec 64) from by decide] at this
  have ha4_3 := obs_alu_other' hobs3 Register.x14 (by decide) ha4_2
  have ha5_3 := obs_alu_other' hobs3 Register.x15 (by decide) ha5_2
  have hra_3 := obs_alu_other' hobs3 Register.x1 (by decide) hra_2
  have ha0_3 : σ3.regs.get? Register.x10 = some (wa >>> (48:Nat) - wb >>> (48:Nat)) :=
    obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hframe_3 : ∀ R, NotWrittenStrcmp R → σ3.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs3 R hR.2.2.2.1 hR).trans (hframe_2 R hR)
  obtain ⟨vmi3, hmi3'⟩ := obs_alu_minstret hobs3
  -- f50: a1 = a0 & 0xff
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80006f50 σ3 i3 (c.steps + 1 + 1 + 1) (0x80006f50#64) vmi3 (wa >>> (48:Nat) - wb >>> (48:Nat))
      hG3 hpc3 hmi3' ha0_3 (by rw [hmem3, hmem2, hmem1]; exact hloaded) rfl hi3
  have hpc4 : σ4.regs.get? Register.PC = some (0x80006f54#64 : BitVec 64) := by
    have := obs_alu_pc hobs4; rwa [show BitVec.addInt (0x80006f50#64) 4 = (0x80006f54#64 : BitVec 64) from by decide] at this
  have ha4_4 := obs_alu_other' hobs4 Register.x14 (by decide) ha4_3
  have ha5_4 := obs_alu_other' hobs4 Register.x15 (by decide) ha5_3
  have hra_4 := obs_alu_other' hobs4 Register.x1 (by decide) hra_3
  have ha1_4 : σ4.regs.get? Register.x11
      = some ((wa >>> (48:Nat) - wb >>> (48:Nat)) &&& sign_extend (m := 64) (0x0ff#12)) :=
    obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hframe_4 : ∀ R, NotWrittenStrcmp R → σ4.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs4 R hR.2.2.2.2.1 hR).trans (hframe_3 R hR)
  obtain ⟨vmi4, hmi4'⟩ := obs_alu_minstret hobs4
  -- low byte of the block difference: (wa>>>48 - wb>>>48).extractLsb' 0 8, nonzero iff byte 6 differs
  have hlobyteA : (wa >>> (48:Nat)).extractLsb' 0 8 = wa.extractLsb' (8*6) 8 := srli48_byte0 wa
  have hlobyteB : (wb >>> (48:Nat)).extractLsb' 0 8 = wb.extractLsb' (8*6) 8 := srli48_byte0 wb
  by_cases hbnez : ((wa >>> (48:Nat) - wb >>> (48:Nat)) &&& sign_extend (m := 64) (0x0ff#12)) = 0#64
  · -- bnez not taken → f58 ret; means byte 6 agrees, so j0 = 7 (block diff = high byte diff)
    have hguard : (((wa >>> (48:Nat) - wb >>> (48:Nat)) &&& sign_extend (m := 64) (0x0ff#12)) != (0#64)) = false := by
      rw [hbnez]; simp
    obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
      site_80006f54_nottaken σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x80006f54#64) vmi4
        ((wa >>> (48:Nat) - wb >>> (48:Nat)) &&& sign_extend (m := 64) (0x0ff#12))
        hG4 hpc4 hmi4' ha1_4 (by rw [hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hguard hi4
    have hpc5 : σ5.regs.get? Register.PC = some (0x80006f58#64 : BitVec 64) := by
      have := obs_bnottaken_pc hobs5; rwa [show BitVec.addInt (0x80006f54#64) 4 = (0x80006f58#64 : BitVec 64) from by decide] at this
    have ha4_5 := obs_bnottaken_other' hobs5 Register.x14 (by decide) ha4_4
    have ha5_5 := obs_bnottaken_other' hobs5 Register.x15 (by decide) ha5_4
    have ha0_4 := obs_alu_other' hobs4 Register.x10 (by decide) ha0_3
    have ha0_5 := obs_bnottaken_other' hobs5 Register.x10 (by decide) ha0_4
    have hra_5 := obs_bnottaken_other' hobs5 Register.x1 (by decide) hra_4
    have hframe_5 : ∀ R, NotWrittenStrcmp R → σ5.regs.get? R = g R :=
      fun R hR => (sframe_bnottaken hobs5 R hR).trans (hframe_4 R hR)
    obtain ⟨vmi5, hmi5'⟩ := obs_bnottaken_minstret hobs5
    -- byte 6 agrees ⇒ j0 = 7
    have hbyte6eq : wa.extractLsb' (8*6) 8 = wb.extractLsb' (8*6) 8 := by
      -- low byte of the block diff is 0 (from `a1 = block-diff & 0xff = 0`)
      have hlodiff : ((wa >>> (48:Nat) - wb >>> (48:Nat)).extractLsb' 0 8) = 0#8 := by
        have hz : (((wa >>> (48:Nat) - wb >>> (48:Nat)) &&& sign_extend (m := 64) (0x0ff#12)).extractLsb' 0 8) = 0#8 := by
          rw [hbnez]; apply BitVec.eq_of_toNat_eq; decide
        rw [andi_ff_eq_zext_byte] at hz
        apply BitVec.eq_of_toNat_eq
        have := congrArg BitVec.toNat hz
        rw [BitVec.extractLsb'_toNat, zext_toNat] at this
        simpa using this
      have hsub := (block_diff_lo_zero _ _ (shr48_lt wa) (shr48_lt wb)).mp hlodiff
      rw [hlobyteA, hlobyteB] at hsub; exact hsub
    have hj07 : j0 = 7 := by
      rcases Nat.lt_or_ge j0 7 with h7 | h7
      · -- j0 = 6 (since 6 ≤ j0 < 7); but then byte 6 differs, contra hbyte6eq
        have : j0 = 6 := by omega
        exact absurd hbyte6eq (hbyte6ne this)
      · omega
    -- block ret: a0 = wa>>>48 - wb>>>48, sign = isign(byte7) = strcmpSpecSign
    -- f58: ret
    have htgt : (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
      rw [ret_tgt r halignr]; exact halignr
    obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
      site_80006f58 σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x80006f58#64) vmi5 r
        hG5 hpc5 hmi5' hra_5 (by rw [hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl htgt hi5
    have hpc6 : σ6.regs.get? Register.PC = some r := by rw [obs_jr_pc hobs6, ret_tgt r halignr]
    have ha0_6 := obs_jr_other' hobs6 Register.x10 (by decide) ha0_5
    have hra_6 := obs_jr_other' hobs6 Register.x1 (by decide) hra_5
    have hframe_6 : ∀ R, NotWrittenStrcmp R → σ6.regs.get? R = g R :=
      fun R hR => (sframe_jr hobs6 R hR).trans (hframe_5 R hR)
    have hmem6eq : σ6.mem = c.σ.mem := by rw [hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]
    have hout6 : σ6.sailOutput = o :=
      (by chain_out [hobs1, hobs2, hobs3, hobs4, hobs5, hobs6] :
        σ6.sailOutput = c.σ.sailOutput).trans hout
    refine ⟨⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩,
      (((((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans
        (Steps.single hs4)).trans (Steps.single hs5)).trans (Steps.single hs6), ?_⟩
    refine ⟨hG6, hpc6, hra_6, by rw [hmem6eq]; exact hmem, hout6, hi6, ?_, hframe_6⟩
    refine ⟨_, ha0_6, ?_⟩
    -- sign: strcmpSign (wa>>>48 - wb>>>48) = isign (high bytes) = isign (byte7) = strcmpSpecSign
    have hblkA : (wa >>> (48:Nat)).toNat < 2^16 := shr48_lt wa
    have hblkB : (wb >>> (48:Nat)).toNat < 2^16 := shr48_lt wb
    have hlomatch : (wa >>> (48:Nat)).toNat % 256 = (wb >>> (48:Nat)).toNat % 256 := by
      have := congrArg BitVec.toNat (hlobyteA.trans (hbyte6eq.trans hlobyteB.symm))
      rw [block_lo, block_lo] at this; exact this
    have hhiA : (wa >>> (48:Nat)).toNat / 256 = (wa.extractLsb' (8*7) 8).toNat := by
      rw [← block_hi _ hblkA]
      have : (wa >>> (48:Nat)).extractLsb' 8 8 = wa.extractLsb' (8*7) 8 := by
        have := shl_shr48_hi wa 0 (by omega); simpa using this
      rw [this]
    have hhiB : (wb >>> (48:Nat)).toNat / 256 = (wb.extractLsb' (8*7) 8).toNat := by
      rw [← block_hi _ hblkB]
      have : (wb >>> (48:Nat)).extractLsb' 8 8 = wb.extractLsb' (8*7) 8 := by
        have := shl_shr48_hi wb 0 (by omega); simpa using this
      rw [this]
    have hba7 : (wa.extractLsb' (8*7) 8).toNat < 128 := by rw [← hj07]; exact hba128
    have hbb7 : (wb.extractLsb' (8*7) 8).toNat < 128 := by rw [← hj07]; exact hbb128
    rw [strcmpSign_block_sub _ _ hblkA hblkB hlomatch (by rw [hhiA]; exact hba7) (by rw [hhiB]; exact hbb7)]
    rw [hhiA, hhiB, ← hj07]; exact hsign
  · -- bnez taken → f74 (byte 6 differs, j0 = 6)
    have hguard : (((wa >>> (48:Nat) - wb >>> (48:Nat)) &&& sign_extend (m := 64) (0x0ff#12)) != (0#64)) = true := by
      rw [bne_iff_ne]; exact hbnez
    obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
      site_80006f54_taken σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x80006f54#64) vmi4
        ((wa >>> (48:Nat) - wb >>> (48:Nat)) &&& sign_extend (m := 64) (0x0ff#12))
        hG4 hpc4 hmi4' ha1_4 (by rw [hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hguard hi4
    have hpceq : (0x80006f54#64 : BitVec 64) + sign_extend (m := 64) (0x0020#13) = (0x80006f74#64 : BitVec 64) := by
      apply BitVec.eq_of_toNat_eq; decide
    have hpc5 : σ5.regs.get? Register.PC = some (0x80006f74#64 : BitVec 64) := by rw [obs_btaken_pc hobs5, hpceq]
    have ha4_5 := obs_btaken_other' hobs5 Register.x14 (by decide) ha4_4
    have ha5_5 := obs_btaken_other' hobs5 Register.x15 (by decide) ha5_4
    have hra_5 := obs_btaken_other' hobs5 Register.x1 (by decide) hra_4
    have hframe_5 : ∀ R, NotWrittenStrcmp R → σ5.regs.get? R = g R :=
      fun R hR => (sframe_btaken hobs5 R hR).trans (hframe_4 R hR)
    obtain ⟨vmi5, hmi5'⟩ := obs_btaken_minstret hobs5
    -- j0 = 6 (byte 6 differs since low byte of block diff ≠ 0)
    have hj06 : j0 = 6 := by
      rcases hlo6 with h | h
      · -- byte6 agrees ⇒ block diff low byte 0 ⇒ contra hbnez
        exfalso; apply hbnez
        have hsub : (wa >>> (48:Nat)).extractLsb' 0 8 = (wb >>> (48:Nat)).extractLsb' 0 8 := by
          rw [hlobyteA, hlobyteB, h]
        have hd : (wa >>> (48:Nat) - wb >>> (48:Nat)).extractLsb' 0 8 = 0#8 :=
          (block_diff_lo_zero _ _ (shr48_lt wa) (shr48_lt wb)).mpr hsub
        rw [andi_ff_eq_zext_byte]
        apply BitVec.eq_of_toNat_eq
        rw [zext_toNat, hd]; rfl
      · exact h
    -- feed lane_f74_to_done: at f74, a4 = wa>>>48, a5 = wb>>>48; low byte = byte 6 = byte j0
    have hlowA : (wa >>> (48:Nat)).extractLsb' 0 8 = wa.extractLsb' (8*j0) 8 := by rw [hlobyteA, hj06]
    have hlowB : (wb >>> (48:Nat)).extractLsb' 0 8 = wb.extractLsb' (8*j0) 8 := by rw [hlobyteB, hj06]
    obtain ⟨c', hsteps', hDone'⟩ := lane_f74_to_done g r (wa >>> (48:Nat)) (wb >>> (48:Nat)) csa csb m0 o halignr
      (by rw [hlowA]; exact hba128) (by rw [hlowB]; exact hbb128)
      (by rw [hlowA, hlowB]; exact hsign)
      ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩
      hG5 (by rw [hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) (by rw [hmem5, hmem4, hmem3, hmem2, hmem1]; exact hmem)
      ((by chain_out [hobs1, hobs2, hobs3, hobs4, hobs5] : σ5.sailOutput = c.σ.sailOutput).trans hout)
      hpc5 ha4_5 ha5_5 hra_5 ⟨vmi5, hmi5'⟩ hi5 hframe_5
    exact ⟨c', ((((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans
      (Steps.single hs4)).trans ((Steps.single hs5).trans hsteps'), hDone'⟩

/-- Uniform lane-compare preamble: the first differing byte index `j0 < 8`, the byte
values, and the reduced target sign. Kept as one big proof since the machine leaves are
tightly coupled to the located byte. -/
theorem wlane_to_done (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (n : Nat) (halignr : r.toNat % 4 = 0) :
    Triple (WLaneCmp g pa pb r csa csb m0 o n) (BDone g r csa csb m0 o) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hmem, hout, hpc, ha2, ha3, hra, ⟨vmi, hmi⟩, htick,
    hrega, hregb, hcstra, hcstrb, hpre, hnulfree, hwne, hframe⟩ := hSt
  classical
  -- first differing byte index j0 < 8 of the two words
  have hexbyte : ∃ k, k < 8 ∧ (cwordAt m0 (pa.toNat + n)).extractLsb' (8*k) 8
      ≠ (cwordAt m0 (pb.toNat + n)).extractLsb' (8*k) 8 :=
    word_ne_byte _ _ hwne
  have hexj : ∃ k, (cwordAt m0 (pa.toNat + n)).extractLsb' (8*k) 8
      ≠ (cwordAt m0 (pb.toNat + n)).extractLsb' (8*k) 8 := by
    obtain ⟨k, _, hk⟩ := hexbyte; exact ⟨k, hk⟩
  -- least such index via firstDiff-of-bytes is overkill; use the 8-bounded least
  obtain ⟨j0, hj0lt8, hj0spec, hj0min⟩ :
      ∃ j0, j0 < 8 ∧ (cwordAt m0 (pa.toNat + n)).extractLsb' (8*j0) 8
              ≠ (cwordAt m0 (pb.toNat + n)).extractLsb' (8*j0) 8 ∧
            ∀ k, k < j0 → (cwordAt m0 (pa.toNat + n)).extractLsb' (8*k) 8
              = (cwordAt m0 (pb.toNat + n)).extractLsb' (8*k) 8 := by
    -- pick least over {0..7}
    obtain ⟨k0, hk0lt, hk0⟩ := hexbyte
    -- linear search for the least
    have : ∀ N, N ≤ 8 → (∃ k, k < N ∧ (cwordAt m0 (pa.toNat + n)).extractLsb' (8*k) 8
              ≠ (cwordAt m0 (pb.toNat + n)).extractLsb' (8*k) 8) →
        ∃ j0, j0 < 8 ∧ (cwordAt m0 (pa.toNat + n)).extractLsb' (8*j0) 8
              ≠ (cwordAt m0 (pb.toNat + n)).extractLsb' (8*j0) 8 ∧
            ∀ k, k < j0 → (cwordAt m0 (pa.toNat + n)).extractLsb' (8*k) 8
              = (cwordAt m0 (pb.toNat + n)).extractLsb' (8*k) 8 := by
      intro N
      induction N with
      | zero => intro _ ⟨k, hk, _⟩; omega
      | succ N ih =>
        intro hN8 hexN
        by_cases hlow : ∃ k, k < N ∧ (cwordAt m0 (pa.toNat + n)).extractLsb' (8*k) 8
            ≠ (cwordAt m0 (pb.toNat + n)).extractLsb' (8*k) 8
        · exact ih (by omega) hlow
        · -- no diff below N; then the diff is at N itself, and N is least
          refine ⟨N, by omega, ?_, ?_⟩
          · obtain ⟨k, hk, hkne⟩ := hexN
            rcases Nat.lt_or_ge k N with h | h
            · exact absurd ⟨k, h, hkne⟩ hlow
            · have : k = N := by omega
              subst this; exact hkne
          · intro k hk
            exact Decidable.byContradiction (fun hne => hlow ⟨k, hk, hne⟩)
    exact this 8 (Nat.le_refl _) ⟨k0, hk0lt, hk0⟩
  -- absolute differing byte d = n + j0
  have hagree_words : ∀ j, n ≤ j → j < n + j0 →
      (cwordAt m0 (pa.toNat + n)).extractLsb' (8*(j-n)) 8
        = (cwordAt m0 (pb.toNat + n)).extractLsb' (8*(j-n)) 8 := by
    intro j hj1 hj2; exact hj0min (j-n) (by omega)
  obtain ⟨hpred, hdlb⟩ := lane_prefix_extend m0 pa pb csa csb hcstra hcstrb n (n+j0)
    hpre (by omega) (by omega) hnulfree hagree_words
  -- byte values at d = n + j0
  have hbytea : ((cwordAt m0 (pa.toNat + n)).extractLsb' (8*j0) 8).toNat = byteVal csa (n+j0) :=
    cword_byte_byteVal m0 pa csa hcstra n j0 hj0lt8 (by omega)
  have hbyteb : ((cwordAt m0 (pb.toNat + n)).extractLsb' (8*j0) 8).toNat = byteVal csb (n+j0) :=
    cword_byte_byteVal m0 pb csb hcstrb n j0 hj0lt8 (by omega)
  have hbytea128 : ((cwordAt m0 (pa.toNat + n)).extractLsb' (8*j0) 8).toNat < 128 := by
    rw [hbytea]; exact byteVal_lt m0 pa.toNat csa hcstra (n+j0)
  have hbyteb128 : ((cwordAt m0 (pb.toNat + n)).extractLsb' (8*j0) 8).toNat < 128 := by
    rw [hbyteb]; exact byteVal_lt m0 pb.toNat csb hcstrb (n+j0)
  have hbytene : byteVal csa (n+j0) ≠ byteVal csb (n+j0) := by
    rw [← hbytea, ← hbyteb]; intro h; exact hj0spec (BitVec.eq_of_toNat_eq h)
  -- target sign, in extractLsb'-form for the tails
  have hsigntarget : strcmpSpecSign csa csb = isign (byteVal csa (n+j0)) (byteVal csb (n+j0)) :=
    strcmpSpecSign_at csa csb (n+j0) hpred hbytene
  have hsign : isign ((cwordAt m0 (pa.toNat + n)).extractLsb' (8*j0) 8).toNat
      ((cwordAt m0 (pb.toNat + n)).extractLsb' (8*j0) 8).toNat = strcmpSpecSign csa csb := by
    rw [hbytea, hbyteb]; exact hsigntarget.symm
  -- block-agreement characterization: bytes below `p` agree via `hj0min`
  have hbagree : ∀ p, p ≤ j0 → ∀ m, m < p →
      (cwordAt m0 (pa.toNat + n)).extractLsb' (8*m) 8 = (cwordAt m0 (pb.toNat + n)).extractLsb' (8*m) 8 := by
    intro p hp m hm; exact hj0min m (by omega)
  -- f20: a4 = wa <<< 48
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006f20 c.σ c.tick c.steps (0x80006f20#64) vmi (cwordAt m0 (pa.toNat + n)) hgood hpc hmi ha2 hloaded rfl htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006f24#64 : BitVec 64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x80006f20#64) 4 = (0x80006f24#64 : BitVec 64) from by decide] at this
  have ha2_1 := obs_alu_other' hobs1 Register.x12 (by decide) ha2
  have ha3_1 := obs_alu_other' hobs1 Register.x13 (by decide) ha3
  have hra_1 := obs_alu_other' hobs1 Register.x1 (by decide) hra
  have ha4_1 : σ1.regs.get? Register.x14 = some (cwordAt m0 (pa.toNat + n) <<< (48:Nat)) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [shl_48] at this
  have hframe_1 : ∀ R, NotWrittenStrcmp R → σ1.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs1 R hR.2.2.2.2.2.2.2.1 hR).trans (hframe R hR)
  obtain ⟨vmi1, hmi1'⟩ := obs_alu_minstret hobs1
  -- f24: a5 = wb <<< 48
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006f24 σ1 i1 (c.steps + 1) (0x80006f24#64) vmi1 (cwordAt m0 (pb.toNat + n)) hG1 hpc1 hmi1' ha3_1 (by rw [hmem1]; exact hloaded) rfl hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006f28#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006f24#64) 4 = (0x80006f28#64 : BitVec 64) from by decide] at this
  have ha2_2 := obs_alu_other' hobs2 Register.x12 (by decide) ha2_1
  have ha3_2 := obs_alu_other' hobs2 Register.x13 (by decide) ha3_1
  have ha4_2 := obs_alu_other' hobs2 Register.x14 (by decide) ha4_1
  have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  have ha5_2 : σ2.regs.get? Register.x15 = some (cwordAt m0 (pb.toNat + n) <<< (48:Nat)) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [shl_48] at this
  have hframe_2 : ∀ R, NotWrittenStrcmp R → σ2.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs2 R hR.2.2.2.2.2.2.2.2.1 hR).trans (hframe_1 R hR)
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  -- f28: bne a4,a5 (taken iff bytes {0,1} differ iff j0 < 2)
  by_cases hb28 : (cwordAt m0 (pa.toNat + n) <<< (48:Nat)) = (cwordAt m0 (pb.toNat + n) <<< (48:Nat))
  · -- not taken: bytes {0,1} agree ⇒ j0 ≥ 2
    have hj0ge2 : 2 ≤ j0 := by
      have hbyeq := (slli48_eq_iff _ _).mp hb28
      rcases Nat.lt_or_ge j0 2 with h | h
      · exact absurd (hbyeq j0 h) hj0spec
      · exact h
    have hguard : ((cwordAt m0 (pa.toNat + n) <<< (48:Nat)) != (cwordAt m0 (pb.toNat + n) <<< (48:Nat))) = false := by rw [hb28]; simp
    obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
      site_80006f28_nottaken σ2 i2 (c.steps + 1 + 1) (0x80006f28#64) vmi2
        (cwordAt m0 (pa.toNat + n) <<< (48:Nat)) (cwordAt m0 (pb.toNat + n) <<< (48:Nat))
        hG2 hpc2 hmi2' ha4_2 ha5_2 (by rw [hmem2, hmem1]; exact hloaded) rfl hguard hi2
    have hpc3 : σ3.regs.get? Register.PC = some (0x80006f2c#64 : BitVec 64) := by
      have := obs_bnottaken_pc hobs3; rwa [show BitVec.addInt (0x80006f28#64) 4 = (0x80006f2c#64 : BitVec 64) from by decide] at this
    have ha2_3 := obs_bnottaken_other' hobs3 Register.x12 (by decide) ha2_2
    have ha3_3 := obs_bnottaken_other' hobs3 Register.x13 (by decide) ha3_2
    have hra_3 := obs_bnottaken_other' hobs3 Register.x1 (by decide) hra_2
    have hframe_3 : ∀ R, NotWrittenStrcmp R → σ3.regs.get? R = g R :=
      fun R hR => (sframe_bnottaken hobs3 R hR).trans (hframe_2 R hR)
    obtain ⟨vmi3, hmi3'⟩ := obs_bnottaken_minstret hobs3
    -- f2c: a4 = wa <<< 32
    obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
      site_80006f2c σ3 i3 (c.steps + 1 + 1 + 1) (0x80006f2c#64) vmi3 (cwordAt m0 (pa.toNat + n)) hG3 hpc3 hmi3' ha2_3 (by rw [hmem3, hmem2, hmem1]; exact hloaded) rfl hi3
    have hpc4 : σ4.regs.get? Register.PC = some (0x80006f30#64 : BitVec 64) := by
      have := obs_alu_pc hobs4; rwa [show BitVec.addInt (0x80006f2c#64) 4 = (0x80006f30#64 : BitVec 64) from by decide] at this
    have ha2_4 := obs_alu_other' hobs4 Register.x12 (by decide) ha2_3
    have ha3_4 := obs_alu_other' hobs4 Register.x13 (by decide) ha3_3
    have hra_4 := obs_alu_other' hobs4 Register.x1 (by decide) hra_3
    have ha4_4 : σ4.regs.get? Register.x14 = some (cwordAt m0 (pa.toNat + n) <<< (32:Nat)) := by
      have := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [shl_32] at this
    have hframe_4 : ∀ R, NotWrittenStrcmp R → σ4.regs.get? R = g R :=
      fun R hR => (sframe_alu hobs4 R hR.2.2.2.2.2.2.2.1 hR).trans (hframe_3 R hR)
    obtain ⟨vmi4, hmi4'⟩ := obs_alu_minstret hobs4
    -- f30: a5 = wb <<< 32
    obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
      site_80006f30 σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x80006f30#64) vmi4 (cwordAt m0 (pb.toNat + n)) hG4 hpc4 hmi4' ha3_4 (by rw [hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi4
    have hpc5 : σ5.regs.get? Register.PC = some (0x80006f34#64 : BitVec 64) := by
      have := obs_alu_pc hobs5; rwa [show BitVec.addInt (0x80006f30#64) 4 = (0x80006f34#64 : BitVec 64) from by decide] at this
    have ha2_5 := obs_alu_other' hobs5 Register.x12 (by decide) ha2_4
    have ha3_5 := obs_alu_other' hobs5 Register.x13 (by decide) ha3_4
    have ha4_5 := obs_alu_other' hobs5 Register.x14 (by decide) ha4_4
    have hra_5 := obs_alu_other' hobs5 Register.x1 (by decide) hra_4
    have ha5_5 : σ5.regs.get? Register.x15 = some (cwordAt m0 (pb.toNat + n) <<< (32:Nat)) := by
      have := obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [shl_32] at this
    have hframe_5 : ∀ R, NotWrittenStrcmp R → σ5.regs.get? R = g R :=
      fun R hR => (sframe_alu hobs5 R hR.2.2.2.2.2.2.2.2.1 hR).trans (hframe_4 R hR)
    obtain ⟨vmi5, hmi5'⟩ := obs_alu_minstret hobs5
    -- f34: bne (taken iff bytes {0..3} differ iff j0 < 4)
    by_cases hb34 : (cwordAt m0 (pa.toNat + n) <<< (32:Nat)) = (cwordAt m0 (pb.toNat + n) <<< (32:Nat))
    · have hj0ge4 : 4 ≤ j0 := by
        have hbyeq := (slli32_eq_iff _ _).mp hb34
        rcases Nat.lt_or_ge j0 4 with h | h
        · exact absurd (hbyeq j0 h) hj0spec
        · exact h
      have hguard : ((cwordAt m0 (pa.toNat + n) <<< (32:Nat)) != (cwordAt m0 (pb.toNat + n) <<< (32:Nat))) = false := by rw [hb34]; simp
      obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
        site_80006f34_nottaken σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x80006f34#64) vmi5
          (cwordAt m0 (pa.toNat + n) <<< (32:Nat)) (cwordAt m0 (pb.toNat + n) <<< (32:Nat))
          hG5 hpc5 hmi5' ha4_5 ha5_5 (by rw [hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hguard hi5
      have hpc6 : σ6.regs.get? Register.PC = some (0x80006f38#64 : BitVec 64) := by
        have := obs_bnottaken_pc hobs6; rwa [show BitVec.addInt (0x80006f34#64) 4 = (0x80006f38#64 : BitVec 64) from by decide] at this
      have ha2_6 := obs_bnottaken_other' hobs6 Register.x12 (by decide) ha2_5
      have ha3_6 := obs_bnottaken_other' hobs6 Register.x13 (by decide) ha3_5
      have hra_6 := obs_bnottaken_other' hobs6 Register.x1 (by decide) hra_5
      have hframe_6 : ∀ R, NotWrittenStrcmp R → σ6.regs.get? R = g R :=
        fun R hR => (sframe_bnottaken hobs6 R hR).trans (hframe_5 R hR)
      obtain ⟨vmi6, hmi6'⟩ := obs_bnottaken_minstret hobs6
      -- f38: a4 = wa <<< 16
      obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
        site_80006f38 σ6 i6 (c.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x80006f38#64) vmi6 (cwordAt m0 (pa.toNat + n)) hG6 hpc6 hmi6' ha2_6 (by rw [hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi6
      have hpc7 : σ7.regs.get? Register.PC = some (0x80006f3c#64 : BitVec 64) := by
        have := obs_alu_pc hobs7; rwa [show BitVec.addInt (0x80006f38#64) 4 = (0x80006f3c#64 : BitVec 64) from by decide] at this
      have ha2_7 := obs_alu_other' hobs7 Register.x12 (by decide) ha2_6
      have ha3_7 := obs_alu_other' hobs7 Register.x13 (by decide) ha3_6
      have hra_7 := obs_alu_other' hobs7 Register.x1 (by decide) hra_6
      have ha4_7 : σ7.regs.get? Register.x14 = some (cwordAt m0 (pa.toNat + n) <<< (16:Nat)) := by
        have := obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [shl_16] at this
      have hframe_7 : ∀ R, NotWrittenStrcmp R → σ7.regs.get? R = g R :=
        fun R hR => (sframe_alu hobs7 R hR.2.2.2.2.2.2.2.1 hR).trans (hframe_6 R hR)
      obtain ⟨vmi7, hmi7'⟩ := obs_alu_minstret hobs7
      -- f3c: a5 = wb <<< 16
      obtain ⟨σ8, i8, hs8, hi8, hG8, hmem8, hobs8⟩ :=
        site_80006f3c σ7 i7 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80006f3c#64) vmi7 (cwordAt m0 (pb.toNat + n)) hG7 hpc7 hmi7' ha3_7 (by rw [hmem7, hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi7
      have hpc8 : σ8.regs.get? Register.PC = some (0x80006f40#64 : BitVec 64) := by
        have := obs_alu_pc hobs8; rwa [show BitVec.addInt (0x80006f3c#64) 4 = (0x80006f40#64 : BitVec 64) from by decide] at this
      have ha2_8 := obs_alu_other' hobs8 Register.x12 (by decide) ha2_7
      have ha3_8 := obs_alu_other' hobs8 Register.x13 (by decide) ha3_7
      have ha4_8 := obs_alu_other' hobs8 Register.x14 (by decide) ha4_7
      have hra_8 := obs_alu_other' hobs8 Register.x1 (by decide) hra_7
      have ha5_8 : σ8.regs.get? Register.x15 = some (cwordAt m0 (pb.toNat + n) <<< (16:Nat)) := by
        have := obs_alu_rd hobs8 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [shl_16] at this
      have hframe_8 : ∀ R, NotWrittenStrcmp R → σ8.regs.get? R = g R :=
        fun R hR => (sframe_alu hobs8 R hR.2.2.2.2.2.2.2.2.1 hR).trans (hframe_7 R hR)
      obtain ⟨vmi8, hmi8'⟩ := obs_alu_minstret hobs8
      -- f40: bne (taken iff bytes {0..5} differ iff j0 < 6)
      by_cases hb40 : (cwordAt m0 (pa.toNat + n) <<< (16:Nat)) = (cwordAt m0 (pb.toNat + n) <<< (16:Nat))
      · -- not taken ⇒ j0 ≥ 6 ⇒ fallthrough f44
        have hj0ge6 : 6 ≤ j0 := by
          have hbyeq := (slli16_eq_iff _ _).mp hb40
          rcases Nat.lt_or_ge j0 6 with h | h
          · exact absurd (hbyeq j0 h) hj0spec
          · exact h
        have hguard : ((cwordAt m0 (pa.toNat + n) <<< (16:Nat)) != (cwordAt m0 (pb.toNat + n) <<< (16:Nat))) = false := by rw [hb40]; simp
        obtain ⟨σ9, i9, hs9, hi9, hG9, hmem9, hobs9⟩ :=
          site_80006f40_nottaken σ8 i8 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80006f40#64) vmi8
            (cwordAt m0 (pa.toNat + n) <<< (16:Nat)) (cwordAt m0 (pb.toNat + n) <<< (16:Nat))
            hG8 hpc8 hmi8' ha4_8 ha5_8 (by rw [hmem8, hmem7, hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hguard hi8
        have hpc9 : σ9.regs.get? Register.PC = some (0x80006f44#64 : BitVec 64) := by
          have := obs_bnottaken_pc hobs9; rwa [show BitVec.addInt (0x80006f40#64) 4 = (0x80006f44#64 : BitVec 64) from by decide] at this
        have ha2_9 := obs_bnottaken_other' hobs9 Register.x12 (by decide) ha2_8
        have ha3_9 := obs_bnottaken_other' hobs9 Register.x13 (by decide) ha3_8
        have hra_9 := obs_bnottaken_other' hobs9 Register.x1 (by decide) hra_8
        have hframe_9 : ∀ R, NotWrittenStrcmp R → σ9.regs.get? R = g R :=
          fun R hR => (sframe_bnottaken hobs9 R hR).trans (hframe_8 R hR)
        obtain ⟨vmi9, hmi9'⟩ := obs_bnottaken_minstret hobs9
        have hj078 : 6 ≤ j0 := hj0ge6
        obtain ⟨c', hsteps', hDone'⟩ := lane_fallthrough_tail g r (cwordAt m0 (pa.toNat + n)) (cwordAt m0 (pb.toNat + n)) csa csb m0 o n j0 halignr
          hj0ge6 hj0lt8
          (by rcases Nat.lt_or_ge 6 j0 with h | h
              · left; exact hj0min 6 (by omega)
              · right; omega)
          (by intro h; rw [← h]; exact hj0spec)
          hbytea128 hbyteb128 hsign
          ⟨σ9, i9, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
          hG9 (by rw [hmem9, hmem8, hmem7, hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded)
          (by rw [hmem9, hmem8, hmem7, hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]; exact hmem)
          ((by chain_out [hobs1, hobs2, hobs3, hobs4, hobs5, hobs6, hobs7, hobs8, hobs9] :
            σ9.sailOutput = c.σ.sailOutput).trans hout)
          hpc9 ha2_9 ha3_9 hra_9 ⟨vmi9, hmi9'⟩ hi9 hframe_9
        exact ⟨c', (((((((((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans
          (Steps.single hs4)).trans (Steps.single hs5)).trans (Steps.single hs6)).trans (Steps.single hs7)).trans
          (Steps.single hs8)).trans (Steps.single hs9)).trans hsteps', hDone'⟩
      · -- f40 taken ⇒ block {4,5} first differs (s'=2); j0 ∈ {4,5}
        have hj045 : j0 = 4 ∨ j0 = 5 := by
          have hne : ¬ (∀ m, m < 6 → (cwordAt m0 (pa.toNat + n)).extractLsb' (8*m) 8 = (cwordAt m0 (pb.toNat + n)).extractLsb' (8*m) 8) := by
            intro hall; exact hb40 ((slli16_eq_iff _ _).mpr hall)
          rcases Nat.lt_or_ge j0 6 with h | h
          · omega
          · exact absurd (fun m hm => hj0min m (by omega)) hne
        have hguard : ((cwordAt m0 (pa.toNat + n) <<< (16:Nat)) != (cwordAt m0 (pb.toNat + n) <<< (16:Nat))) = true := by rw [bne_iff_ne]; exact hb40
        obtain ⟨σ9, i9, hs9, hi9, hG9, hmem9, hobs9⟩ :=
          site_80006f40_taken σ8 i8 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80006f40#64) vmi8
            (cwordAt m0 (pa.toNat + n) <<< (16:Nat)) (cwordAt m0 (pb.toNat + n) <<< (16:Nat))
            hG8 hpc8 hmi8' ha4_8 ha5_8 (by rw [hmem8, hmem7, hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hguard hi8
        have hpceq : (0x80006f40#64 : BitVec 64) + sign_extend (m := 64) (0x001c#13) = (0x80006f5c#64 : BitVec 64) := by
          apply BitVec.eq_of_toNat_eq; decide
        have hpc9 : σ9.regs.get? Register.PC = some (0x80006f5c#64 : BitVec 64) := by rw [obs_btaken_pc hobs9, hpceq]
        have ha4_9 := obs_btaken_other' hobs9 Register.x14 (by decide) ha4_8
        have ha5_9 := obs_btaken_other' hobs9 Register.x15 (by decide) ha5_8
        have hra_9 := obs_btaken_other' hobs9 Register.x1 (by decide) hra_8
        have hframe_9 : ∀ R, NotWrittenStrcmp R → σ9.regs.get? R = g R :=
          fun R hR => (sframe_btaken hobs9 R hR).trans (hframe_8 R hR)
        obtain ⟨vmi9, hmi9'⟩ := obs_btaken_minstret hobs9
        obtain ⟨c', hsteps', hDone'⟩ := lane_f5c_tail g r (cwordAt m0 (pa.toNat + n)) (cwordAt m0 (pb.toNat + n)) csa csb m0 o n j0 2 halignr
          (by left; rfl) (by omega)
          (by rcases hj045 with h | h
              · right; omega
              · left; exact hj0min 4 (by omega))
          (by intro h; have hh := hj0spec; rw [h] at hh; exact hh)
          hbytea128 hbyteb128 hsign
          ⟨σ9, i9, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
          hG9 (by rw [hmem9, hmem8, hmem7, hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded)
          (by rw [hmem9, hmem8, hmem7, hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]; exact hmem)
          ((by chain_out [hobs1, hobs2, hobs3, hobs4, hobs5, hobs6, hobs7, hobs8, hobs9] :
            σ9.sailOutput = c.σ.sailOutput).trans hout)
          hpc9 (by rw [show 8*2 = 16 from by decide]; exact ha4_9) (by rw [show 8*2 = 16 from by decide]; exact ha5_9) hra_9 ⟨vmi9, hmi9'⟩ hi9 hframe_9
        exact ⟨c', (((((((((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans
          (Steps.single hs4)).trans (Steps.single hs5)).trans (Steps.single hs6)).trans (Steps.single hs7)).trans
          (Steps.single hs8)).trans (Steps.single hs9)).trans hsteps', hDone'⟩
    · -- f34 taken ⇒ block {2,3} first differs (s'=4); j0 ∈ {2,3}
      have hj023 : j0 = 2 ∨ j0 = 3 := by
        have hne : ¬ (∀ m, m < 4 → (cwordAt m0 (pa.toNat + n)).extractLsb' (8*m) 8 = (cwordAt m0 (pb.toNat + n)).extractLsb' (8*m) 8) := by
          intro hall; exact hb34 ((slli32_eq_iff _ _).mpr hall)
        rcases Nat.lt_or_ge j0 4 with h | h
        · omega
        · exact absurd (fun m hm => hj0min m (by omega)) hne
      have hguard : ((cwordAt m0 (pa.toNat + n) <<< (32:Nat)) != (cwordAt m0 (pb.toNat + n) <<< (32:Nat))) = true := by rw [bne_iff_ne]; exact hb34
      obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
        site_80006f34_taken σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x80006f34#64) vmi5
          (cwordAt m0 (pa.toNat + n) <<< (32:Nat)) (cwordAt m0 (pb.toNat + n) <<< (32:Nat))
          hG5 hpc5 hmi5' ha4_5 ha5_5 (by rw [hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hguard hi5
      have hpceq : (0x80006f34#64 : BitVec 64) + sign_extend (m := 64) (0x0028#13) = (0x80006f5c#64 : BitVec 64) := by
        apply BitVec.eq_of_toNat_eq; decide
      have hpc6 : σ6.regs.get? Register.PC = some (0x80006f5c#64 : BitVec 64) := by rw [obs_btaken_pc hobs6, hpceq]
      have ha4_6 := obs_btaken_other' hobs6 Register.x14 (by decide) ha4_5
      have ha5_6 := obs_btaken_other' hobs6 Register.x15 (by decide) ha5_5
      have hra_6 := obs_btaken_other' hobs6 Register.x1 (by decide) hra_5
      have hframe_6 : ∀ R, NotWrittenStrcmp R → σ6.regs.get? R = g R :=
        fun R hR => (sframe_btaken hobs6 R hR).trans (hframe_5 R hR)
      obtain ⟨vmi6, hmi6'⟩ := obs_btaken_minstret hobs6
      obtain ⟨c', hsteps', hDone'⟩ := lane_f5c_tail g r (cwordAt m0 (pa.toNat + n)) (cwordAt m0 (pb.toNat + n)) csa csb m0 o n j0 4 halignr
        (by right; left; rfl) (by omega)
        (by rcases hj023 with h | h
            · right; omega
            · left; exact hj0min 2 (by omega))
        (by intro h; have hh := hj0spec; rw [h] at hh; exact hh)
        hbytea128 hbyteb128 hsign
        ⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩
        hG6 (by rw [hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded)
        (by rw [hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]; exact hmem)
        ((by chain_out [hobs1, hobs2, hobs3, hobs4, hobs5, hobs6] :
          σ6.sailOutput = c.σ.sailOutput).trans hout)
        hpc6 (by rw [show 8*4 = 32 from by decide]; exact ha4_6) (by rw [show 8*4 = 32 from by decide]; exact ha5_6) hra_6 ⟨vmi6, hmi6'⟩ hi6 hframe_6
      exact ⟨c', ((((((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans
        (Steps.single hs4)).trans (Steps.single hs5)).trans (Steps.single hs6)).trans hsteps', hDone'⟩
  · -- f28 taken ⇒ block {0,1} first differs (s'=6); j0 ∈ {0,1}
    have hj001 : j0 = 0 ∨ j0 = 1 := by
      have hne : ¬ (∀ m, m < 2 → (cwordAt m0 (pa.toNat + n)).extractLsb' (8*m) 8 = (cwordAt m0 (pb.toNat + n)).extractLsb' (8*m) 8) := by
        intro hall; exact hb28 ((slli48_eq_iff _ _).mpr hall)
      rcases Nat.lt_or_ge j0 2 with h | h
      · omega
      · exact absurd (fun m hm => hj0min m (by omega)) hne
    have hguard : ((cwordAt m0 (pa.toNat + n) <<< (48:Nat)) != (cwordAt m0 (pb.toNat + n) <<< (48:Nat))) = true := by rw [bne_iff_ne]; exact hb28
    obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
      site_80006f28_taken σ2 i2 (c.steps + 1 + 1) (0x80006f28#64) vmi2
        (cwordAt m0 (pa.toNat + n) <<< (48:Nat)) (cwordAt m0 (pb.toNat + n) <<< (48:Nat))
        hG2 hpc2 hmi2' ha4_2 ha5_2 (by rw [hmem2, hmem1]; exact hloaded) rfl hguard hi2
    have hpceq : (0x80006f28#64 : BitVec 64) + sign_extend (m := 64) (0x0034#13) = (0x80006f5c#64 : BitVec 64) := by
      apply BitVec.eq_of_toNat_eq; decide
    have hpc3 : σ3.regs.get? Register.PC = some (0x80006f5c#64 : BitVec 64) := by rw [obs_btaken_pc hobs3, hpceq]
    have ha4_3 := obs_btaken_other' hobs3 Register.x14 (by decide) ha4_2
    have ha5_3 := obs_btaken_other' hobs3 Register.x15 (by decide) ha5_2
    have hra_3 := obs_btaken_other' hobs3 Register.x1 (by decide) hra_2
    have hframe_3 : ∀ R, NotWrittenStrcmp R → σ3.regs.get? R = g R :=
      fun R hR => (sframe_btaken hobs3 R hR).trans (hframe_2 R hR)
    obtain ⟨vmi3, hmi3'⟩ := obs_btaken_minstret hobs3
    obtain ⟨c', hsteps', hDone'⟩ := lane_f5c_tail g r (cwordAt m0 (pa.toNat + n)) (cwordAt m0 (pb.toNat + n)) csa csb m0 o n j0 6 halignr
      (by right; right; rfl) (by omega)
      (by rcases hj001 with h | h
          · right; omega
          · left; exact hj0min 0 (by omega))
      (by intro h; have hh := hj0spec; rw [h] at hh; exact hh)
      hbytea128 hbyteb128 hsign
      ⟨σ3, i3, c.steps + 1 + 1 + 1⟩
      hG3 (by rw [hmem3, hmem2, hmem1]; exact hloaded)
      (by rw [hmem3, hmem2, hmem1]; exact hmem)
      ((by chain_out [hobs1, hobs2, hobs3] : σ3.sailOutput = c.σ.sailOutput).trans hout)
      hpc3 (by rw [show 8*6 = 48 from by decide]; exact ha4_3) (by rw [show 8*6 = 48 from by decide]; exact ha5_3) hra_3 ⟨vmi3, hmi3'⟩ hi3 hframe_3
    exact ⟨c', (((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans hsteps', hDone'⟩

/-! ## Byte-suffix bridge for the NUL-exit byte loop

The NUL-exit blocks, on `a2 ≠ a3`, jump to the byte loop `0xf84` at the ADVANCED pointer
`pa+n`. Ghost the tail as `csa.drop n` / `csb.drop n`, based at `pa.toNat + n` /
`pb.toNat + n`. We need:
* `cstr_drop` — a suffix of a `CStr` is a `CStr` at the shifted base;
* `byteVal_drop` — `byteVal (cs.drop n) i = byteVal cs (n + i)`;
* `firstDiff`/`strcmpSpecSign` on the suffixes equal those on the whole strings, given
  agreement + nonzero on `[0,n)` (`BytePrefix csa csb n`). -/

/-- A suffix of a `CStr`. If `CStr m a cs` and `n ≤ cs.length`, then
`CStr m (a+n) (cs.drop n)`. -/
theorem cstr_drop (m : Mem) : ∀ {a : Nat} {cs : List Char}, CStr m a cs →
    ∀ (n : Nat), n ≤ cs.length → CStr m (a + n) (cs.drop n) := by
  intro a cs hcs
  induction hcs with
  | @nil a hnil =>
    intro n hn
    have : n = 0 := by simpa using hn
    subst this; simpa using CStr.nil hnil
  | @cons a b cs hb hbne hblt hrest ih =>
    intro n hn
    match n with
    | 0 => simpa using CStr.cons hb hbne hblt hrest
    | n+1 =>
      have hn' : n ≤ cs.length := by simpa using hn
      have := ih n hn'
      rw [List.drop_succ_cons, show a + (n+1) = (a+1) + n from by omega]
      exact this

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

/-- Aligned word-entry precondition at `0x80006ea0`. -/
structure PreWCmp (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrcmpLoaded c.σ.mem
  mem : c.σ.mem = m0
  out : c.σ.sailOutput = o
  pc : c.σ.regs.get? Register.PC = some (0x80006ea0#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some pa
  a1 : c.σ.regs.get? Register.x11 = some pb
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  rega : StrcmpWRegion pa csa.length
  regb : StrcmpWRegion pb csb.length
  cstra : CStr m0 pa.toNat csa
  cstrb : CStr m0 pb.toNat csb
  maskpin : MaskPinned m0
  aligned : ((pa ||| pb) &&& sign_extend (m := 64) (0x007#12)) = 0#64
  hframe : ∀ R : Register, NotWrittenStrcmp R → c.σ.regs.get? R = g R

/-- **Aligned entry** `0xea0 → 0xeb8`: establishes `WHead 0`. -/
theorem entry_word (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (o : Array String) :
    Triple (PreWCmp g pa pb r csa csb m0 o) (WHead g pa pb r csa csb m0 o 0) := by
  intro c hPre
  obtain ⟨hgood, hloaded, hmem, hout, hpc, ha0, ha1, hra, ⟨vmi, hmi⟩, htick,
    hrega, hregb, hcstra, hcstrb, hmaskpin, halign, hframe⟩ := hPre
  -- ea0: or a4,a0,a1 → a4 = pa | pb
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006ea0 c.σ c.tick c.steps (0x80006ea0#64) vmi pa pb hgood hpc hmi ha0 ha1 hloaded rfl htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006ea4#64 : BitVec 64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x80006ea0#64) 4 = (0x80006ea4#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_alu_other' hobs1 Register.x10 (by decide) ha0
  have ha1_1 := obs_alu_other' hobs1 Register.x11 (by decide) ha1
  have ha4_1 : σ1.regs.get? Register.x14 = some (pa ||| pb) :=
    obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hra_1 := obs_alu_other' hobs1 Register.x1 (by decide) hra
  have hframe_1 : ∀ R, NotWrittenStrcmp R → σ1.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs1 R hR.2.2.2.2.2.2.2.1 hR).trans (hframe R hR)
  obtain ⟨vmi1, hmi1'⟩ := obs_alu_minstret hobs1
  -- ea4: li t2,-1 → t2 = allOnes
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006ea4 σ1 i1 (c.steps + 1) (0x80006ea4#64) vmi1 hG1 hpc1 hmi1' (by rw [hmem1]; exact hloaded) rfl hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006ea8#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006ea4#64) 4 = (0x80006ea8#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other' hobs2 Register.x10 (by decide) ha0_1
  have ha1_2 := obs_alu_other' hobs2 Register.x11 (by decide) ha1_1
  have ha4_2 := obs_alu_other' hobs2 Register.x14 (by decide) ha4_1
  have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  have ht2_2 : σ2.regs.get? Register.x7 = some (BitVec.allOnes 64) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [show ((0#64) + sign_extend (m := 64) (0xfff#12) : BitVec 64) = BitVec.allOnes 64 from by
      apply BitVec.eq_of_toNat_eq; decide] at this
    exact this
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  -- ea8: andi a4,a4,7 → a4 = (pa|pb) & 7
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80006ea8 σ2 i2 (c.steps + 1 + 1) (0x80006ea8#64) vmi2 (pa ||| pb)
      hG2 hpc2 hmi2' ha4_2 (by rw [hmem2, hmem1]; exact hloaded) rfl hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x80006eac#64 : BitVec 64) := by
    have := obs_alu_pc hobs3; rwa [show BitVec.addInt (0x80006ea8#64) 4 = (0x80006eac#64 : BitVec 64) from by decide] at this
  have ha0_3 := obs_alu_other' hobs3 Register.x10 (by decide) ha0_2
  have ha1_3 := obs_alu_other' hobs3 Register.x11 (by decide) ha1_2
  have ht2_3 := obs_alu_other' hobs3 Register.x7 (by decide) ht2_2
  have ha4_3 : σ3.regs.get? Register.x14 = some ((pa ||| pb) &&& sign_extend (m := 64) (0x007#12)) :=
    obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hra_3 := obs_alu_other' hobs3 Register.x1 (by decide) hra_2
  have hframe_3 : ∀ R, NotWrittenStrcmp R → σ3.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs3 R hR.2.2.2.2.2.2.2.1 hR).trans
      ((sframe_alu hobs2 R hR.2.2.1 hR).trans (hframe_1 R hR))
  obtain ⟨vmi3, hmi3'⟩ := obs_alu_minstret hobs3
  -- eac: bnez a4 NOT taken (aligned) → eb0
  have hguard : (((pa ||| pb) &&& sign_extend (m := 64) (0x007#12)) != (0#64)) = false := by
    rw [halign]; simp
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80006eac_nottaken σ3 i3 (c.steps + 1 + 1 + 1) (0x80006eac#64) vmi3
      ((pa ||| pb) &&& sign_extend (m := 64) (0x007#12))
      hG3 hpc3 hmi3' ha4_3 (by rw [hmem3, hmem2, hmem1]; exact hloaded) rfl hguard hi3
  have hpc4 : σ4.regs.get? Register.PC = some (0x80006eb0#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs4; rwa [show BitVec.addInt (0x80006eac#64) 4 = (0x80006eb0#64 : BitVec 64) from by decide] at this
  have ha0_4 := obs_bnottaken_other' hobs4 Register.x10 (by decide) ha0_3
  have ha1_4 := obs_bnottaken_other' hobs4 Register.x11 (by decide) ha1_3
  have ht2_4 := obs_bnottaken_other' hobs4 Register.x7 (by decide) ht2_3
  have hra_4 := obs_bnottaken_other' hobs4 Register.x1 (by decide) hra_3
  have hframe_4 : ∀ R, NotWrittenStrcmp R → σ4.regs.get? R = g R :=
    fun R hR => (sframe_bnottaken hobs4 R hR).trans (hframe_3 R hR)
  obtain ⟨vmi4, hmi4'⟩ := obs_bnottaken_minstret hobs4
  -- eb0: auipc a5,0x14 → a5 = 0x8001aeb0
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80006eb0 σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x80006eb0#64) vmi4 hG4 hpc4 hmi4' (by rw [hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi4
  have hpc5 : σ5.regs.get? Register.PC = some (0x80006eb4#64 : BitVec 64) := by
    have := obs_alu_pc hobs5; rwa [show BitVec.addInt (0x80006eb0#64) 4 = (0x80006eb4#64 : BitVec 64) from by decide] at this
  have ha0_5 := obs_alu_other' hobs5 Register.x10 (by decide) ha0_4
  have ha1_5 := obs_alu_other' hobs5 Register.x11 (by decide) ha1_4
  have ht2_5 := obs_alu_other' hobs5 Register.x7 (by decide) ht2_4
  have hra_5 := obs_alu_other' hobs5 Register.x1 (by decide) hra_4
  have ha5_5 : σ5.regs.get? Register.x15 = some (0x8001aeb0#64 : BitVec 64) := by
    have := obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [auipc_mask_base] at this
  have hframe_5 : ∀ R, NotWrittenStrcmp R → σ5.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs5 R hR.2.2.2.2.2.2.2.2.1 hR).trans (hframe_4 R hR)
  obtain ⟨vmi5, hmi5'⟩ := obs_alu_minstret hobs5
  -- eb4: ld a5,-560(a5) [mask] → a5 = magic7f
  have hloadbnds := mask_ld_addr
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_80006eb4 σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x80006eb4#64) vmi5 (0x8001aeb0#64)
      hG5 hpc5 hmi5' ha5_5 (by rw [hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl
      (by rw [mask_ld_addr]; decide) (by rw [mask_ld_addr]; decide)
      (by rw [mask_ld_addr]; left; decide) (by rw [mask_ld_addr]; decide) hi5
  have hpc6 : σ6.regs.get? Register.PC = some (0x80006eb8#64 : BitVec 64) := by
    have := obs_alu_pc hobs6; rwa [show BitVec.addInt (0x80006eb4#64) 4 = (0x80006eb8#64 : BitVec 64) from by decide] at this
  have ha0_6 := obs_alu_other' hobs6 Register.x10 (by decide) ha0_5
  have ha1_6 := obs_alu_other' hobs6 Register.x11 (by decide) ha1_5
  have ht2_6 := obs_alu_other' hobs6 Register.x7 (by decide) ht2_5
  have hra_6 := obs_alu_other' hobs6 Register.x1 (by decide) hra_5
  have ha5_6 : σ6.regs.get? Register.x15 = some magic7f := by
    have := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [show (sign_extend (m := 64)
        (ldBytesT (afterNextPC (afterPrelude σ5) (0x80006eb4#64)) ((0x8001aeb0#64) + sign_extend (m := 64) (0xdd0#12))))
        = magic7f from by
      have haddr : ((0x8001aeb0#64 : BitVec 64) + sign_extend (m := 64) (0xdd0#12)) = (0x8001ac80#64 : BitVec 64) := by
        apply BitVec.eq_of_toNat_eq; rw [mask_ld_addr]; decide
      rw [haddr, ldBytesT_mask _ (by
        rw [mem_afterNextPC, mem_afterPrelude, hmem5, hmem4, hmem3, hmem2, hmem1, hmem]; exact hmaskpin),
        sext64_self]] at this
    exact this
  have hframe_6 : ∀ R, NotWrittenStrcmp R → σ6.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs6 R hR.2.2.2.2.2.2.2.2.1 hR).trans (hframe_5 R hR)
  obtain ⟨vmi6, hmi6'⟩ := obs_alu_minstret hobs6
  have hmem6eq : σ6.mem = c.σ.mem := by rw [hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]
  have hout6 : σ6.sailOutput = o :=
    (by chain_out [hobs1, hobs2, hobs3, hobs4, hobs5, hobs6] :
      σ6.sailOutput = c.σ.sailOutput).trans hout
  refine ⟨⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩,
    (((((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans
      (Steps.single hs4)).trans (Steps.single hs5)).trans (Steps.single hs6), ?_⟩
  refine ⟨hG6, by rw [hmem6eq]; exact hloaded, by rw [hmem6eq]; exact hmem, hout6, hpc6, ?_, ?_,
    ha5_6, ht2_6, hra_6, ⟨vmi6, hmi6'⟩, hi6, hrega, hregb, hcstra, hcstrb, hmaskpin,
    (fun i hi => absurd hi (by omega)), (by omega), hframe_6⟩
  · rw [show pa + BitVec.ofNat 64 (24*0) = pa from by simp]; exact ha0_6
  · rw [show pb + BitVec.ofNat 64 (24*0) = pb from by simp]; exact ha1_6

/-- **Aligned word path, entry through loop exit.** Composes `entry_word` (`0xea0 →
`WHead 0`) with the verified word loop `swloop_to_exit`. Lands in `WordExit` = the lane
compare `WLaneCmp` (which `wlane_to_done` carries to `BDone`) or a NUL-word block. -/
theorem strcmp_word_reaches_exit (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (o : Array String) :
    Triple (PreWCmp g pa pb r csa csb m0 o) (WordExit g pa pb r csa csb m0 o) := by
  refine (entry_word g pa pb r csa csb m0 o).seq ?_
  -- WHead 0 ⟹ SWLoopI, then swloop_to_exit
  refine (?_ : Triple (WHead g pa pb r csa csb m0 o 0) (SWLoopI g pa pb r csa csb m0 o)).seq
    (swloop_to_exit g pa pb r csa csb m0 o)
  intro c hHead
  exact ⟨c, .refl c, Or.inl ⟨0, hHead⟩⟩

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
