import Vsa.Sim.SnprintfSpec38

/-!
# M3 Layer-3 — `SnprintfSpec39` : the byte-for-byte `intToString` bridge

pctrace item 4: the buffer content produced by the verified svfprintf `%lld`
chain **is** `(intToString v.toInt).toUTF8`.  Spec37/38 export the digit bytes
as the arithmetic formula

    bs2 k = ofNat 8 (48 + (mag / 10^(n2−1−k)) % 10)     (k < n2)

together with `1 ≤ n2 ≤ 20`, the leading-digit bound `mag / 10^(n2−1) ≤ 9`
(equivalently `mag < 10^n2`) and — since the `DLI` minimality widening — the
lower bound `n2 = 1 ∨ 9 < mag / 10^(n2−2)` (equivalently `10^(n2−1) ≤ mag`
for `n2 ≥ 2`), which pins `n2` as *the* decimal digit count.  This module
closes the gap to `Vsa.While.natToString` / `intToString`:

* `digitList_eq_natDigits_39` — the digit-formula list *is* `natDigits`
  (the mathematical heart: induction on `n2` along `natDigits_step`'s
  split, using minimality for the recursive guard);
* `digits_eq_natToString` — the `BitVec 8` byte list = `natToString mag`'s
  characters (via `digitChar_toNat_39`);
* `toUTF8_toList_ascii_39` — for ASCII strings, `toUTF8` is the byte image
  of the character list (the v4.29 `String`-as-`ByteArray` representation:
  `toUTF8 = toByteArray`, `utf8EncodeChar c = [c.toNat]` for `c ≤ 127`);
* `natToString_toUTF8_toList_39` / `intToString_neg_toUTF8_toList_39` —
  the UTF-8 byte lists of the magnitude string and of the negative
  rendering `"-" ++ …`;
* `svfprintf_buffer_eq_intToString` — the machine-facing verdict:
  `signByte :: [bs2 0, …, bs2 (n2−1)] = (intToString v.toInt).toUTF8` bytes,
  under exactly the hypotheses Spec38's postcondition exports;
* `svfprintf_lld_intToString_spec` — the composed capstone: Spec38 with the
  buffer content restated **byte-for-byte** as
  `(intToString (llArg …).toInt).toUTF8`, indexed into the caller buffer
  `[d, d + len)` with `a0 = len` = the UTF-8 length.
-/

open Vsa Vsa.Sim Vsa.While
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Sim.Code (SvfprintfSliceLoaded SvfprintfSlice2Loaded FlushPinsLoaded MemmoveLoaded
  __ssprint_rLoaded __locale_mb_cur_maxLoaded __ascii_mbtowcLoaded __hidden___udivdi3Loaded)

namespace Vsa.Sim

set_option maxHeartbeats 1600000

/-! ## Digit characters -/

/-- `(Nat.digitChar d).toNat = 48 + d` for `d < 10` — the numeric converse of
`digitChar_eq`. -/
theorem digitChar_toNat_39 (d : Nat) (h : d < 10) : (Nat.digitChar d).toNat = 48 + d := by
  match d, h with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl

/-- Digit characters are ASCII. -/
theorem digitChar_ascii_39 (d : Nat) (h : d < 10) : (Nat.digitChar d).toNat ≤ 127 := by
  rw [digitChar_toNat_39 d h]; omega

/-- Every character `natDigits` produces is ASCII. -/
theorem natDigits_ascii_39 (f n : Nat) : ∀ c ∈ natDigits f n, c.toNat ≤ 127 := by
  induction f generalizing n with
  | zero => intro c hc; simp [natDigits] at hc
  | succ f ih =>
    intro c hc
    unfold natDigits at hc
    by_cases h : n < 10
    · rw [if_pos h] at hc
      rw [List.mem_singleton.mp hc]
      exact digitChar_ascii_39 n h
    · rw [if_neg h] at hc
      rcases List.mem_append.mp hc with h1 | h1
      · exact ih (n / 10) c h1
      · rw [List.mem_singleton.mp h1]
        exact digitChar_ascii_39 (n % 10) (Nat.mod_lt _ (by omega))

/-! ## `natToString`'s character list -/

/-- `foldl push` builds exactly the appended character list. -/
theorem foldl_push_toList_39 (l : List Char) (s : String) :
    (l.foldl String.push s).toList = s.toList ++ l := by
  induction l generalizing s with
  | nil => simp
  | cons c t ih => rw [List.foldl_cons, ih, String.toList_push]; simp

/-- `(natToString n).toList = natDigits (n+1) n`. -/
theorem natToString_toList_39 (n : Nat) :
    (natToString n).toList = natDigits (n + 1) n := by
  unfold Vsa.While.natToString
  rw [foldl_push_toList_39]
  rfl

/-! ## The digit-formula list IS `natDigits` (the heart) -/

/-- **The digit-formula/`natDigits` identity.**  For `1 ≤ n2` with
`mag / 10^(n2−1) ≤ 9` (at most `n2` digits) and the minimality bound
`n2 = 1 ∨ 9 < mag / 10^(n2−2)` (at least `n2` digits), the MSB-first
digit-formula list is exactly `natDigits (mag+1) mag` — `n2` really is the
decimal digit count and the formula enumerates the digits in order. -/
theorem digitList_eq_natDigits_39 (n2 : Nat) : ∀ (mag : Nat), 1 ≤ n2 →
    mag / 10 ^ (n2 - 1) ≤ 9 → (n2 = 1 ∨ 9 < mag / 10 ^ (n2 - 2)) →
    (List.range n2).map (fun k => Nat.digitChar (mag / 10 ^ (n2 - 1 - k) % 10))
      = natDigits (mag + 1) mag := by
  induction n2 with
  | zero => intro mag h1 _ _; omega
  | succ m ih =>
    intro mag h1 hub hlb
    cases m with
    | zero =>
      -- n2 = 1: a single digit, mag ≤ 9
      have hm9 : mag ≤ 9 := by
        have h := hub
        rwa [show 0 + 1 - 1 = 0 from rfl, Nat.pow_zero, Nat.div_one] at h
      rw [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil]
      unfold natDigits
      rw [if_pos (show mag < 10 by omega)]
      rw [show 0 + 1 - 1 - 0 = 0 from rfl, Nat.pow_zero, Nat.div_one,
        Nat.mod_eq_of_lt (by omega)]
    | succ j =>
      -- n2 = j + 2 ≥ 2: minimality gives the recursion guard 9 < mag / 10^j
      have hgt : 9 < mag / 10 ^ j := by
        rcases hlb with h | h
        · omega
        · rwa [show j + 1 + 1 - 2 = j from by omega] at h
      have hmag10 : 10 ≤ mag := by
        have hle : mag / 10 ^ j ≤ mag := Nat.div_le_self _ _
        omega
      -- split both sides at the last digit
      rw [natDigits_step mag hmag10, List.range_succ, List.map_append]
      -- the recursive hypotheses for mag / 10 with n2' = j + 1
      have hub' : (mag / 10) / 10 ^ (j + 1 - 1) ≤ 9 := by
        rw [show j + 1 - 1 = j from rfl, Nat.div_div_eq_div_mul,
          show 10 * 10 ^ j = 10 ^ (j + 1) from by rw [Nat.pow_succ']]
        exact hub
      have hlb' : j + 1 = 1 ∨ 9 < (mag / 10) / 10 ^ (j + 1 - 2) := by
        cases j with
        | zero => exact Or.inl rfl
        | succ i =>
          refine Or.inr ?_
          rw [show i + 1 + 1 - 2 = i from by omega, Nat.div_div_eq_div_mul,
            show 10 * 10 ^ i = 10 ^ (i + 1) from by rw [Nat.pow_succ']]
          exact hgt
      congr 1
      · -- head part: re-index onto mag / 10
        rw [← ih (mag / 10) (by omega) hub' hlb']
        apply List.map_congr_left
        intro k hk
        have hklt : k < j + 1 := List.mem_range.mp hk
        have hexp : mag / 10 ^ (j + 1 + 1 - 1 - k) = (mag / 10) / 10 ^ (j + 1 - 1 - k) := by
          rw [show j + 1 + 1 - 1 - k = (j - k) + 1 from by omega,
            show j + 1 - 1 - k = j - k from by omega,
            Nat.pow_succ', ← Nat.div_div_eq_div_mul]
        rw [hexp]
      · -- last digit: exponent 0
        simp only [List.map_cons, List.map_nil]
        rw [show j + 1 + 1 - 1 - (j + 1) = 0 from by omega, Nat.pow_zero, Nat.div_one]

/-- **The byte-list/`natToString` identity** (`BitVec 8` form, matching
Spec37/38's `bs2` export): the machine's digit bytes are the `toNat` image of
`natToString mag`'s characters. -/
theorem digits_eq_natToString (mag n2 : Nat) (bs : Nat → BitVec 8)
    (h1 : 1 ≤ n2)
    (hbs : ∀ k, k < n2 → bs k = BitVec.ofNat 8 (48 + mag / 10 ^ (n2 - 1 - k) % 10))
    (hub : mag / 10 ^ (n2 - 1) ≤ 9)
    (hlb : n2 = 1 ∨ 9 < mag / 10 ^ (n2 - 2)) :
    (List.range n2).map bs
      = (natToString mag).toList.map (fun ch => BitVec.ofNat 8 ch.toNat) := by
  rw [natToString_toList_39, ← digitList_eq_natDigits_39 n2 mag h1 hub hlb, List.map_map]
  apply List.map_congr_left
  intro k hk
  have hklt : k < n2 := List.mem_range.mp hk
  rw [hbs k hklt]
  show BitVec.ofNat 8 (48 + mag / 10 ^ (n2 - 1 - k) % 10)
      = BitVec.ofNat 8 (Nat.digitChar (mag / 10 ^ (n2 - 1 - k) % 10)).toNat
  rw [digitChar_toNat_39 _ (Nat.mod_lt _ (by omega))]

/-! ## The UTF-8 byte image (ASCII strings) -/

/-- ASCII characters UTF-8-encode to their single code-point byte. -/
theorem utf8EncodeChar_ascii_39 (c : Char) (h : c.toNat ≤ 127) :
    String.utf8EncodeChar c = [UInt8.ofNat c.toNat] := by
  simp only [String.utf8EncodeChar]
  rw [if_pos (show c.val.toNat ≤ 127 from h)]
  rfl

/-- `flatMap utf8EncodeChar` over an ASCII list is the byte map. -/
theorem flatMap_utf8_ascii_39 (l : List Char) (h : ∀ c ∈ l, c.toNat ≤ 127) :
    l.flatMap String.utf8EncodeChar = l.map (fun c => UInt8.ofNat c.toNat) := by
  induction l with
  | nil => rfl
  | cons c t ih =>
    rw [List.flatMap_cons, List.map_cons,
      utf8EncodeChar_ascii_39 c (h c (List.mem_cons_self ..)),
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    rfl

/-- **`toUTF8` of an ASCII string is the byte image of its character list**
(v4.29 `String` = UTF-8 `ByteArray`; `toUTF8 = toByteArray`). -/
theorem toUTF8_toList_ascii_39 (s : String) (h : ∀ c ∈ s.toList, c.toNat ≤ 127) :
    s.toUTF8.data.toList = s.toList.map (fun c => UInt8.ofNat c.toNat) := by
  rw [show s.toUTF8 = s.toByteArray from rfl, ← String.utf8Encode_toList]
  simp only [List.utf8Encode]
  rw [List.toList_data_toByteArray, flatMap_utf8_ascii_39 _ h]

/-- The `UInt8` byte map of `natToString mag` = the digit formula. -/
theorem natToString_map_bytes_39 (mag n2 : Nat)
    (h1 : 1 ≤ n2) (hub : mag / 10 ^ (n2 - 1) ≤ 9)
    (hlb : n2 = 1 ∨ 9 < mag / 10 ^ (n2 - 2)) :
    (natToString mag).toList.map (fun c => UInt8.ofNat c.toNat)
      = (List.range n2).map (fun k => UInt8.ofNat (48 + mag / 10 ^ (n2 - 1 - k) % 10)) := by
  rw [natToString_toList_39, ← digitList_eq_natDigits_39 n2 mag h1 hub hlb, List.map_map]
  apply List.map_congr_left
  intro k hk
  have hklt : k < n2 := List.mem_range.mp hk
  show UInt8.ofNat (Nat.digitChar (mag / 10 ^ (n2 - 1 - k) % 10)).toNat
      = UInt8.ofNat (48 + mag / 10 ^ (n2 - 1 - k) % 10)
  rw [digitChar_toNat_39 _ (Nat.mod_lt _ (by omega))]

/-- **`(natToString mag).toUTF8`, byte for byte** = the digit formula. -/
theorem natToString_toUTF8_toList_39 (mag n2 : Nat)
    (h1 : 1 ≤ n2) (hub : mag / 10 ^ (n2 - 1) ≤ 9)
    (hlb : n2 = 1 ∨ 9 < mag / 10 ^ (n2 - 2)) :
    (natToString mag).toUTF8.data.toList
      = (List.range n2).map (fun k => UInt8.ofNat (48 + mag / 10 ^ (n2 - 1 - k) % 10)) := by
  rw [toUTF8_toList_ascii_39 _ (by rw [natToString_toList_39]; exact natDigits_ascii_39 _ _),
    natToString_map_bytes_39 mag n2 h1 hub hlb]

/-! ## The negative arm: `'-' ::` digits = `intToString v.toInt` -/

/-- **`(intToString v.toInt).toUTF8`, byte for byte**, for negative `v`
(top bit set): the `'-'` byte (45) followed by the digit-formula bytes of the
magnitude `((0#64) − v).toNat` (INT64_MIN-safe via `intToString_neg`). -/
theorem intToString_neg_toUTF8_toList_39 (v : BitVec 64) (n2 : Nat)
    (hneg : 2 ^ 63 ≤ v.toNat) (h1 : 1 ≤ n2)
    (hub : ((0#64) - v).toNat / 10 ^ (n2 - 1) ≤ 9)
    (hlb : n2 = 1 ∨ 9 < ((0#64) - v).toNat / 10 ^ (n2 - 2)) :
    (intToString v.toInt).toUTF8.data.toList
      = UInt8.ofNat 45 :: (List.range n2).map
          (fun k => UInt8.ofNat (48 + ((0#64) - v).toNat / 10 ^ (n2 - 1 - k) % 10)) := by
  have h0v : ((0#64) - v) = -v := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_neg, BitVec.toNat_sub]
    simp
  rw [intToString_neg v hneg, ← h0v]
  have hascii : ∀ c ∈ ("-" ++ natToString ((0#64) - v).toNat).toList, c.toNat ≤ 127 := by
    intro c hc
    rw [String.toList_append] at hc
    rcases List.mem_append.mp hc with h | h
    · have hc' : c = '-' := by
        rw [show ("-" : String).toList = ['-'] from rfl] at h
        exact List.mem_singleton.mp h
      rw [hc']
      decide
    · rw [natToString_toList_39] at h
      exact natDigits_ascii_39 _ _ c h
  rw [toUTF8_toList_ascii_39 _ hascii, String.toList_append,
    show ("-" : String).toList = ['-'] from rfl, List.map_append, List.map_cons, List.map_nil,
    List.singleton_append]
  congr 1
  exact natToString_map_bytes_39 ((0#64) - v).toNat n2 h1 hub hlb

/-- **The machine-facing byte-for-byte verdict**, in exactly the vocabulary
Spec38's postcondition exports: for the negative `%lld` argument `v`, the
flushed buffer content `signByte :: [bs2 0, …, bs2 (n2−1)]` *is*
`(intToString v.toInt).toUTF8` (as `BitVec 8` bytes). -/
theorem svfprintf_buffer_eq_intToString (v : BitVec 64) (n2 : Nat) (bs2 : Nat → BitVec 8)
    (hneg : zopz0zKzJ_s v (0#64) = false)
    (h1 : 1 ≤ n2)
    (hbs : ∀ k, k < n2 → bs2 k = BitVec.ofNat 8
      (48 + (((0#64) - v).toNat / 10 ^ (n2 - 1 - k)) % 10))
    (hub : ((0#64) - v).toNat / 10 ^ (n2 - 1) ≤ 9)
    (hlb : n2 = 1 ∨ 9 < ((0#64) - v).toNat / 10 ^ (n2 - 2)) :
    signByte :: (List.range n2).map bs2
      = (intToString v.toInt).toUTF8.data.toList.map (fun u => u.toBitVec) := by
  rw [intToString_neg_toUTF8_toList_39 v n2 (bgez_false' v hneg) h1 hub hlb,
    List.map_cons, List.map_map]
  refine List.cons_eq_cons.mpr ⟨by decide, ?_⟩
  exact List.map_congr_left (fun k hk => by
    rw [hbs k (List.mem_range.mp hk)]; rfl)

/-! ## The composed capstone: Spec38 restated byte-for-byte -/

/-- **svfprintf `%lld`, byte-for-byte `intToString`.**  The full
`svfprintf_lld_spec` chain with the buffer content restated as the UTF-8
bytes of `intToString (llArg …).toInt`: `a0 = the byte length`, and the
caller buffer `[d, d + len)` holds exactly `ubytes` — the `toUTF8` byte
list.  (Hypotheses are verbatim `svfprintf_lld_spec`'s; see Spec38.) -/
theorem svfprintf_lld_intToString_spec
    (vsp vra0 va0 vfile vfmt vva d : BitVec 64)
    (vS0o vS1o vS2o vS3o vS4o vS5o vS6o vS7o vS8o vS9o vS10o vS11o : BitVec 64)
    (fl0 fl1 : BitVec 8) (cap32 : BitVec 32)
    (a0 a1 a2 a3 a4b a5b a6 a7 : BitVec 8)
    (c : Config)
    (hG : GoodState c.σ)
    (hsl0 : SvfprintfSliceLoaded c.σ.mem)
    (hsl20 : SvfprintfSlice2Loaded c.σ.mem)
    (hlc0 : Vsa.Sim.Code._localeconv_rLoaded c.σ.mem)
    (hstr0 : Vsa.Sim.Code.StrlenLoaded c.σ.mem)
    (hms0 : Vsa.Sim.Code.MemsetLoaded c.σ.mem)
    (hlm0 : __locale_mb_cur_maxLoaded c.σ.mem)
    (hamb0 : __ascii_mbtowcLoaded c.σ.mem)
    (hum0 : Vsa.Sim.Code.__umoddi3Loaded c.σ.mem)
    (hud0 : __hidden___udivdi3Loaded c.σ.mem)
    (hfp0 : FlushPinsLoaded c.σ.mem)
    (hap0 : Vsa.Sim.Code.ArmPinsLoaded c.σ.mem)
    (hslot0 : ParseSlotPinned 0x64 (0x80008008#64) c.σ.mem)
    (hsspL0 : __ssprint_rLoaded c.σ.mem)
    (hsspuL0 : Vsa.Sim.Code.__ssputs_rLoaded c.σ.mem)
    (hmvL0 : MemmoveLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x80007654#64))
    (hx2 : c.σ.regs.get? Register.x2 = some (vsp + (592#64)))
    (hx1 : c.σ.regs.get? Register.x1 = some vra0)
    (hx3 : c.σ.regs.get? Register.x3 = some (0x8001b510#64))
    (hx10 : c.σ.regs.get? Register.x10 = some va0)
    (hx11 : c.σ.regs.get? Register.x11 = some vfile)
    (hx12 : c.σ.regs.get? Register.x12 = some vfmt)
    (hx13 : c.σ.regs.get? Register.x13 = some vva)
    (hx8 : c.σ.regs.get? Register.x8 = some vS0o)
    (hx9 : c.σ.regs.get? Register.x9 = some vS1o)
    (hx22 : c.σ.regs.get? Register.x22 = some vS6o)
    (hx18 : c.σ.regs.get? Register.x18 = some vS2o)
    (hx19 : c.σ.regs.get? Register.x19 = some vS3o)
    (hx20 : c.σ.regs.get? Register.x20 = some vS4o)
    (hx21 : c.σ.regs.get? Register.x21 = some vS5o)
    (hx23 : c.σ.regs.get? Register.x23 = some vS7o)
    (hx24 : c.σ.regs.get? Register.x24 = some vS8o)
    (hx25 : c.σ.regs.get? Register.x25 = some vS9o)
    (hx26 : c.σ.regs.get? Register.x26 = some vS10o)
    (hx27 : c.σ.regs.get? Register.x27 = some vS11o)
    (hdp0 : c.σ.mem[(0x8001b898 : Nat)]? = some (0x70#8))
    (hdp1 : c.σ.mem[(0x8001b898 : Nat) + 1]? = some (0x97#8))
    (hdp2 : c.σ.mem[(0x8001b898 : Nat) + 2]? = some (0x01#8))
    (hdp3 : c.σ.mem[(0x8001b898 : Nat) + 3]? = some (0x80#8))
    (hdp4 : c.σ.mem[(0x8001b898 : Nat) + 4]? = some (0x00#8))
    (hdp5 : c.σ.mem[(0x8001b898 : Nat) + 5]? = some (0x00#8))
    (hdp6 : c.σ.mem[(0x8001b898 : Nat) + 6]? = some (0x00#8))
    (hdp7 : c.σ.mem[(0x8001b898 : Nat) + 7]? = some (0x00#8))
    (hdb0 : c.σ.mem[(0x80019770 : Nat)]? = some (0x2e#8))
    (hdb1 : c.σ.mem[(0x80019770 : Nat) + 1]? = some (0x00#8))
    (hdb2 : c.σ.mem[(0x80019770 : Nat) + 2]? = some (0x00#8))
    (hdb3 : c.σ.mem[(0x80019770 : Nat) + 3]? = some (0x00#8))
    (hdb4 : c.σ.mem[(0x80019770 : Nat) + 4]? = some (0x00#8))
    (hdb5 : c.σ.mem[(0x80019770 : Nat) + 5]? = some (0x00#8))
    (hdb6 : c.σ.mem[(0x80019770 : Nat) + 6]? = some (0x00#8))
    (hdb7 : c.σ.mem[(0x80019770 : Nat) + 7]? = some (0x00#8))
    (hfn0 : c.σ.mem[(0x8001b880 : Nat)]? = some (0x68#8))
    (hfn1 : c.σ.mem[(0x8001b880 : Nat) + 1]? = some (0x22#8))
    (hfn2 : c.σ.mem[(0x8001b880 : Nat) + 2]? = some (0x01#8))
    (hfn3 : c.σ.mem[(0x8001b880 : Nat) + 3]? = some (0x80#8))
    (hfn4 : c.σ.mem[(0x8001b880 : Nat) + 4]? = some (0x00#8))
    (hfn5 : c.σ.mem[(0x8001b880 : Nat) + 5]? = some (0x00#8))
    (hfn6 : c.σ.mem[(0x8001b880 : Nat) + 6]? = some (0x00#8))
    (hfn7 : c.σ.mem[(0x8001b880 : Nat) + 7]? = some (0x00#8))
    (hmbB : c.σ.mem[(0x8001b8f8 : Nat)]? = some (0x01#8))
    (htb0 : c.σ.mem[(0x8001a22c : Nat)]? = some (0x38#8))
    (htb1 : c.σ.mem[(0x8001a22c : Nat) + 1]? = some (0xe4#8))
    (htb2 : c.σ.mem[(0x8001a22c : Nat) + 2]? = some (0xfe#8))
    (htb3 : c.σ.mem[(0x8001a22c : Nat) + 3]? = some (0xff#8))
    (hfmt0 : c.σ.mem[vfmt.toNat]? = some (0x25#8))
    (hfmt1 : c.σ.mem[vfmt.toNat + 1]? = some (0x6c#8))
    (hfmt2 : c.σ.mem[vfmt.toNat + 2]? = some (0x6c#8))
    (hfmt3 : c.σ.mem[vfmt.toNat + 3]? = some (0x64#8))
    (hfmt4 : c.σ.mem[vfmt.toNat + 4]? = some (0x00#8))
    (hfl0B : c.σ.mem[vfile.toNat + 16]? = some fl0)
    (hfl1B : c.σ.mem[vfile.toNat + 17]? = some fl1)
    (hflagB : (zero_extend (m := 64) ((fl1.append fl0) : BitVec (8 * 2)) : BitVec 64)
        &&& sign_extend (m := 64) (0x080#12) = 0#64)
    (hflag40 : (zero_extend (m := 64) ((fl1.append fl0) : BitVec (8 * 2)) : BitVec 64)
        &&& sign_extend (m := 64) (0x040#12) = 0#64)
    (hsinkcur : Pin8 c.σ.mem vfile.toNat d)
    (hsinkcap : Pin4 c.σ.mem (vfile.toNat + 12) cap32)
    (hcap21 : 21 < cap32.toNat)
    (hcap31 : cap32.toNat < 2 ^ 31)
    (ha0 : c.σ.mem[vva.toNat]? = some a0)
    (ha1 : c.σ.mem[vva.toNat + 1]? = some a1)
    (ha2 : c.σ.mem[vva.toNat + 2]? = some a2)
    (ha3 : c.σ.mem[vva.toNat + 3]? = some a3)
    (ha4 : c.σ.mem[vva.toNat + 4]? = some a4b)
    (ha5 : c.σ.mem[vva.toNat + 5]? = some a5b)
    (ha6 : c.σ.mem[vva.toNat + 6]? = some a6)
    (ha7 : c.σ.mem[vva.toNat + 7]? = some a7)
    (hvlo : 0x80000000 ≤ vva.toNat)
    (hvhiram : vva.toNat + 8 ≤ 0x100000000)
    (hvhtif : vva.toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ vva.toNat)
    (hvalign : vva.toNat % 8 = 0)
    (hvdisj : vva.toNat + 8 ≤ vsp.toNat ∨ vsp.toNat + 592 ≤ vva.toNat)
    (hneg : zopz0zKzJ_s (llArg a0 a1 a2 a3 a4b a5b a6 a7) (0#64) = false)
    (hfilelo : vsp.toNat + 592 ≤ vfile.toNat)
    (hfilehi : vfile.toNat + 24 ≤ 0x100000000)
    (hfileal : vfile.toNat % 8 = 0)
    (hflo : 0x80000000 ≤ vfmt.toNat)
    (hfhi : vfmt.toNat + 8 ≤ 0x100000000)
    (hfhtif : vfmt.toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ vfmt.toNat)
    (hfstk : vfmt.toNat + 8 ≤ vsp.toNat - 128 ∨ vsp.toNat + 592 ≤ vfmt.toNat)
    (hfd : vfmt.toNat + 8 ≤ d.toNat ∨ d.toNat + 21 ≤ vfmt.toNat)
    (hfpp : vfmt.toNat + 8 ≤ vfile.toNat ∨ vfile.toNat + 24 ≤ vfmt.toNat)
    (hsplo : 0x8001c000 ≤ vsp.toNat)
    (hsphi : vsp.toNat + 592 ≤ 0x100000000)
    (hspal : vsp.toNat % 8 = 0)
    (hdge : 0x8001b900 ≤ d.toNat)
    (hdhi : d.toNat + 21 ≤ 0x100000000)
    (hdstk : vsp.toNat + 592 ≤ d.toNat ∨ d.toNat + 21 ≤ vsp.toNat - 128)
    (hfiled : vfile.toNat + 24 ≤ d.toNat ∨ d.toNat + 21 ≤ vfile.toNat)
    (hra0align : vra0.toNat % 4 = 0)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
    -- the UTF-8 byte list of the mathematical rendering
    ∃ ubytes : List UInt8,
      ubytes = (intToString (llArg a0 a1 a2 a3 a4b a5b a6 a7).toInt).toUTF8.data.toList ∧
      -- return: PC = ra, sp restored, **a0 = the byte length**
      c'.σ.regs.get? Register.PC = some vra0 ∧
      c'.σ.regs.get? Register.x1 = some vra0 ∧
      c'.σ.regs.get? Register.x2 = some (vsp + (592#64)) ∧
      c'.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 ubytes.length) ∧
      -- callee-saves restored
      c'.σ.regs.get? Register.x8 = some vS0o ∧
      c'.σ.regs.get? Register.x9 = some vS1o ∧
      c'.σ.regs.get? Register.x18 = some vS2o ∧
      c'.σ.regs.get? Register.x19 = some vS3o ∧
      c'.σ.regs.get? Register.x20 = some vS4o ∧
      c'.σ.regs.get? Register.x21 = some vS5o ∧
      c'.σ.regs.get? Register.x22 = some vS6o ∧
      c'.σ.regs.get? Register.x23 = some vS7o ∧
      c'.σ.regs.get? Register.x24 = some vS8o ∧
      c'.σ.regs.get? Register.x25 = some vS9o ∧
      c'.σ.regs.get? Register.x26 = some vS10o ∧
      c'.σ.regs.get? Register.x27 = some vS11o ∧
      -- **the caller buffer = the UTF-8 bytes of `intToString`, byte for byte**
      (∀ (k : Nat) (hk : k < ubytes.length),
        c'.σ.mem[d.toNat + k]? = some (ubytes[k].toBitVec)) ∧
      -- FILE cursor/capacity updated by the byte length
      Pin8 c'.σ.mem vfile.toNat (d + BitVec.ofNat 64 ubytes.length) ∧
      (∀ a : Nat, ¬(vsp.toNat - 88 ≤ a ∧ a < vsp.toNat + 592) →
        ¬(d.toNat ≤ a ∧ a < d.toNat + ubytes.length) →
        ¬(vfile.toNat ≤ a ∧ a < vfile.toNat + 8) →
        ¬(vfile.toNat + 12 ≤ a ∧ a < vfile.toNat + 16) →
        c'.σ.mem[a]? = c.σ.mem[a]?) ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) := by
  obtain ⟨c', hsteps, hG', n2, bs2, hn2a, hn2b, hub, hlb, hbs2f,
      hpc', hx1', hx2', hx10', h8', h9', h18', h19', h20', h21', h22', h23', h24', h25',
      h26', h27', hsignB, hdigB, hcurP, hcapP, hframe, htk', hmi'⟩ :=
    svfprintf_lld_spec vsp vra0 va0 vfile vfmt vva d
      vS0o vS1o vS2o vS3o vS4o vS5o vS6o vS7o vS8o vS9o vS10o vS11o
      fl0 fl1 cap32 a0 a1 a2 a3 a4b a5b a6 a7 c hG
      hsl0 hsl20 hlc0 hstr0 hms0 hlm0 hamb0 hum0 hud0 hfp0 hap0 hslot0 hsspL0 hsspuL0 hmvL0
      hpc hx2 hx1 hx3 hx10 hx11 hx12 hx13 hx8 hx9 hx22 hx18 hx19 hx20 hx21 hx23 hx24
      hx25 hx26 hx27
      hdp0 hdp1 hdp2 hdp3 hdp4 hdp5 hdp6 hdp7
      hdb0 hdb1 hdb2 hdb3 hdb4 hdb5 hdb6 hdb7
      hfn0 hfn1 hfn2 hfn3 hfn4 hfn5 hfn6 hfn7 hmbB htb0 htb1 htb2 htb3
      hfmt0 hfmt1 hfmt2 hfmt3 hfmt4 hfl0B hfl1B hflagB hflag40
      hsinkcur hsinkcap hcap21 hcap31
      ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 hvlo hvhiram hvhtif hvalign hvdisj
      hneg
      hfilelo hfilehi hfileal hflo hfhi hfhtif hfstk hfd hfpp hsplo hsphi hspal
      hdge hdhi hdstk hfiled hra0align htick
  -- the byte-for-byte identity, in Spec38's vocabulary
  have hbytes : signByte :: (List.range n2).map bs2
      = (intToString (llArg a0 a1 a2 a3 a4b a5b a6 a7).toInt).toUTF8.data.toList.map
          (fun u => u.toBitVec) :=
    svfprintf_buffer_eq_intToString _ n2 bs2 hneg hn2a hbs2f hub hlb
  -- lengths: |ubytes| = 1 + n2
  have hlen : (intToString (llArg a0 a1 a2 a3 a4b a5b a6 a7).toInt).toUTF8.data.toList.length
      = 1 + n2 := by
    have h := congrArg List.length hbytes
    rw [List.length_cons, List.length_map, List.length_range, List.length_map] at h
    omega
  refine ⟨c', hsteps, hG',
    (intToString (llArg a0 a1 a2 a3 a4b a5b a6 a7).toInt).toUTF8.data.toList, rfl,
    hpc', hx1', hx2', (by rw [hlen]; exact hx10'),
    h8', h9', h18', h19', h20', h21', h22', h23', h24', h25', h26', h27',
    ?_, (by rw [hlen]; exact hcurP), ?_, htk', hmi'⟩
  · -- byte-for-byte in the caller buffer
    intro k hk
    have hk' : k < 1 + n2 := by rwa [hlen] at hk
    -- ubytes[k].toBitVec = (signByte :: map bs2)[k]
    have hget : (intToString (llArg a0 a1 a2 a3 a4b a5b a6 a7).toInt).toUTF8.data.toList[k].toBitVec
        = (signByte :: (List.range n2).map bs2)[k]'(by
            rw [List.length_cons, List.length_map, List.length_range]; omega) := by
      have hmapg : ((intToString (llArg a0 a1 a2 a3 a4b a5b a6 a7).toInt).toUTF8.data.toList.map
          (fun u => u.toBitVec))[k]'(by rw [List.length_map, hlen]; omega)
          = (intToString (llArg a0 a1 a2 a3 a4b a5b a6 a7).toInt).toUTF8.data.toList[k].toBitVec :=
        List.getElem_map _
      rw [← hmapg]
      exact List.getElem_of_eq hbytes.symm _
    rw [hget]
    cases k with
    | zero =>
      simpa using hsignB
    | succ j =>
      have hj : j < n2 := by omega
      have : (signByte :: (List.range n2).map bs2)[j + 1]'(by simp; omega)
          = bs2 j := by
        simp [List.getElem_map, List.getElem_range]
      rw [this, show d.toNat + (j + 1) = d.toNat + 1 + j from by omega]
      exact hdigB j hj
  · -- the frame, re-based to the byte length
    intro a hW1 hW2 hW3 hW4
    exact hframe a hW1 (by rw [hlen] at hW2; omega) hW3 hW4

end Vsa.Sim
