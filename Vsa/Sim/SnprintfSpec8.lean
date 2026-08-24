import Vsa.Sim.SnprintfSpec7

/-!
# M3 Layer-3 — `SnprintfSpec8` : sign block → PRINT entry, composed (`_ep`)

This module glues the two already-verified halves of the negative-`%lld`
digit-formatting path into a **single** `Triple` covering the executed footprint

  `[0x800080e4, 0x8000782c)`   (sign block → split → loop entry → decimal loop
                                → exit restore → three hops → PRINT entry)

for the negative case (`v < 0`, magnitude `> 9`):

* `signToDigits_neg_spec` (`SnprintfSpec6`) : `0x800080e4 → 0x80008358`, emitting
  the complete decimal digit buffer and leaving the `'-'` sign byte at `sp+167`;
* `exitToPrint_spec` (`SnprintfSpec7`) : `0x80008358 → 0x8000782c`, the restore
  block (five spill reloads, `len = top − cursor`, width test, the sign-byte
  read-back into `t5`, `a6 := len+1`) and the three hops.

The composition is a `Steps.trans`.  Two of `exitToPrint_spec`'s hypotheses are
**discharged here from what `signToDigits_neg_spec` already delivers**:

* `hsb`  — the sign byte at `sp+167` : this is literally
  `signToDigits_neg_spec`'s last post-conjunct, with `sb := '-'`;
* `hsbne` — the sign byte is non-zero : `'-' = 0x2d ≠ 0`, closed by `decide`.

The remaining `exitToPrint_spec` hypotheses (`x2/x26/x20/x23`, the six
`SlotHolds`, and the width test `hwlt`) are the loop-carried spill/cursor facts
that the digit loop preserves but does not yet *surface* in
`signToDigits_neg_spec`'s postcondition (the wiring gap tracked as "part 2b
item 1").  They are carried here as an explicit hypothesis bundle
(`hExit`) about the exit configuration, so this lemma reduces the whole
`[0x800080e4, 0x8000782c)` obligation to exactly that spill-threading task —
without touching, or re-deriving, any of the green machinery below it.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (__hidden___udivdi3Loaded SvfprintfSliceLoaded FlushPinsLoaded)

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- The `'-'` sign byte `signToDigits_neg_spec` leaves at `sp+167`. -/
abbrev signByte : BitVec 8 := stData 1 ((0#64) + sign_extend (m := 64) (0x02d#12))

/-- The sign byte is non-zero: `'-' = 0x2d ≠ 0`. -/
theorem signByte_ne_zero :
    ((zero_extend (m := 64) signByte : BitVec 64) == (0#64)) = false := by decide

/-- `extractLsb 31 0` of a 64-bit value that already fits in 32 bits just returns
its low 32 bits (`= ofNat 32 x.toNat`). -/
theorem extractLsb32_of_lt (x : BitVec 64) (hx : x.toNat < 2 ^ 32) :
    Sail.BitVec.extractLsb x 31 0 = BitVec.ofNat 32 x.toNat := by
  show x.extractLsb 31 0 = BitVec.ofNat 32 x.toNat
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat (31 - 0 + 1) (x.toNat >>> 0)).toNat = (BitVec.ofNat 32 x.toNat).toNat
  simp only [Nat.shiftRight_zero, BitVec.toNat_ofNat]

/-- **The digit-count length lemma.**  At the loop exit the buffer top is
`entryTop vsp = vsp+348` and the descending cursor is `ofNat (top-1-p)`, so the
32-bit `subw`-computed length, sign-extended, is exactly `p+1` (the digit count).
Both operands fit in 32 bits (`vsp.toNat+356 ≤ 2^32`) and `p+1 ≤ 20 < 2^31`, so
the truncating subtraction and the sign extension are transparent. -/
theorem len_eq_p1 (vsp : BitVec 64) (p : Nat)
    (hhi : vsp.toNat + 356 ≤ 0x100000000) (hp : p + 1 ≤ 20) :
    (sign_extend (m := 64)
      ((Sail.BitVec.extractLsb (entryTop vsp) 31 0)
        - (Sail.BitVec.extractLsb (BitVec.ofNat 64 ((entryTop vsp).toNat - 1 - p)) 31 0)))
      = BitVec.ofNat 64 (p + 1) := by
  have hnw : vsp.toNat + 348 < 2 ^ 64 := by omega
  -- top = vsp+348, both operands are < 2^32
  have htop_toNat : (entryTop vsp).toNat = vsp.toNat + 348 :=
    addoff_toNat_sn5 vsp (0x15c#12) 348 (by omega) (by decide) hnw
  have htop_lt : (entryTop vsp).toNat < 2 ^ 32 := by rw [htop_toNat]; omega
  have hcur_toNat : (BitVec.ofNat 64 ((entryTop vsp).toNat - 1 - p)).toNat
      = (entryTop vsp).toNat - 1 - p := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [htop_toNat]; omega)]
  have hcur_lt : (BitVec.ofNat 64 ((entryTop vsp).toNat - 1 - p)).toNat < 2 ^ 32 := by
    rw [hcur_toNat, htop_toNat]; omega
  -- slice both to 32-bit `ofNat`s
  rw [extractLsb32_of_lt _ htop_lt, extractLsb32_of_lt _ hcur_lt, hcur_toNat]
  -- the 32-bit difference has toNat = p+1
  have hsub : (BitVec.ofNat 32 (entryTop vsp).toNat
      - BitVec.ofNat 32 ((entryTop vsp).toNat - 1 - p)).toNat = p + 1 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt htop_lt, Nat.mod_eq_of_lt (show (entryTop vsp).toNat - 1 - p < 2 ^ 32 by rw [htop_toNat]; omega)]
    -- 2^32 + (top-1-p) is the additive so the subtraction is exact mod 2^32
    rw [show (2:Nat) ^ 32 - ((entryTop vsp).toNat - 1 - p) + (entryTop vsp).toNat
          = 2 ^ 32 + (p + 1) from by rw [htop_toNat]; omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  -- the difference equals `ofNat 32 (p+1)`
  have hdiff : (BitVec.ofNat 32 (entryTop vsp).toNat
      - BitVec.ofNat 32 ((entryTop vsp).toNat - 1 - p)) = BitVec.ofNat 32 (p + 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hdiff]
  -- sign-extend `ofNat 32 (p+1)` (msb clear since p+1 < 2^31) = ofNat 64 (p+1)
  apply BitVec.eq_of_toNat_eq
  show ((BitVec.ofNat 32 (p + 1)).signExtend 64).toNat = (BitVec.ofNat 64 (p + 1)).toNat
  rw [BitVec.toNat_signExtend]
  have hmsb : (BitVec.ofNat 32 (p + 1)).msb = false := by
    rw [BitVec.msb_eq_getLsbD_last]
    simp only [BitVec.getLsbD_ofNat]
    rw [Nat.testBit_lt_two_pow (by omega)]
    rfl
  rw [hmsb, if_neg (by simp), Nat.add_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]

/-- **Composed sign-block → PRINT-entry `Triple` for the negative case.**

From `0x800080e4` (value negative, magnitude `> 9`) to `0x8000782c` (the PRINT
entry), one `Steps` chain covering the full `[0x800080e4, 0x8000782c)` executed
footprint.  The digit buffer is complete (`BufInv`), the `'-'` byte has been read
back into `t5 = x30` and `a6 = x16 = len+1` carries the sign-inclusive length.

All of `exitToPrint_spec`'s spill/cursor/register/`Loaded` preconditions are now
**discharged from `signToDigits_neg_spec`'s (strengthened) postcondition** — the
six `SlotHolds`, `x2`/`x20`/`x23`/`x26`, `SvfprintfSliceLoaded` and
`FlushPinsLoaded` are threaded through the entry frames (`EntryFrame`), the digit
loop (`DigitFrame` + the `NotWrittenL` register frame) and the sign block.

The **only** residual is the field-width comparison `hwlt` (`bge s4,s6` not
taken, i.e. `width < len`).  Its comparand is the spilled width in slot 56, a
value produced by the earlier `%`-format parse phase (`svfprintf`'s width
accumulator), which is upstream of this segment and not yet formalised.  It is
supplied as `hwidth`, a hypothesis about *whatever* width the parse left in
slot 56 at the loop exit — reducing the whole `[0x800080e4, 0x8000782c)`
obligation to exactly that one parse-phase fact. -/
theorem entryToPrint_neg_spec
    (v vsp vt1 v8 v20 v23 v28 v12 : BitVec 64)
    (c : Config)
    (hG : GoodState c.σ)
    (hload : SvfprintfSliceLoaded c.σ.mem)
    (huload : Vsa.Sim.Code.__umoddi3Loaded c.σ.mem)
    (hcuload : __hidden___udivdi3Loaded c.σ.mem)
    (hfp : Vsa.Sim.Code.FlushPinsLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x800080e4#64))
    (hx13 : c.σ.regs.get? Register.x13 = some v)
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx6 : c.σ.regs.get? Register.x6 = some vt1)
    (hx8 : c.σ.regs.get? Register.x8 = some v8)
    (hx20 : c.σ.regs.get? Register.x20 = some v20)
    (hx23 : c.σ.regs.get? Register.x23 = some v23)
    (hx28 : c.σ.regs.get? Register.x28 = some v28)
    (hx12 : c.σ.regs.get? Register.x12 = some v12)
    (hflag : vt1 &&& sign_extend (m := 64) (0x400#12) = 0#64)
    (hneg : zopz0zKzJ_s v (0#64) = false)
    (hmag : 9 < ((0#64) - v).toNat)
    (htlo : tohostAddr + 16 + 64 ≤ vsp.toNat)
    (hhi : vsp.toNat + 356 ≤ 0x100000000)
    (halign : vsp.toNat % 8 = 0)
    (htick : c.tick < 2)
    -- The **sole residual** — a single arithmetic fact about the *parsed field
    -- width* `v20` (the `x20` value on entry to `0x800080e4`, which the earlier
    -- `%`-format parse phase produced and which this segment carries untouched into
    -- spill slot 56): for the digit count `p+1` the loop emits (`p` characterised
    -- by the exit division `((0#64)-v).toNat / 10^p ≤ 9`, bounded `p+1 ≤ 20`), the
    -- parsed width is strictly less than the length, so `bge s4,s6` is not taken.
    -- For the `%lld` default (no width field) the parse leaves `v20 = 0 < p+1`;
    -- proving that in general requires the parse-phase specification, which is
    -- upstream of `0x800080e4` and not yet formalised (see report).
    (hwidth : ∀ (p : Nat), ((0#64) - v).toNat / 10 ^ p ≤ 9 → p + 1 ≤ 20 →
        v20.toInt < (p + 1 : Int)) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x8000782c#64) ∧
      -- the sign byte read back into `t5`
      c'.σ.regs.get? Register.x30 = some (zero_extend (m := 64) signByte) ∧
      c'.σ.regs.get? Register.x31 = some (0#64) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      -- the magnitude bridge (INT64_MIN-safe): the loop formatted `|v|`
      ((0#64) - v).toNat = (- v.toInt).toNat ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) := by
  -- === 1. sign block → split → loop entry → decimal loop → exit at 0x80008358 ===
  -- (with all spill/cursor/register/Loaded facts surfaced; slot 56 = the *named*
  -- parsed field width `v20` via `hs56v20`, digit-count bound `hpb : p+1 ≤ 20`)
  obtain ⟨c3, hs13, p, hexit, hpb, hpc3, hx23_3, hbuf3, hG3, htick3, hmi3, hbridge, hsign3,
    hload3, hfp3, hx2_3, ⟨vs4j, hx20_3⟩, hx26_3, hs56v20,
    vwid, vflg, vt3, vs7, vs0, hs112_3, hs56_3, hs40_3, hs32_3, hs48_3, hs120_3⟩ :=
    signToDigits_neg_spec v vsp vt1 v8 v20 v23 v28 v12 c
      hG hload hfp huload hcuload hpc hx13 hx2 hx6 hx8 hx20 hx23 hx28 hx12
      hflag hneg hmag htlo hhi halign htick
  -- the sign byte is the concrete `'-'`, hence non-zero
  have hsbne : ((zero_extend (m := 64) signByte : BitVec 64) == (0#64)) = false :=
    signByte_ne_zero
  -- the length `len = top − cur`, sign-extended, is exactly the digit count `p+1`
  have hlen : (sign_extend (m := 64)
      ((Sail.BitVec.extractLsb (entryTop vsp) 31 0)
        - (Sail.BitVec.extractLsb (BitVec.ofNat 64 ((entryTop vsp).toNat - 1 - p)) 31 0)))
      = BitVec.ofNat 64 (p + 1) := len_eq_p1 vsp p hhi hpb
  -- `(ofNat 64 (p+1)).toInt = p+1` (since `p+1 ≤ 20 < 2^63`)
  have hp1_toInt : (BitVec.ofNat 64 (p + 1)).toInt = (p + 1 : Int) := by
    have hlt : 2 * (BitVec.ofNat 64 (p + 1)).toNat < 2 ^ 64 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    rw [BitVec.toInt_eq_toNat_of_lt hlt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp
  -- The width test now concerns the *named* parsed width `v20` (slot 56 holds `v20`
  -- via `hs56v20`), and `hwidth` gives `v20.toInt < p+1 = len.toInt`, so `bge` is
  -- not taken.  This is the single arithmetic residual on the parse phase.
  have hwlt_3 : zopz0zKzJ_s v20 (sign_extend (m := 64)
      ((Sail.BitVec.extractLsb (entryTop vsp) 31 0)
        - (Sail.BitVec.extractLsb (BitVec.ofNat 64 ((entryTop vsp).toNat - 1 - p)) 31 0))) = false := by
    have hlt := hwidth p hexit hpb
    unfold zopz0zKzJ_s
    rw [hlen, hp1_toInt]
    exact decide_eq_false (by omega)
  -- === 2. restore block + hops : 0x80008358 → 0x8000782c ===
  obtain ⟨c', hs37, hG', hpc', hx22', hx16', hx30', hx31', hx20', hx6', hx28',
          hx23', hx8', hx2', htick', hmi'⟩ :=
    exitToPrint_spec vsp (entryTop vsp) v20 vflg vt3 vs7 vs0
      (BitVec.ofNat 64 ((entryTop vsp).toNat - 1 - p)) vs4j (BitVec.ofNat 64 (p + 1)) signByte c3
      hG3 hload3 hfp3 hpc3 hx2_3 hx26_3 hx20_3 hx23_3
      hs112_3 hs56v20 hs40_3 hs32_3 hs48_3 hs120_3
      hsign3 hsbne hwlt_3 htlo hhi halign htick3
  exact ⟨c', hs13.trans hs37, hG', hpc', hx30', hx31', hx2', hbridge, htick', hmi'⟩

/-- The parser's default-width sentinel is signed `-1`, hence below every
positive decimal digit count. -/
theorem default_width_lt_digits (p : Nat) :
    (((0#64) - (0x1#64)).toInt < (p + 1 : Int)) := by
  have h : (((0#64) - (0x1#64)).toInt : Int) = -1 := by decide
  rw [h]
  omega

/-- The negative `%lld` path with the default field width established by
`parseInit_spec`. -/
theorem entryToPrint_neg_default_width_spec
    (v vsp vt1 v8 v23 v28 v12 : BitVec 64)
    (c : Config)
    (hG : GoodState c.σ)
    (hload : SvfprintfSliceLoaded c.σ.mem)
    (huload : Vsa.Sim.Code.__umoddi3Loaded c.σ.mem)
    (hcuload : __hidden___udivdi3Loaded c.σ.mem)
    (hfp : Vsa.Sim.Code.FlushPinsLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x800080e4#64))
    (hx13 : c.σ.regs.get? Register.x13 = some v)
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx6 : c.σ.regs.get? Register.x6 = some vt1)
    (hx8 : c.σ.regs.get? Register.x8 = some v8)
    (hx20 : c.σ.regs.get? Register.x20 = some ((0#64) - (0x1#64)))
    (hx23 : c.σ.regs.get? Register.x23 = some v23)
    (hx28 : c.σ.regs.get? Register.x28 = some v28)
    (hx12 : c.σ.regs.get? Register.x12 = some v12)
    (hflag : vt1 &&& sign_extend (m := 64) (0x400#12) = 0#64)
    (hneg : zopz0zKzJ_s v (0#64) = false)
    (hmag : 9 < ((0#64) - v).toNat)
    (htlo : tohostAddr + 16 + 64 ≤ vsp.toNat)
    (hhi : vsp.toNat + 356 ≤ 0x100000000)
    (halign : vsp.toNat % 8 = 0)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x8000782c#64) ∧
      c'.σ.regs.get? Register.x30 = some (zero_extend (m := 64) signByte) ∧
      c'.σ.regs.get? Register.x31 = some (0#64) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      ((0#64) - v).toNat = (- v.toInt).toNat ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) := by
  exact entryToPrint_neg_spec v vsp vt1 v8 ((0#64) - (0x1#64)) v23 v28 v12 c
    hG hload huload hcuload hfp hpc hx13 hx2 hx6 hx8 hx20 hx23 hx28 hx12
    hflag hneg hmag htlo hhi halign htick
    (fun p _ _ => default_width_lt_digits p)

end Vsa.Sim
