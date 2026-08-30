import Vsa.Sim.SnprintfSpec13
import Vsa.Sim.DecodeTable.Batch16Part11
import Vsa.Sim.DecodeTable.Batch08Part03
import Vsa.Sim.DecodeTable.Batch06Part25
import Vsa.Sim.DecodeTable.Batch06Part14
import Vsa.Sim.DecodeTable.Batch05Part30
import Vsa.Sim.DecodeTable.Batch02Part31
import Vsa.Sim.DecodeTable.Batch02Part12
import Vsa.Sim.ObsAvoid

/-!
# M3 Layer-3 — `SnprintfSpec14` : `%`-format jump-table **slot-address arithmetic** + full dispatch (`_da`)

`SnprintfSpec13.parseDispatchHop_spec` verifies the *load-and-transfer* tail of the
`svfprintf` conversion dispatch (`0x800077b4 → handler`), but takes as a *given*
that the slot address `base + 4*k` is already sitting in `x15`.  This module
supplies the missing **upstream slot-address arithmetic** — the `sext.w`/`addiw`/
`bltu`/`slli`/`srli`/`add` sequence at `[0x80007798, 0x800077b4)` that turns the
conversion **character** (in `s8 = x24`) into that slot address — and composes it
with `parseDispatchHop_spec` to obtain a single `Steps` chain from the dispatch
loop head `0x80007798` **through the jump table** to the conversion handler entry.

## Executed footprint `[0x80007798, 0x800077bc]` (the dispatch block)

```
  7798: addi  s9,s9,1        s9  += 1                 (loop-counter bump, dead here)
  779c: sext.w s8,s8         s8  := sext32(s8)        (char, canonicalized)
  77a0: addiw a5,s8,-32      a5  := sext32(char-32)   (jump-table index k = ch-32)
  77a4: bltu  s10,a5,+..     if 90 < k goto out-of-range   ← NOT taken (k ≤ 90)
  77a8: slli  a4,a5,0x20     a4  := a5 <<< 32
  77ac: srli  a5,a4,0x1e     a5  := a4 >>> 30 = 4*k   ← the (k<<32)>>30 = 4*k trick
  77b0: add   a5,a5,s6       a5  := base + 4*k        (the slot address)
  --> 77b4  (parseDispatchHop_spec: lw / add / jr → handler)
```

The load-bearing bitvector fact is `slotIndexShift`:
`((ofNat 64 k) <<< 32) >>> 30 = ofNat 64 (4*k)` for `k < 2^30` — i.e. the machine
`srli (slli a5 0x20) 0x1e` computes `4*k` exactly (the compiler's byte-scaled
table index, since each `.rodata` slot is a 4-byte signed offset).

## Register preconditions (honest, from the parse loop upstream)

The dispatch block reads four live registers set by the (still-unformalized)
`%`-parse scan loop just before `0x80007798`:

* `x24 (s8)` — the **conversion character** `ch` (for the `%lld` path, `'l' = 0x6c`);
* `x26 (s10)` — the dispatch **upper bound** `90` (`'Z'`), set by `parseInit_spec`;
* `x22 (s6)` — the jump-**table base** `0x8001a0fc = parseTableBase`, set by
  `parseInit_spec` (its `auipc`/`addi` pair);
* `x25 (s9)` — the loop counter (read + bumped at `0x80007798`; its value is
  irrelevant to the dispatch and left existential).

`parseInit_spec` (`SnprintfSpec12`) *establishes* `x22 = parseTableBase`,
`x26 = 90`, and `x24 = zext(format[1])` at its exit `0x80007798`, but its stated
postcondition currently surfaces only `x2/x20/x6`.  Chaining `parseInit → this`
end-to-end therefore requires widening `parseInit_spec`'s post to additionally
surface `x22`, `x24`, `x26` (and, for the concrete `%lld` path, pinning
`format[1] = 'l'` so `x24 = ofNat 0x6c`).  That widening is mechanical (three more
`obs_alu_other` threads per step) but is left to a follow-up; this module states
the three register facts as explicit entry hypotheses and documents their origin.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (SvfprintfSliceLoaded)

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## The reusable slot-index bitvector lemma `slotIndexShift`

`srli (slli a5 0x20) 0x1e = 4*a5` when the index fits in 30 bits.  Concretely,
`((ofNat 64 k) <<< 32) >>> 30 = ofNat 64 (4*k)` for `k < 2^30`.  This is the exact
arithmetic the compiler emits to scale a jump-table index into a byte offset
(4-byte slots): shift left 32 then right 30 nets a left-shift by 2 (`×4`) *after*
zeroing the high 32 bits, so it works for any 32-bit-clean index.  Reused by every
`.rodata` jump-table dispatch (parse, `eval_expr`, `value_equal`). -/
theorem slotIndexShift (k : Nat) (hk : k < 2 ^ 30) :
    ((BitVec.ofNat 64 k) <<< (32#6)) >>> (30#6) = BitVec.ofNat 64 (4 * k) := by
  -- `<<< (bv6)` / `>>> (bv6)` are `<<< (bv6).toNat` / `>>> (bv6).toNat` by defn
  show (((BitVec.ofNat 64 k) <<< (32#6).toNat) >>> (30#6).toNat) = BitVec.ofNat 64 (4 * k)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft]
  simp only [BitVec.toNat_ofNat]
  show ((k % 2 ^ 64) <<< 32 % 2 ^ 64) >>> 30 = 4 * k % 2 ^ 64
  rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have hklt : k < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hklt]
  have hprod : k * 2 ^ 32 < 2 ^ 64 := by
    have hstep : k * 2 ^ 32 < 2 ^ 30 * 2 ^ 32 :=
      (Nat.mul_lt_mul_right (show 0 < 2 ^ 32 by decide)).mpr hk
    have e : (2 : Nat) ^ 30 * 2 ^ 32 = 2 ^ 62 := by decide
    omega
  rw [Nat.mod_eq_of_lt hprod]
  have h4 : 4 * k < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt h4]
  have hdiv : k * 2 ^ 32 / 2 ^ 30 = k * (2 ^ 32 / 2 ^ 30) := by
    rw [Nat.mul_div_assoc]; exact ⟨2 ^ 2, by decide⟩
  rw [hdiv]
  have e2 : (2 : Nat) ^ 32 / 2 ^ 30 = 4 := by decide
  rw [e2]; omega

/-! ## `parseDispatchArith_l_spec` — slot-address arithmetic for `'l'`

`0x80007798 → 0x800077b4`: from the dispatch loop head with the character `'l'`
(`0x6c`) in `x24`, table base in `x22`, and upper bound `90` in `x26`, run the
`sext.w`/`addiw`/`bltu`(not-taken)/`slli`/`srli`/`add` block, landing at the slot
load `0x800077b4` with `x15 = ofNat(parseTableBase + 4*(0x6c-32))` — exactly the
entry `parseDispatchHop_spec` requires. -/
theorem parseDispatchArith_l_spec
    (vsp vs9 v6 v20 v27 : BitVec 64) (c : Config)
    (hG : GoodState c.σ)
    (hload : SvfprintfSliceLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x80007798#64))
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    -- s8 = the conversion character 'l' = 0x6c
    (hx24 : c.σ.regs.get? Register.x24 = some (BitVec.ofNat 64 0x6c))
    -- s10 = 90 (dispatch upper bound, from parseInit)
    (hx26 : c.σ.regs.get? Register.x26 = some (BitVec.ofNat 64 90))
    -- s6 = jump-table base (from parseInit's auipc/addi)
    (hx22 : c.σ.regs.get? Register.x22 = some (BitVec.ofNat 64 parseTableBase))
    -- s9 = loop counter (read+bumped; final value = vs9+1)
    (hx25 : c.σ.regs.get? Register.x25 = some vs9)
    -- x6/x20/x27 (t1 ll-flag / a4 width / s11) threaded unchanged through the block
    (hx6 : c.σ.regs.get? Register.x6 = some v6)
    (hx20 : c.σ.regs.get? Register.x20 = some v20)
    (hx27 : c.σ.regs.get? Register.x27 = some v27)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x800077b4#64) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.σ.regs.get? Register.x15
        = some (BitVec.ofNat 64 (parseTableBase + 4 * (0x6c - 32))) ∧
      c'.σ.regs.get? Register.x22 = some (BitVec.ofNat 64 parseTableBase) ∧
      c'.σ.regs.get? Register.x6 = some v6 ∧
      c'.σ.regs.get? Register.x20 = some v20 ∧
      c'.σ.regs.get? Register.x25 = some (vs9 + sign_extend (m := 64) (0x001#12)) ∧
      c'.σ.regs.get? Register.x27 = some v27 ∧
      c'.σ.mem = c.σ.mem ∧
      c'.tick < 2 := by
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
  -- === 7798: addi s9,s9,1  ⇒  x25 := vs9 + 1  (dead) ===
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80007798 hload
  have hx25n1 : (afterNextPC (afterPrelude c.σ) (0x80007798#64)).regs.get? Register.x25 = some vs9 := by
    rw [get?_afterNextPC c.σ (0x80007798#64) _ (by decide) (by decide)]; exact hx25
  obtain ⟨σ1, i1, hs1s, hi1, hG1, hmem1, hobs1⟩ :=
    stepObs_alu c.σ c.tick c.steps (0x80007798#64) vmi0 (0x001c8c93#32)
      (instruction.ITYPE (0x001#12, regidx.Regidx 0x19#5, regidx.Regidx 0x19#5, iop.ADDI))
      Register.x25 (vs9 + sign_extend (m := 64) (0x001#12))
      (0x93#8) (0x8c#8) (0x1c#8) (0x00#8)
      hG hpc hmi0 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_001c8c93 (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (execute_itype_addi_char (0x001#12) (regidx.Regidx 0x19#5) (regidx.Regidx 0x19#5) vs9
        (afterNextPC (afterPrelude c.σ) (0x80007798#64))
        (sigma3_alu c.σ (0x80007798#64) Register.x25 (vs9 + sign_extend (m := 64) (0x001#12)))
        (rX_bits_x25 _ vs9 hx25n1) (wX_bits_x25 _ (vs9 + sign_extend (m := 64) (0x001#12))))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1s
  have hpc1 : σ1.regs.get? Register.PC = some (0x8000779c#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x80007798#64 : BitVec 64) 4 = (0x8000779c#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hx2_1 : σ1.regs.get? Register.x2 = some vsp :=
    obs_alu_other' hobs1 Register.x2 (by decide) hx2
  have hx24_1 : σ1.regs.get? Register.x24 = some (BitVec.ofNat 64 0x6c) :=
    obs_alu_other' hobs1 Register.x24 (by decide) hx24
  have hx26_1 : σ1.regs.get? Register.x26 = some (BitVec.ofNat 64 90) :=
    obs_alu_other' hobs1 Register.x26 (by decide) hx26
  have hx22_1 : σ1.regs.get? Register.x22 = some (BitVec.ofNat 64 parseTableBase) :=
    obs_alu_other' hobs1 Register.x22 (by decide) hx22
  have hx25_1 : σ1.regs.get? Register.x25 = some (vs9 + sign_extend (m := 64) (0x001#12)) :=
    obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx6_1 : σ1.regs.get? Register.x6 = some v6 :=
    obs_alu_other' hobs1 Register.x6 (by decide) hx6
  have hx20_1 : σ1.regs.get? Register.x20 = some v20 :=
    obs_alu_other' hobs1 Register.x20 (by decide) hx20
  have hx27_1 : σ1.regs.get? Register.x27 = some v27 :=
    obs_alu_other' hobs1 Register.x27 (by decide) hx27
  have hload1 : SvfprintfSliceLoaded σ1.mem := hmem1 ▸ hload
  -- === 779c: sext.w s8,s8  ⇒  x24 := sext32(extractLsb (0x6c + 0) 31 0) = 0x6c ===
  obtain ⟨hc0, hc1, hc2, hc3⟩ := Vsa.Sim.Code.svfprintfSlice_at_8000779c hload1
  have hx24n2 : (afterNextPC (afterPrelude σ1) (0x8000779c#64)).regs.get? Register.x24
      = some (BitVec.ofNat 64 0x6c) := by
    rw [get?_afterNextPC σ1 (0x8000779c#64) _ (by decide) (by decide)]; exact hx24_1
  obtain ⟨σ2, i2, hs2s, hi2, hG2, hmem2, hobs2⟩ :=
    stepObs_alu σ1 i1 (c.steps + 1) (0x8000779c#64) vmi1 (0x000c0c1b#32)
      (instruction.ADDIW (0x000#12, regidx.Regidx 0x18#5, regidx.Regidx 0x18#5))
      Register.x24
      (sign_extend (m := 64)
        (Sail.BitVec.extractLsb ((BitVec.ofNat 64 0x6c) + sign_extend (m := 64) (0x000#12)) 31 0))
      (0x1b#8) (0x0c#8) (0x0c#8) (0x00#8)
      hG1 hpc1 hmi1 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_000c0c1b (afterPrelude σ1)
        (by rw [get?_afterPrelude σ1 _ (by decide)]; exact hG1.misa)
        (by rw [get?_afterPrelude σ1 _ (by decide)]; exact hG1.cur_privilege)
        (by rw [get?_afterPrelude σ1 _ (by decide)]; exact hG1.mseccfg))
      (execute_addiw_char (0x000#12) (regidx.Regidx 0x18#5) (regidx.Regidx 0x18#5)
        (BitVec.ofNat 64 0x6c) (afterNextPC (afterPrelude σ1) (0x8000779c#64))
        (sigma3_alu σ1 (0x8000779c#64) Register.x24
          (sign_extend (m := 64)
            (Sail.BitVec.extractLsb ((BitVec.ofNat 64 0x6c) + sign_extend (m := 64) (0x000#12)) 31 0)))
        (rX_bits_x24 _ (BitVec.ofNat 64 0x6c) hx24n2)
        (wX_bits_x24 _ _))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hc0 hc1 hc2 hc3 (by decide) (by decide) (by decide) hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2s
  have hpc2 : σ2.regs.get? Register.PC = some (0x800077a0#64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x8000779c#64 : BitVec 64) 4 = (0x800077a0#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hx24_2 : σ2.regs.get? Register.x24 = some (BitVec.ofNat 64 0x6c) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (sign_extend (m := 64)
        (Sail.BitVec.extractLsb ((BitVec.ofNat 64 0x6c) + sign_extend (m := 64) (0x000#12)) 31 0))
        = BitVec.ofNat 64 0x6c from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hx2_2 : σ2.regs.get? Register.x2 = some vsp :=
    obs_alu_other' hobs2 Register.x2 (by decide) hx2_1
  have hx26_2 : σ2.regs.get? Register.x26 = some (BitVec.ofNat 64 90) :=
    obs_alu_other' hobs2 Register.x26 (by decide) hx26_1
  have hx22_2 : σ2.regs.get? Register.x22 = some (BitVec.ofNat 64 parseTableBase) :=
    obs_alu_other' hobs2 Register.x22 (by decide) hx22_1
  have hx25_2 : σ2.regs.get? Register.x25 = some (vs9 + sign_extend (m := 64) (0x001#12)) :=
    obs_alu_other' hobs2 Register.x25 (by decide) hx25_1
  have hx6_2 : σ2.regs.get? Register.x6 = some v6 :=
    obs_alu_other' hobs2 Register.x6 (by decide) hx6_1
  have hx20_2 : σ2.regs.get? Register.x20 = some v20 :=
    obs_alu_other' hobs2 Register.x20 (by decide) hx20_1
  have hx27_2 : σ2.regs.get? Register.x27 = some v27 :=
    obs_alu_other' hobs2 Register.x27 (by decide) hx27_1
  have hload2 : SvfprintfSliceLoaded σ2.mem := hmem2 ▸ hload1
  -- === 77a0: addiw a5,s8,-32  ⇒  x15 := sext32(0x6c - 32) = 0x6c-32 = 76 ===
  obtain ⟨hd0, hd1, hd2, hd3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800077a0 hload2
  have hx24n3 : (afterNextPC (afterPrelude σ2) (0x800077a0#64)).regs.get? Register.x24
      = some (BitVec.ofNat 64 0x6c) := by
    rw [get?_afterNextPC σ2 (0x800077a0#64) _ (by decide) (by decide)]; exact hx24_2
  obtain ⟨σ3, i3, hs3s, hi3, hG3, hmem3, hobs3⟩ :=
    stepObs_alu σ2 i2 (c.steps + 1 + 1) (0x800077a0#64) vmi2 (0xfe0c079b#32)
      (instruction.ADDIW (0xfe0#12, regidx.Regidx 0x18#5, regidx.Regidx 0x0f#5))
      Register.x15
      (sign_extend (m := 64)
        (Sail.BitVec.extractLsb ((BitVec.ofNat 64 0x6c) + sign_extend (m := 64) (0xfe0#12)) 31 0))
      (0x9b#8) (0x07#8) (0x0c#8) (0xfe#8)
      hG2 hpc2 hmi2 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_fe0c079b (afterPrelude σ2)
        (by rw [get?_afterPrelude σ2 _ (by decide)]; exact hG2.misa)
        (by rw [get?_afterPrelude σ2 _ (by decide)]; exact hG2.cur_privilege)
        (by rw [get?_afterPrelude σ2 _ (by decide)]; exact hG2.mseccfg))
      (execute_addiw_char (0xfe0#12) (regidx.Regidx 0x18#5) (regidx.Regidx 0x0f#5)
        (BitVec.ofNat 64 0x6c) (afterNextPC (afterPrelude σ2) (0x800077a0#64))
        (sigma3_alu σ2 (0x800077a0#64) Register.x15
          (sign_extend (m := 64)
            (Sail.BitVec.extractLsb ((BitVec.ofNat 64 0x6c) + sign_extend (m := 64) (0xfe0#12)) 31 0)))
        (rX_bits_x24 _ (BitVec.ofNat 64 0x6c) hx24n3)
        (wX_bits_x15 _ _))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hd0 hd1 hd2 hd3 (by decide) (by decide) (by decide) hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3s
  have hpc3 : σ3.regs.get? Register.PC = some (0x800077a4#64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x800077a0#64 : BitVec 64) 4 = (0x800077a4#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hx15_3 : σ3.regs.get? Register.x15 = some (BitVec.ofNat 64 (0x6c - 32)) := by
    have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (sign_extend (m := 64)
        (Sail.BitVec.extractLsb ((BitVec.ofNat 64 0x6c) + sign_extend (m := 64) (0xfe0#12)) 31 0))
        = BitVec.ofNat 64 (0x6c - 32) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hx2_3 : σ3.regs.get? Register.x2 = some vsp :=
    obs_alu_other' hobs3 Register.x2 (by decide) hx2_2
  have hx26_3 : σ3.regs.get? Register.x26 = some (BitVec.ofNat 64 90) :=
    obs_alu_other' hobs3 Register.x26 (by decide) hx26_2
  have hx22_3 : σ3.regs.get? Register.x22 = some (BitVec.ofNat 64 parseTableBase) :=
    obs_alu_other' hobs3 Register.x22 (by decide) hx22_2
  have hx25_3 : σ3.regs.get? Register.x25 = some (vs9 + sign_extend (m := 64) (0x001#12)) :=
    obs_alu_other' hobs3 Register.x25 (by decide) hx25_2
  have hx6_3 : σ3.regs.get? Register.x6 = some v6 :=
    obs_alu_other' hobs3 Register.x6 (by decide) hx6_2
  have hx20_3 : σ3.regs.get? Register.x20 = some v20 :=
    obs_alu_other' hobs3 Register.x20 (by decide) hx20_2
  have hx27_3 : σ3.regs.get? Register.x27 = some v27 :=
    obs_alu_other' hobs3 Register.x27 (by decide) hx27_2
  have hload3 : SvfprintfSliceLoaded σ3.mem := hmem3 ▸ hload2
  -- === 77a4: bltu s10,a5,+..  ⇒  NOT taken (90 not < 76); falls through to 77a8 ===
  obtain ⟨he0, he1, he2, he3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800077a4 hload3
  have hs10r : (rX_bits (regidx.Regidx 0x1a#5)).run (afterNextPC (afterPrelude σ3) (0x800077a4#64))
      = .ok (BitVec.ofNat 64 90) (afterNextPC (afterPrelude σ3) (0x800077a4#64)) := by
    apply rX_bits_x26
    rw [get?_afterNextPC σ3 (0x800077a4#64) _ (by decide) (by decide)]; exact hx26_3
  have ha5r : (rX_bits (regidx.Regidx 0x0f#5)).run (afterNextPC (afterPrelude σ3) (0x800077a4#64))
      = .ok (BitVec.ofNat 64 (0x6c - 32)) (afterNextPC (afterPrelude σ3) (0x800077a4#64)) := by
    apply rX_bits_x15
    rw [get?_afterNextPC σ3 (0x800077a4#64) _ (by decide) (by decide)]; exact hx15_3
  obtain ⟨σ4, i4, hs4s, hi4, hG4, hmem4, hobs4⟩ :=
    stepObs_branch_nottaken σ3 i3 (c.steps + 1 + 1 + 1) (0x800077a4#64) vmi3
      (0x0054#13) (regidx.Regidx 0x1a#5) (regidx.Regidx 0x0f#5) bop.BLTU (0x04fd6a63#32)
      (0x63#8) (0x6a#8) (0xfd#8) (0x04#8)
      hG3 hpc3 hmi3 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_04fd6a63 (afterPrelude σ3)
        (by rw [get?_afterPrelude σ3 _ (by decide)]; exact hG3.misa)
        (by rw [get?_afterPrelude σ3 _ (by decide)]; exact hG3.cur_privilege)
        (by rw [get?_afterPrelude σ3 _ (by decide)]; exact hG3.mseccfg))
      (execute_btype_bltu_nottaken (0x0054#13) (regidx.Regidx 0x1a#5) (regidx.Regidx 0x0f#5)
        (BitVec.ofNat 64 90) (BitVec.ofNat 64 (0x6c - 32))
        (afterNextPC (afterPrelude σ3) (0x800077a4#64)) hs10r ha5r (by decide))
      he0 he1 he2 he3 (by decide) (by decide) (by decide) hi3
  have hstep4 : Step ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ := hs4s
  have hpc4 : σ4.regs.get? Register.PC = some (0x800077a8#64) := by
    have := obs_branch_nottaken_pc hobs4
    rwa [show BitVec.addInt (0x800077a4#64 : BitVec 64) 4 = (0x800077a8#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi4, hmi4⟩ := obs_branch_nottaken_minstret hobs4
  have hx15_4 : σ4.regs.get? Register.x15 = some (BitVec.ofNat 64 (0x6c - 32)) :=
    obs_branch_nottaken_other' hobs4 Register.x15 (by decide) hx15_3
  have hx2_4 : σ4.regs.get? Register.x2 = some vsp :=
    obs_branch_nottaken_other' hobs4 Register.x2 (by decide) hx2_3
  have hx22_4 : σ4.regs.get? Register.x22 = some (BitVec.ofNat 64 parseTableBase) :=
    obs_branch_nottaken_other' hobs4 Register.x22 (by decide) hx22_3
  have hx25_4 : σ4.regs.get? Register.x25 = some (vs9 + sign_extend (m := 64) (0x001#12)) :=
    obs_branch_nottaken_other' hobs4 Register.x25 (by decide) hx25_3
  have hx6_4 : σ4.regs.get? Register.x6 = some v6 :=
    obs_branch_nottaken_other' hobs4 Register.x6 (by decide) hx6_3
  have hx20_4 : σ4.regs.get? Register.x20 = some v20 :=
    obs_branch_nottaken_other' hobs4 Register.x20 (by decide) hx20_3
  have hx27_4 : σ4.regs.get? Register.x27 = some v27 :=
    obs_branch_nottaken_other' hobs4 Register.x27 (by decide) hx27_3
  have hload4 : SvfprintfSliceLoaded σ4.mem := hmem4 ▸ hload3
  -- === 77a8: slli a4,a5,0x20  ⇒  x14 := a5 <<< 32 ===
  obtain ⟨hf0, hf1, hf2, hf3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800077a8 hload4
  have ha5n5 : (rX_bits (regidx.Regidx 0x0f#5)).run (afterNextPC (afterPrelude σ4) (0x800077a8#64))
      = .ok (BitVec.ofNat 64 (0x6c - 32)) (afterNextPC (afterPrelude σ4) (0x800077a8#64)) := by
    apply rX_bits_x15
    rw [get?_afterNextPC σ4 (0x800077a8#64) _ (by decide) (by decide)]; exact hx15_4
  obtain ⟨σ5, i5, hs5s, hi5, hG5, hmem5, hobs5⟩ :=
    stepObs_alu σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x800077a8#64) vmi4 (0x02079713#32)
      (instruction.SHIFTIOP (0x20#6, regidx.Regidx 0x0f#5, regidx.Regidx 0x0e#5, sop.SLLI))
      Register.x14
      (shift_bits_left (BitVec.ofNat 64 (0x6c - 32)) (Sail.BitVec.extractLsb (0x20#6) 5 0))
      (0x13#8) (0x97#8) (0x07#8) (0x02#8)
      hG4 hpc4 hmi4 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_02079713 (afterPrelude σ4)
        (by rw [get?_afterPrelude σ4 _ (by decide)]; exact hG4.misa)
        (by rw [get?_afterPrelude σ4 _ (by decide)]; exact hG4.cur_privilege)
        (by rw [get?_afterPrelude σ4 _ (by decide)]; exact hG4.mseccfg))
      (execute_shiftiop_slli_char (0x20#6) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0e#5)
        (BitVec.ofNat 64 (0x6c - 32)) (afterNextPC (afterPrelude σ4) (0x800077a8#64))
        (sigma3_alu σ4 (0x800077a8#64) Register.x14
          (shift_bits_left (BitVec.ofNat 64 (0x6c - 32)) (Sail.BitVec.extractLsb (0x20#6) 5 0)))
        ha5n5 (wX_bits_x14 _ _))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hf0 hf1 hf2 hf3 (by decide) (by decide) (by decide) hi4
  have hstep5 : Step ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ := hs5s
  have hpc5 : σ5.regs.get? Register.PC = some (0x800077ac#64) := by
    have := obs_alu_pc hobs5
    rwa [show BitVec.addInt (0x800077a8#64 : BitVec 64) 4 = (0x800077ac#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi5, hmi5⟩ := obs_alu_minstret hobs5
  have hx14_5 : σ5.regs.get? Register.x14
      = some (shift_bits_left (BitVec.ofNat 64 (0x6c - 32)) (Sail.BitVec.extractLsb (0x20#6) 5 0)) :=
    obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx2_5 : σ5.regs.get? Register.x2 = some vsp :=
    obs_alu_other' hobs5 Register.x2 (by decide) hx2_4
  have hx22_5 : σ5.regs.get? Register.x22 = some (BitVec.ofNat 64 parseTableBase) :=
    obs_alu_other' hobs5 Register.x22 (by decide) hx22_4
  have hx25_5 : σ5.regs.get? Register.x25 = some (vs9 + sign_extend (m := 64) (0x001#12)) :=
    obs_alu_other' hobs5 Register.x25 (by decide) hx25_4
  have hx6_5 : σ5.regs.get? Register.x6 = some v6 :=
    obs_alu_other' hobs5 Register.x6 (by decide) hx6_4
  have hx20_5 : σ5.regs.get? Register.x20 = some v20 :=
    obs_alu_other' hobs5 Register.x20 (by decide) hx20_4
  have hx27_5 : σ5.regs.get? Register.x27 = some v27 :=
    obs_alu_other' hobs5 Register.x27 (by decide) hx27_4
  have hload5 : SvfprintfSliceLoaded σ5.mem := hmem5 ▸ hload4
  -- === 77ac: srli a5,a4,0x1e  ⇒  x15 := a4 >>> 30 = 4*(0x6c-32) ===
  obtain ⟨hg0, hg1, hg2, hg3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800077ac hload5
  have ha4n6 : (rX_bits (regidx.Regidx 0x0e#5)).run (afterNextPC (afterPrelude σ5) (0x800077ac#64))
      = .ok (shift_bits_left (BitVec.ofNat 64 (0x6c - 32)) (Sail.BitVec.extractLsb (0x20#6) 5 0))
        (afterNextPC (afterPrelude σ5) (0x800077ac#64)) := by
    apply rX_bits_x14
    rw [get?_afterNextPC σ5 (0x800077ac#64) _ (by decide) (by decide)]; exact hx14_5
  obtain ⟨σ6, i6, hs6s, hi6, hG6, hmem6, hobs6⟩ :=
    stepObs_alu σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x800077ac#64) vmi5 (0x01e75793#32)
      (instruction.SHIFTIOP (0x1e#6, regidx.Regidx 0x0e#5, regidx.Regidx 0x0f#5, sop.SRLI))
      Register.x15
      (shift_bits_right
        (shift_bits_left (BitVec.ofNat 64 (0x6c - 32)) (Sail.BitVec.extractLsb (0x20#6) 5 0))
        (Sail.BitVec.extractLsb (0x1e#6) 5 0))
      (0x93#8) (0x57#8) (0xe7#8) (0x01#8)
      hG5 hpc5 hmi5 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_01e75793 (afterPrelude σ5)
        (by rw [get?_afterPrelude σ5 _ (by decide)]; exact hG5.misa)
        (by rw [get?_afterPrelude σ5 _ (by decide)]; exact hG5.cur_privilege)
        (by rw [get?_afterPrelude σ5 _ (by decide)]; exact hG5.mseccfg))
      (execute_shiftiop_srli_char (0x1e#6) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0f#5)
        (shift_bits_left (BitVec.ofNat 64 (0x6c - 32)) (Sail.BitVec.extractLsb (0x20#6) 5 0))
        (afterNextPC (afterPrelude σ5) (0x800077ac#64))
        (sigma3_alu σ5 (0x800077ac#64) Register.x15
          (shift_bits_right
            (shift_bits_left (BitVec.ofNat 64 (0x6c - 32)) (Sail.BitVec.extractLsb (0x20#6) 5 0))
            (Sail.BitVec.extractLsb (0x1e#6) 5 0)))
        ha4n6 (wX_bits_x15 _ _))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hg0 hg1 hg2 hg3 (by decide) (by decide) (by decide) hi5
  have hstep6 : Step ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ ⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs6s
  have hpc6 : σ6.regs.get? Register.PC = some (0x800077b0#64) := by
    have := obs_alu_pc hobs6
    rwa [show BitVec.addInt (0x800077ac#64 : BitVec 64) 4 = (0x800077b0#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi6, hmi6⟩ := obs_alu_minstret hobs6
  -- x15 = 4*(0x6c-32) via slotIndexShift
  have hshift : (shift_bits_right
        (shift_bits_left (BitVec.ofNat 64 (0x6c - 32)) (Sail.BitVec.extractLsb (0x20#6) 5 0))
        (Sail.BitVec.extractLsb (0x1e#6) 5 0))
      = BitVec.ofNat 64 (4 * (0x6c - 32)) := by
    show ((BitVec.ofNat 64 (0x6c - 32)) <<< (Sail.BitVec.extractLsb (0x20#6) 5 0))
        >>> (Sail.BitVec.extractLsb (0x1e#6) 5 0) = BitVec.ofNat 64 (4 * (0x6c - 32))
    rw [show (Sail.BitVec.extractLsb (0x20#6) 5 0) = (32#6) from by decide,
        show (Sail.BitVec.extractLsb (0x1e#6) 5 0) = (30#6) from by decide]
    exact slotIndexShift (0x6c - 32) (by decide)
  have hx15_6 : σ6.regs.get? Register.x15 = some (BitVec.ofNat 64 (4 * (0x6c - 32))) := by
    have := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hshift] at this
  have hx2_6 : σ6.regs.get? Register.x2 = some vsp :=
    obs_alu_other' hobs6 Register.x2 (by decide) hx2_5
  have hx22_6 : σ6.regs.get? Register.x22 = some (BitVec.ofNat 64 parseTableBase) :=
    obs_alu_other' hobs6 Register.x22 (by decide) hx22_5
  have hx25_6 : σ6.regs.get? Register.x25 = some (vs9 + sign_extend (m := 64) (0x001#12)) :=
    obs_alu_other' hobs6 Register.x25 (by decide) hx25_5
  have hx6_6 : σ6.regs.get? Register.x6 = some v6 :=
    obs_alu_other' hobs6 Register.x6 (by decide) hx6_5
  have hx20_6 : σ6.regs.get? Register.x20 = some v20 :=
    obs_alu_other' hobs6 Register.x20 (by decide) hx20_5
  have hx27_6 : σ6.regs.get? Register.x27 = some v27 :=
    obs_alu_other' hobs6 Register.x27 (by decide) hx27_5
  have hload6 : SvfprintfSliceLoaded σ6.mem := hmem6 ▸ hload5
  -- === 77b0: add a5,a5,s6  ⇒  x15 := 4*(0x6c-32) + base = slot address ===
  obtain ⟨hh0, hh1, hh2, hh3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800077b0 hload6
  have ha5n7 : (rX_bits (regidx.Regidx 0x0f#5)).run (afterNextPC (afterPrelude σ6) (0x800077b0#64))
      = .ok (BitVec.ofNat 64 (4 * (0x6c - 32))) (afterNextPC (afterPrelude σ6) (0x800077b0#64)) := by
    apply rX_bits_x15
    rw [get?_afterNextPC σ6 (0x800077b0#64) _ (by decide) (by decide)]; exact hx15_6
  have hs6n7 : (rX_bits (regidx.Regidx 0x16#5)).run (afterNextPC (afterPrelude σ6) (0x800077b0#64))
      = .ok (BitVec.ofNat 64 parseTableBase) (afterNextPC (afterPrelude σ6) (0x800077b0#64)) := by
    apply rX_bits_x22
    rw [get?_afterNextPC σ6 (0x800077b0#64) _ (by decide) (by decide)]; exact hx22_6
  obtain ⟨σ7, i7, hs7s, hi7, hG7, hmem7, hobs7⟩ :=
    stepObs_alu σ6 i6 (c.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x800077b0#64) vmi6 (0x016787b3#32)
      (instruction.RTYPE (regidx.Regidx 0x16#5, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, rop.ADD))
      Register.x15 ((BitVec.ofNat 64 (4 * (0x6c - 32))) + (BitVec.ofNat 64 parseTableBase))
      (0xb3#8) (0x87#8) (0x67#8) (0x01#8)
      hG6 hpc6 hmi6 (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_016787b3 (afterPrelude σ6)
        (by rw [get?_afterPrelude σ6 _ (by decide)]; exact hG6.misa)
        (by rw [get?_afterPrelude σ6 _ (by decide)]; exact hG6.cur_privilege)
        (by rw [get?_afterPrelude σ6 _ (by decide)]; exact hG6.mseccfg))
      (execute_rtype_add_char (regidx.Regidx 0x16#5) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5)
        (BitVec.ofNat 64 (4 * (0x6c - 32))) (BitVec.ofNat 64 parseTableBase)
        (afterNextPC (afterPrelude σ6) (0x800077b0#64))
        (sigma3_alu σ6 (0x800077b0#64) Register.x15
          ((BitVec.ofNat 64 (4 * (0x6c - 32))) + (BitVec.ofNat 64 parseTableBase)))
        ha5n7 hs6n7 (wX_bits_x15 _ _))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hh0 hh1 hh2 hh3 (by decide) (by decide) (by decide) hi6
  have hstep7 : Step ⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ7, i7, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs7s
  have hpc7 : σ7.regs.get? Register.PC = some (0x800077b4#64) := by
    have := obs_alu_pc hobs7
    rwa [show BitVec.addInt (0x800077b0#64 : BitVec 64) 4 = (0x800077b4#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx15_7 : σ7.regs.get? Register.x15
      = some (BitVec.ofNat 64 (parseTableBase + 4 * (0x6c - 32))) := by
    have := obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((BitVec.ofNat 64 (4 * (0x6c - 32))) + (BitVec.ofNat 64 parseTableBase))
        = BitVec.ofNat 64 (parseTableBase + 4 * (0x6c - 32)) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx2_7 : σ7.regs.get? Register.x2 = some vsp :=
    obs_alu_other' hobs7 Register.x2 (by decide) hx2_6
  have hx22_7 : σ7.regs.get? Register.x22 = some (BitVec.ofNat 64 parseTableBase) :=
    obs_alu_other' hobs7 Register.x22 (by decide) hx22_6
  have hx25_7 : σ7.regs.get? Register.x25 = some (vs9 + sign_extend (m := 64) (0x001#12)) :=
    obs_alu_other' hobs7 Register.x25 (by decide) hx25_6
  have hx6_7 : σ7.regs.get? Register.x6 = some v6 :=
    obs_alu_other' hobs7 Register.x6 (by decide) hx6_6
  have hx20_7 : σ7.regs.get? Register.x20 = some v20 :=
    obs_alu_other' hobs7 Register.x20 (by decide) hx20_6
  have hx27_7 : σ7.regs.get? Register.x27 = some v27 :=
    obs_alu_other' hobs7 Register.x27 (by decide) hx27_6
  -- memory preserved end-to-end (all steps are ALU/branch, no stores)
  have hmemc : σ7.mem = c.σ.mem := by
    rw [hmem7, hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]
  -- assemble
  refine ⟨⟨σ7, i7, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩, ?_, hG7, hpc7, hx2_7, hx15_7, hx22_7,
    hx6_7, hx20_7, hx25_7, hx27_7, hmemc, hi7⟩
  exact (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans
    ((Steps.single hstep4).trans ((Steps.single hstep5).trans ((Steps.single hstep6).trans
    (Steps.single hstep7))))))

/-! ## `parseDispatch_l_full_spec` — full `%lld` dispatch `0x80007798 → 0x80008534`

Composes `parseDispatchArith_l_spec` (slot-address arithmetic) with
`SnprintfSpec13.parseDispatch_l_spec` (load + transfer through the jump table) to
obtain a single `Steps` chain from the dispatch loop head `0x80007798` through the
`.rodata` jump table to the `'l'` length-modifier conversion handler entry
`0x80008534`.  The frame pointer `x2` is preserved throughout. -/
theorem parseDispatch_l_full_spec
    (vsp vs9 v6 v20 v27 : BitVec 64) (c : Config)
    (hG : GoodState c.σ)
    (hload : SvfprintfSliceLoaded c.σ.mem)
    (hslot : ParseSlotPinned 0x6c (0x80008534#64) c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x80007798#64))
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx24 : c.σ.regs.get? Register.x24 = some (BitVec.ofNat 64 0x6c))
    (hx26 : c.σ.regs.get? Register.x26 = some (BitVec.ofNat 64 90))
    (hx22 : c.σ.regs.get? Register.x22 = some (BitVec.ofNat 64 parseTableBase))
    (hx25 : c.σ.regs.get? Register.x25 = some vs9)
    (hx6 : c.σ.regs.get? Register.x6 = some v6)
    (hx20 : c.σ.regs.get? Register.x20 = some v20)
    (hx27 : c.σ.regs.get? Register.x27 = some v27)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x80008534#64) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.σ.regs.get? Register.x6 = some v6 ∧
      c'.σ.regs.get? Register.x20 = some v20 ∧
      c'.σ.regs.get? Register.x25 = some (vs9 + sign_extend (m := 64) (0x001#12)) ∧
      c'.σ.regs.get? Register.x27 = some v27 ∧
      c'.tick < 2 := by
  obtain ⟨c1, hsteps1, hG1, hpc1, hx2_1, hx15_1, hx22_1, hx6_1, hx20_1, hx25_1, hx27_1, hmem1,
      htick1⟩ :=
    parseDispatchArith_l_spec vsp vs9 v6 v20 v27 c hG hload hpc hx2 hx24 hx26 hx22 hx25
      hx6 hx20 hx27 htick
  have hload1 : SvfprintfSliceLoaded c1.σ.mem := by rw [hmem1]; exact hload
  have hslot1 : ParseSlotPinned 0x6c (0x80008534#64) c1.σ.mem := by rw [hmem1]; exact hslot
  obtain ⟨c2, hsteps2, hG2, hpc2, hx2_2, hx6_2, hx20_2, hx25_2, hx27_2, htick2⟩ :=
    parseDispatch_l_spec vsp v6 v20 (vs9 + sign_extend (m := 64) (0x001#12)) v27 c1 hG1 hload1
      hslot1 hpc1 hx15_1 hx22_1 hx2_1 hx6_1 hx20_1 hx25_1 hx27_1 htick1
  exact ⟨c2, hsteps1.trans hsteps2, hG2, hpc2, hx2_2, hx6_2, hx20_2, hx25_2, hx27_2, htick2⟩

end Vsa.Sim
