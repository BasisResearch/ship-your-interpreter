import Vsa.Sim.SnprintfSpec36
import Vsa.Sim.SnprintfSpec16
import Vsa.Sim.SnprintfSpec26
import Vsa.Sim.PinW
import Vsa.Sim.SnprintfSpec44

/-!
# M3 Layer-3 — `SnprintfSpec37` : svfprintf entry → the `__ssprint_r` call
## `0x80007654` (`_svfprintf_r` ABI entry) → `0x8000e908` with `PreSr` assembled

THE post-widening capstone: one `Steps` chain

    svfPrologueParse_spec       (Spec36 : 0x80007654 → 0x80008534)
  ≫ parseToPrintEntry_spec      (Spec16 : 0x80008534 → 0x800080e4, widened)
  ≫ entryToPrint_neg_spec       (Spec8  : 0x800080e4 → 0x8000782c, widened)
  ≫ printEntryToSignIov_spec    (Spec11 : 0x8000782c → 0x800078ac, widened)
  ≫ iov2ToSsprintCall_spec      (Spec17 : 0x800078ac → jal done, PC = 0x8000e908,
                                 widened — kills Spec26's `hmidregs`)

from the svfprintf ABI entry with the `"%lld"` format and a negative multi-digit
argument to the completed `jal __ssprint_r`, with **`PreSr` fully assembled**
(n1 = 1 sign byte + n2 = p+1 digit bytes, count = 2, resid = 1+n2, both iovec
entries written, the running total `1+n2` at `sp+16`) plus every
`svfprintf_flushReturn_spec` (Spec25) input that is not wrapper-owned: `gp`,
the locale statics, the parse-state slots (fmt cursor at the NUL, FILE ptr,
total, `sp+0x20 = 0`), the 13 prologue spill slots, the fmt NUL byte, the FILE
`_flags` bytes, and a pointwise frame outside `[vsp, vsp+592)`.

## Residual hypotheses (the wrapper-owned facts; everything else is derived)

* the sink FILE struct built by `snprintf`/`_svsnprintf_r` (`hsinkcur`,
  `hsinkcap`, `hcap21`, `hcap31`, the `_flags` bytes `hfl0B/hfl1B/hflagB`) and
  the destination-buffer layout (`hdge/hdhi/hdstk`);
* the `va_list` area (`hvva*` layout + the eight argument bytes `ha0..ha7`);
* the argument-value ghost `hneg` (negative — ANY magnitude; the single-digit
  fast path is `entryToPrint_neg_any_spec`'s Spec43 arm);
* the static data / code pins of the loaded image (link-time constants);
* the `"%lld"` format bytes and the fmt/stack layout (as in Spec36).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (SvfprintfSliceLoaded SvfprintfSlice2Loaded FlushPinsLoaded MemmoveLoaded
  __ssprint_rLoaded __locale_mb_cur_maxLoaded __ascii_mbtowcLoaded __hidden___udivdi3Loaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Arithmetic bridges -/

/-- `sext32→64` of a small `ofNat` is transparent. -/
theorem sext32_ofNat_small_37 (n : Nat) (hn : n < 2 ^ 31) :
    (sign_extend (m := 64) (BitVec.ofNat 32 n) : BitVec 64) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  show ((BitVec.ofNat 32 n).signExtend 64).toNat = (BitVec.ofNat 64 n).toNat
  rw [BitVec.toNat_signExtend]
  have hmsb : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_decide]
    simp only [decide_eq_false_iff_not, Nat.not_le, BitVec.toNat_ofNat]
    omega
  rw [hmsb, if_neg (by simp), Nat.add_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]

/-- `0 <s sext32(2^32 − k)` is false (the padding / width guards). -/
theorem lt0_sext32_negk_37 (k : Nat) (h1 : 1 ≤ k) (h2 : k ≤ 64) :
    zopz0zI_s (0#64) (sign_extend (m := 64) (BitVec.ofNat 32 (2 ^ 32 - k))) = false := by
  have hsx : (sign_extend (m := 64) (BitVec.ofNat 32 (2 ^ 32 - k)) : BitVec 64)
      = BitVec.ofNat 64 (2 ^ 64 - k) := by
    apply BitVec.eq_of_toNat_eq
    show ((BitVec.ofNat 32 (2 ^ 32 - k)).signExtend 64).toNat = _
    rw [BitVec.toNat_signExtend]
    have hmsb : (BitVec.ofNat 32 (2 ^ 32 - k)).msb = true := by
      rw [BitVec.msb_eq_decide]
      simp only [decide_eq_true_eq, BitVec.toNat_ofNat]
      omega
    simp only [hmsb, if_true, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  rw [hsx]
  unfold zopz0zI_s
  have hti : (BitVec.ofNat 64 (2 ^ 64 - k)).toInt = -(k : Int) := by
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      if_neg (by omega)]
    omega
  rw [hti, show (0#64 : BitVec 64).toInt = 0 from by decide]
  exact decide_eq_false (by omega)

/-- `0 ≥s ofNat n` is false for positive small `n` (the total selection). -/
theorem ge0_ofNat_false_37 (n : Nat) (h1 : 1 ≤ n) (h2 : n < 2 ^ 31) :
    zopz0zKzJ_s (0#64) (BitVec.ofNat 64 n) = false := by
  unfold zopz0zKzJ_s
  have hti : (BitVec.ofNat 64 n).toInt = (n : Int) := by
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      if_pos (by omega)]
  rw [hti, show (0#64 : BitVec 64).toInt = 0 from by decide]
  exact decide_eq_false (by omega)

/-- The 32-bit `subw` image `0 − n` (`t3 = 0` padding guard operand). -/
theorem sub32_zero_ofNat_37 (n : Nat) (h1 : 1 ≤ n) (h2 : n < 2 ^ 32) :
    Sail.BitVec.extractLsb (0#64) 31 0 - Sail.BitVec.extractLsb (BitVec.ofNat 64 n) 31 0
      = BitVec.ofNat 32 (2 ^ 32 - n) := by
  rw [extractLsb32_of_lt (0#64) (by decide),
    extractLsb32_of_lt (BitVec.ofNat 64 n) (by rw [BitVec.toNat_ofNat]; omega)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat]
  omega

/-- The 32-bit `subw` image `(−1) − n` (`s4 = −1` width guard operand). -/
theorem sub32_neg1_ofNat_37 (n : Nat) (h1 : 1 ≤ n) (h2 : n + 1 < 2 ^ 32) :
    Sail.BitVec.extractLsb (0xffffffffffffffff#64) 31 0
      - Sail.BitVec.extractLsb (BitVec.ofNat 64 n) 31 0
      = BitVec.ofNat 32 (2 ^ 32 - (n + 1)) := by
  rw [show Sail.BitVec.extractLsb (0xffffffffffffffff#64) 31 0 = (0xffffffff#32 : BitVec 32)
      from by decide,
    extractLsb32_of_lt (BitVec.ofNat 64 n) (by rw [BitVec.toNat_ofNat]; omega)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat]
  omega

/-! ## Loaded-predicate transports (agreement forms not yet provided upstream) -/

/-- `SvfprintfSlice2Loaded` (handler pins in `[0x80008534, 0x80009070)`) from a
pointwise agreement below `0x8000b000`. -/
theorem slice2_of_agree_37 {m0 mem : Std.ExtHashMap Nat (BitVec 8)}
    (hag : ∀ a, 0x80007654 ≤ a → a < 0x8000b000 → mem[a]? = m0[a]?)
    (h : SvfprintfSlice2Loaded m0) : SvfprintfSlice2Loaded mem := by
  unfold Vsa.Sim.Code.SvfprintfSlice2Loaded at h ⊢
  simp only [Vsa.Sim.Code.svfprintfSlice2ChunkL, Vsa.Sim.Code.svfprintfSlice2ChunkLL] at h ⊢
  simp (disch := omega) only [hag]
  exact h

/-- `__umoddi3Loaded` (pins at `[0x800046f4, …)`) from a pointwise agreement
below `0x8000b000`. -/
theorem umoddi3_of_agree_37 {m0 mem : Std.ExtHashMap Nat (BitVec 8)}
    (hag : ∀ a, a < 0x8000b000 → mem[a]? = m0[a]?)
    (h : Vsa.Sim.Code.__umoddi3Loaded m0) : Vsa.Sim.Code.__umoddi3Loaded mem := by
  unfold Vsa.Sim.Code.__umoddi3Loaded at h ⊢
  simp only [Vsa.Sim.Code.__umoddi3Chunk0] at h ⊢
  simp (disch := omega) only [hag]
  exact h

/-- `__hidden___udivdi3Loaded` from the same agreement. -/
theorem cudivdi3_of_agree_37 {m0 mem : Std.ExtHashMap Nat (BitVec 8)}
    (hag : ∀ a, a < 0x8000b000 → mem[a]? = m0[a]?)
    (h : __hidden___udivdi3Loaded m0) : __hidden___udivdi3Loaded mem := by
  unfold Vsa.Sim.Code.__hidden___udivdi3Loaded at h ⊢
  simp only [Vsa.Sim.Code.__hidden___udivdi3Chunk0,
    Vsa.Sim.Code.__hidden___udivdi3Chunk1] at h ⊢
  simp (disch := omega) only [hag]
  exact h

/-- `ParseSlotPinned` transports across a pointwise agreement below `0x8000b000`
(the conversion table sits at `0x8001a0fc + …`; use an unconditional low-memory
agreement). -/
theorem parseSlot_of_agree_37 {m0 mem : Std.ExtHashMap Nat (BitVec 8)}
    (ch : Nat) (tgt : BitVec 64) (hch : ch ≤ 128)
    (hag : ∀ a, a < 0x8001c000 → mem[a]? = m0[a]?)
    (h : ParseSlotPinned ch tgt m0) : ParseSlotPinned ch tgt mem := by
  obtain ⟨t0, t1, t2, t3, h0, h1, h2, h3, htgt⟩ := h
  have hlt : parseTableBase + 4 * (ch - 32) + 4 ≤ 0x8001c000 := by
    have : ch - 32 ≤ ch := Nat.sub_le _ _
    simp only [parseTableBase]
    omega
  exact ⟨t0, t1, t2, t3, (hag _ (by omega)).trans h0, (hag _ (by omega)).trans h1,
    (hag _ (by omega)).trans h2, (hag _ (by omega)).trans h3, htgt⟩

/-! ## The capstone -/

/-- **svfprintf ABI entry → the `__ssprint_r` call, `PreSr` assembled.**

One `Steps` chain `0x80007654 → 0x8000e908` (the completed `jal __ssprint_r`)
for `"%lld"` with a negative multi-digit argument: Spec36's prologue+parse
capstone composed with the four post-widened segments (Spec16 ≫ Spec8 ≫
Spec11 ≫ Spec17).  The conclusion carries `PreSr` — `__ssprint_r`'s full
precondition (n1 = 1 sign byte at `sp+167`, n2 digit bytes at `sp+348−n2`,
count 2, resid `1+n2`, both iovec entries, `ra = 0x80008688`) — **plus** every
non-wrapper-owned input of `svfprintf_flushReturn_spec` (Spec25): `gp`, the
locale statics, the parse-state slots, the 13 prologue spills, the fmt NUL,
the FILE `_flags` bytes, and the pointwise frame outside `[vsp, vsp+592)`.
The five mid-registers arrive as *values* (`x9 = &__global_locale` etc.) —
Spec26's `hmidregs` residual is dead. -/
theorem svfEntryToSsprintCall_spec
    (vsp vra0 va0 vfile vfmt vva d : BitVec 64)
    (vS0o vS1o vS2o vS3o vS4o vS5o vS6o vS7o vS8o vS9o vS10o vS11o : BitVec 64)
    (fl0 fl1 : BitVec 8) (cap32 : BitVec 32)
    (a0 a1 a2 a3 a4b a5b a6 a7 : BitVec 8)
    (c : Config)
    (hG : GoodState c.σ)
    -- code / static-code pins at entry (link-time constants of the image)
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
    -- ABI entry registers
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
    -- static data (link-time constants, as Spec36)
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
    -- the "%lld" format bytes
    (hfmt0 : c.σ.mem[vfmt.toNat]? = some (0x25#8))
    (hfmt1 : c.σ.mem[vfmt.toNat + 1]? = some (0x6c#8))
    (hfmt2 : c.σ.mem[vfmt.toNat + 2]? = some (0x6c#8))
    (hfmt3 : c.σ.mem[vfmt.toNat + 3]? = some (0x64#8))
    (hfmt4 : c.σ.mem[vfmt.toNat + 4]? = some (0x00#8))
    -- the FILE `_flags` halfword (wrapper-owned; __SCLE clear)
    (hfl0B : c.σ.mem[vfile.toNat + 16]? = some fl0)
    (hfl1B : c.σ.mem[vfile.toNat + 17]? = some fl1)
    (hflagB : (zero_extend (m := 64) ((fl1.append fl0) : BitVec (8 * 2)) : BitVec 64)
        &&& sign_extend (m := 64) (0x080#12) = 0#64)
    -- the sink FILE struct (wrapper-owned)
    (hsinkcur : Pin8 c.σ.mem vfile.toNat d)
    (hsinkcap : Pin4 c.σ.mem (vfile.toNat + 12) cap32)
    (hcap21 : 21 < cap32.toNat)
    (hcap31 : cap32.toNat < 2 ^ 31)
    -- the va_list area (wrapper-owned): the eight argument bytes at `vva`
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
    -- the argument-value ghost: negative (any magnitude)
    (hneg : zopz0zKzJ_s (llArg a0 a1 a2 a3 a4b a5b a6 a7) (0#64) = false)
    -- layout
    (hfilelo : vsp.toNat + 592 ≤ vfile.toNat)
    (hfilehi : vfile.toNat + 24 ≤ 0x100000000)
    (hfileal : vfile.toNat % 8 = 0)
    (hflo : 0x80000000 ≤ vfmt.toNat)
    (hfhi : vfmt.toNat + 8 ≤ 0x100000000)
    (hfhtif : vfmt.toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ vfmt.toNat)
    (hfstk : vfmt.toNat + 8 ≤ vsp.toNat ∨ vsp.toNat + 592 ≤ vfmt.toNat)
    (hsplo : 0x8001c000 ≤ vsp.toNat)
    (hsphi : vsp.toNat + 592 ≤ 0x100000000)
    (hspal : vsp.toNat % 8 = 0)
    (hdge : 0x8001b900 ≤ d.toNat)
    (hdhi : d.toNat + 21 ≤ 0x100000000)
    (hdstk : vsp.toNat + 592 ≤ d.toNat ∨ d.toNat + 21 ≤ vsp.toNat - 128)
    (hfiled : vfile.toNat + 24 ≤ d.toNat ∨ d.toNat + 21 ≤ vfile.toNat)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧
    ∃ (n2 : Nat) (bs2 : Nat → BitVec 8) (vsubw : BitVec 64),
      1 ≤ n2 ∧ n2 ≤ 20 ∧
      ((0#64) - llArg a0 a1 a2 a3 a4b a5b a6 a7).toNat / 10 ^ (n2 - 1) ≤ 9 ∧
      (n2 = 1 ∨ 9 < ((0#64) - llArg a0 a1 a2 a3 a4b a5b a6 a7).toNat / 10 ^ (n2 - 2)) ∧
      (∀ k, k < n2 → bs2 k = BitVec.ofNat 8
        (48 + (((0#64) - llArg a0 a1 a2 a3 a4b a5b a6 a7).toNat / 10 ^ (n2 - 1 - k)) % 10)) ∧
      PreSr (fun R => c'.σ.regs.get? R) (0x80008688#64)
        (vsp + sign_extend (m := 64) (0x0e0#12))
        (vsp + sign_extend (m := 64) (0x160#12))
        vfile d
        (vsp + sign_extend (m := 64) (0x0a7#12))
        (BitVec.ofNat 64 (vsp.toNat + 348 - n2))
        vsp va0 (0x8001b798#64) (16#64) (37#64) vsubw
        (vsp + sign_extend (m := 64) (0x160#12)) va0
        1 n2 cap32 c'.σ.mem (fun _ => signByte) bs2 c' ∧
      -- Spec25's non-wrapper-owned inputs, all established at c'
      c'.σ.regs.get? Register.x3 = some (0x8001b510#64) ∧
      SlotHolds (0x8001b798#64) 0x0e8 (0x80012268#64) c'.σ.mem ∧
      c'.σ.mem[(0x8001b8f8 : Nat)]? = some (0x01#8) ∧
      SlotHolds vsp 0x000 (vfmt + sign_extend (m := 64) (0x004#12)) c'.σ.mem ∧
      (vfmt + sign_extend (m := 64) (0x004#12)).toNat = vfmt.toNat + 4 ∧
      c'.σ.mem[vfmt.toNat + 4]? = some (0x00#8) ∧
      SlotHolds vsp 0x008 vfile c'.σ.mem ∧
      SlotHolds vsp 0x010 (BitVec.ofNat 64 (1 + n2)) c'.σ.mem ∧
      SlotHolds vsp 0x020 (0#64) c'.σ.mem ∧
      SlotHolds vsp 0x1e8 vS11o c'.σ.mem ∧
      SlotHolds vsp 0x1f0 vS10o c'.σ.mem ∧
      SlotHolds vsp 0x1f8 vS9o c'.σ.mem ∧
      SlotHolds vsp 0x200 vS8o c'.σ.mem ∧
      SlotHolds vsp 0x208 vS7o c'.σ.mem ∧
      SlotHolds vsp 0x210 vS6o c'.σ.mem ∧
      SlotHolds vsp 0x218 vS5o c'.σ.mem ∧
      SlotHolds vsp 0x220 vS4o c'.σ.mem ∧
      SlotHolds vsp 0x228 vS3o c'.σ.mem ∧
      SlotHolds vsp 0x230 vS2o c'.σ.mem ∧
      SlotHolds vsp 0x238 vS1o c'.σ.mem ∧
      SlotHolds vsp 0x240 vS0o c'.σ.mem ∧
      SlotHolds vsp 0x248 vra0 c'.σ.mem ∧
      c'.σ.mem[vfile.toNat + 16]? = some fl0 ∧
      c'.σ.mem[vfile.toNat + 17]? = some fl1 ∧
      (∀ a : Nat, ¬(vsp.toNat ≤ a ∧ a < vsp.toNat + 592) →
        c'.σ.mem[a]? = c.σ.mem[a]?) := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hfmtlt := vfmt.isLt
  -- ============ stage 1: prologue + first parse pass (Spec36) ============
  obtain ⟨c1, hs1, hG1, hpc1, h1x2, h1x6, h1x20, h1x25, h1x26, h1x22, h1x27, h1x8, h1x12,
      h1x23, h1x3, h1x9, h1x18, h1x19, h1x21, h1x10,
      hS248, hS018, hS008, hS240, hS238, hS230, hS228, hS220, hS218, hS210, hS208, hS200,
      hS1f8, hS1f0, hS1e8, hS050, hS048, hS0f0, hS0e0, hS028, hS040, hS058, hS068, hS080,
      hS060, hS010, hS000, hP232, hP180, hz167, hz200s, hfmt2c1, hfmt3c1, hfmt4c1,
      hg1, hsl1, htk1, hmi1⟩ :=
    svfPrologueParse_spec vsp vra0 va0 vfile vfmt vva vS0o vS1o vS2o vS3o vS4o vS5o vS6o
      vS7o vS8o vS9o vS10o vS11o fl0 fl1 c hG hsl0 hlc0 hstr0 hms0 hlm0 hamb0 hpc
      hx2 hx1 hx3 hx10 hx11 hx12 hx13 hx8 hx9 hx22 hx18 hx19 hx20 hx21 hx23 hx24
      hx25 hx26 hx27
      hdp0 hdp1 hdp2 hdp3 hdp4 hdp5 hdp6 hdp7
      hdb0 hdb1 hdb2 hdb3 hdb4 hdb5 hdb6 hdb7
      hfn0 hfn1 hfn2 hfn3 hfn4 hfn5 hfn6 hfn7 hmbB htb0 htb1 htb2 htb3
      hfmt0 hfmt1 hfmt2 hfmt3 hfmt4 hfl0B hfl1B hflagB
      hfilelo hfilehi hfileal hflo hfhi hfhtif hfstk hsplo hsphi hspal htick
  -- entry-time pins transported to c1 (everything below the stack frame)
  have haglow1 : ∀ a : Nat, a < 0x8001c000 → c1.σ.mem[a]? = c.σ.mem[a]? :=
    fun a ha => hg1 a (by omega)
  have hsl2c1 : SvfprintfSlice2Loaded c1.σ.mem :=
    slice2_of_agree_37 (fun a h1 h2 => haglow1 a (by omega)) hsl20
  have humc1 : Vsa.Sim.Code.__umoddi3Loaded c1.σ.mem :=
    umoddi3_of_agree_37 (fun a ha => haglow1 a (by omega)) hum0
  have hudc1 : __hidden___udivdi3Loaded c1.σ.mem :=
    cudivdi3_of_agree_37 (fun a ha => haglow1 a (by omega)) hud0
  have hfpc1 : FlushPinsLoaded c1.σ.mem :=
    flushPins_of_agree_rt (fun a h1 h2 => haglow1 a (by omega)) hfp0
  have hslotc1 : ParseSlotPinned 0x64 (0x80008008#64) c1.σ.mem :=
    parseSlot_of_agree_37 0x64 _ (by omega) haglow1 hslot0
  have hapc1 : Vsa.Sim.Code.ArmPinsLoaded c1.σ.mem :=
    armPins_of_agree_43 (fun a ha => haglow1 a (by omega)) hap0
  -- the format cursor at c1 sits at vfmt+2
  have hcurT : ((vfmt + sign_extend (m := 64) (0x001#12))
      + sign_extend (m := 64) (0x001#12)).toNat = vfmt.toNat + 2 := by
    have h1 : (vfmt + sign_extend (m := 64) (0x001#12)).toNat = vfmt.toNat + 1 :=
      ptr_addoff vfmt _ 1 (by decide) (by omega)
    rw [ptr_addoff _ _ 1 (by decide) (by rw [h1]; omega), h1]
  -- the va-area pointer bytes at sp+24 (from the spilled va_list slot)
  obtain ⟨hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7⟩ := hS018
  have hvptr : ((((((((sdData_val vva).extractLsb' 56 8).append
      ((sdData_val vva).extractLsb' 48 8)).append ((sdData_val vva).extractLsb' 40 8)).append
      ((sdData_val vva).extractLsb' 32 8)).append ((sdData_val vva).extractLsb' 24 8)).append
      ((sdData_val vva).extractLsb' 16 8)).append ((sdData_val vva).extractLsb' 8 8)).append
      ((sdData_val vva).extractLsb' 0 8) = vva :=
    (pinw8_reassemble (sdData_val vva)).trans (sdData_val_id vva)
  have hvout : ∀ k : Nat, k < 8 → ¬(vsp.toNat ≤ vva.toNat + k ∧ vva.toNat + k < vsp.toNat + 592) := by
    intro k hk
    rcases hvdisj with h | h <;> omega
  -- ============ stage 2: parse gap + 'd' handler arg fetch (Spec16) ============
  obtain ⟨c2, hs2, hG2, hpc2, h2x2, h2x6, h2x20, h2x28, h2x8, h2x23, h2x12, h2x13,
      hsl2, hum2, hud2, hfp2, htk2, hfmtS2, hkeep2, hmfr2⟩ :=
    parseToPrintEntry_spec vsp
      ((vfmt + sign_extend (m := 64) (0x001#12)) + sign_extend (m := 64) (0x001#12))
      vva (0xffffffffffffffff#64) (0#64) va0 (vsp + sign_extend (m := 64) (0x160#12)) vfmt
      ((sdData_val vva).extractLsb' 0 8) ((sdData_val vva).extractLsb' 8 8)
      ((sdData_val vva).extractLsb' 16 8) ((sdData_val vva).extractLsb' 24 8)
      ((sdData_val vva).extractLsb' 32 8) ((sdData_val vva).extractLsb' 40 8)
      ((sdData_val vva).extractLsb' 48 8) ((sdData_val vva).extractLsb' 56 8)
      a0 a1 a2 a3 a4b a5b a6 a7 c1
      hG1 hsl1 hsl2c1 humc1 hudc1 hfpc1 hslotc1 hpc1 h1x2 h1x6 h1x20 h1x27 h1x8 h1x23
      h1x12 h1x25 h1x26 h1x22
      (by rw [hcurT]; exact hfmt2c1) (by rw [hcurT]; exact hfmt3c1)
      (by rw [hcurT]; omega) (by rw [hcurT]; omega)
      (by rw [hcurT]; simp only [tohostAddr] at hfhtif ⊢; omega) htk1
      (by simp only [tohostAddr]; omega) (by omega) hspal
      hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hvptr hvlo hvhiram hvhtif hvalign
      (hvdisj.imp (fun h => h) (fun h => by omega))
      ((hg1 _ (by rcases hvdisj with h | h <;> omega)).trans ha0)
      ((hg1 _ (by rcases hvdisj with h | h <;> omega)).trans ha1)
      ((hg1 _ (by rcases hvdisj with h | h <;> omega)).trans ha2)
      ((hg1 _ (by rcases hvdisj with h | h <;> omega)).trans ha3)
      ((hg1 _ (by rcases hvdisj with h | h <;> omega)).trans ha4)
      ((hg1 _ (by rcases hvdisj with h | h <;> omega)).trans ha5)
      ((hg1 _ (by rcases hvdisj with h | h <;> omega)).trans ha6)
      ((hg1 _ (by rcases hvdisj with h | h <;> omega)).trans ha7)
  -- ============ address bridges ============
  have hA167 : (vsp + sign_extend (m := 64) (0x0a7#12)).toNat = vsp.toNat + 167 :=
    ptr_addoff vsp _ 167 (by decide) (by omega)
  have hA0 : (vsp + sign_extend (m := 64) (BitVec.ofNat 12 0x000)).toNat = vsp.toNat + 0 :=
    ptr_addoff vsp _ 0 (by decide) (by omega)
  have hA8 : (vsp + sign_extend (m := 64) (BitVec.ofNat 12 0x008)).toNat = vsp.toNat + 8 :=
    ptr_addoff vsp _ 8 (by decide) (by omega)
  have hA16 : (vsp + sign_extend (m := 64) (BitVec.ofNat 12 0x010)).toNat = vsp.toNat + 16 :=
    ptr_addoff vsp _ 16 (by decide) (by omega)
  have hA32 : (vsp + sign_extend (m := 64) (BitVec.ofNat 12 0x020)).toNat = vsp.toNat + 32 :=
    ptr_addoff vsp _ 32 (by decide) (by omega)
  have hA224 : (vsp + sign_extend (m := 64) (0x0e0#12)).toNat = vsp.toNat + 224 :=
    ptr_addoff vsp _ 224 (by decide) (by omega)
  have hA232 : (vsp + sign_extend (m := 64) (0x0e8#12)).toNat = vsp.toNat + 232 :=
    ptr_addoff vsp _ 232 (by decide) (by omega)
  have hA240 : (vsp + sign_extend (m := 64) (0x0f0#12)).toNat = vsp.toNat + 240 :=
    ptr_addoff vsp _ 240 (by decide) (by omega)
  have hA352 : (vsp + sign_extend (m := 64) (0x160#12)).toNat = vsp.toNat + 352 :=
    ptr_addoff vsp _ 352 (by decide) (by omega)
  have hA360 : ((vsp + sign_extend (m := 64) (0x160#12))
      + sign_extend (m := 64) (0x008#12)).toNat = vsp.toNat + 360 := by
    rw [ptr_addoff _ _ 8 (by decide) (by rw [hA352]; omega), hA352]
  have hA368 : ((vsp + sign_extend (m := 64) (0x160#12))
      + sign_extend (m := 64) (0x010#12)).toNat = vsp.toNat + 368 := by
    rw [ptr_addoff _ _ 16 (by decide) (by rw [hA352]; omega), hA352]
  have hA376 : (((vsp + sign_extend (m := 64) (0x160#12))
      + sign_extend (m := 64) (0x010#12)) + sign_extend (m := 64) (0x008#12)).toNat
      = vsp.toNat + 376 := by
    rw [ptr_addoff _ _ 8 (by decide) (by rw [hA368]; omega), hA368]
  have hnw : vsp.toNat + 348 < 2 ^ 64 := by omega
  have htop_toNat : (entryTop vsp).toNat = vsp.toNat + 348 :=
    addoff_toNat_sn5 vsp (0x15c#12) 348 (by omega) (by decide) hnw
  -- ============ stage 3: sign block + digit loop + exit restore (Spec8) ============
  obtain ⟨c3, hs3, hG3, hpc3, h3x30, h3x31, h3x2, hbridge, htk3, hmi3,
      hsl3, hfp3, h3x20, h3x23, h3x8, h3x28, ⟨vflg, h3x6, hvflgor⟩, hs020c3, hkeep3,
      ⟨p, hexit, hpb, hmin3, h3x22, h3x16, h3x26, hbuf3⟩, hmfr3, hsign3⟩ :=
    entryToPrint_neg_any_spec (llArg a0 a1 a2 a3 a4b a5b a6 a7) vsp (BitVec.ofNat 64 0x20) va0
      (0xffffffffffffffff#64) (vsp + sign_extend (m := 64) (0x160#12)) (0#64) vfmt c2
      hG2 hsl2 hum2 hud2 hfp2
      (armPins_of_agree_43
        (fun a ha => (hmfr2 a (by omega) (by omega)).trans (haglow1 a (by omega))) hap0)
      hpc2 h2x13 h2x2 h2x6 h2x8 h2x20 h2x23 h2x28 h2x12
      (by decide) hneg (by simp only [tohostAddr]; omega) (by omega) hspal htk2
      (fun q _ _ => show ((0xffffffffffffffff#64 : BitVec 64)).toInt < (q + 1 : Int) from by
        rw [show (0xffffffffffffffff#64 : BitVec 64) = (0#64) - (0x1#64) from by decide]
        exact default_width_lt_digits q)
  -- the flag word at the PRINT entry is concretely 0x20 (both split arms agree)
  have hvflg20 : vflg = BitVec.ofNat 64 0x20 := by
    rcases hvflgor with h | h
    · exact h
    · rw [h]; decide
  rw [hvflg20] at h3x6
  -- ============ transports into c3 ============
  have hag21 : ∀ a : Nat, ¬(vsp.toNat ≤ a ∧ a < vsp.toNat + 8) →
      ¬(vsp.toNat + 24 ≤ a ∧ a < vsp.toNat + 32) → c2.σ.mem[a]? = c1.σ.mem[a]? := hmfr2
  have hag32 : ∀ a : Nat, a ≠ vsp.toNat + 167 →
      (a < vsp.toNat + 32 ∨ (vsp.toNat + 128 ≤ a ∧ a < vsp.toNat + 328) ∨
        vsp.toNat + 348 ≤ a) → c3.σ.mem[a]? = c2.σ.mem[a]? := by
    intro a hne hdom
    exact hmfr3 a (by rw [hA167]; omega) hdom
  -- mid-frame slots at c3 (transported from c1 across the two parse writes)
  have hlowUp3 : ∀ (off : Nat) (v : BitVec 64) (A : Nat),
      (vsp + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat = A →
      (vsp.toNat + 8 ≤ A ∧ A + 8 ≤ vsp.toNat + 24) ∨
        (vsp.toNat + 128 ≤ A ∧ A + 8 ≤ vsp.toNat + 328 ∧ ¬(A ≤ vsp.toNat + 167 ∧ vsp.toNat + 167 < A + 8)) ∨
        (vsp.toNat + 348 ≤ A ∧ A + 8 ≤ vsp.toNat + 592) →
      SlotHolds vsp off v c1.σ.mem → SlotHolds vsp off v c3.σ.mem := by
    intro off v A hA hcond h
    refine slotHolds_of_agree_rt vsp off v A _ _ hA (fun a ha1 ha2 => ?_) h
    exact (hag32 a (by omega) (by omega)).trans (hag21 a (by omega) (by omega))
  have h010c3 : SlotHolds vsp 0x010 (0#64) c3.σ.mem :=
    hlowUp3 0x010 (0#64) (vsp.toNat + 16) hA16 (by omega) hS010
  have h008c3 : SlotHolds vsp 0x008 vfile c3.σ.mem :=
    hlowUp3 0x008 vfile (vsp.toNat + 8) hA8 (by omega) hS008
  have h0f0c3 : SlotHolds vsp 0x0f0 (0#64) c3.σ.mem :=
    hlowUp3 0x0f0 (0#64) (vsp.toNat + 240) hA240 (by omega) hS0f0
  have h0e0c3 : SlotHolds vsp 0x0e0 (vsp + sign_extend (m := 64) (0x160#12)) c3.σ.mem :=
    hlowUp3 0x0e0 (vsp + sign_extend (m := 64) (0x160#12)) (vsp.toNat + 224) hA224
      (by omega) hS0e0
  -- the iov count word (still 0) at c3
  have hsw0 : swData (0#64) = (0#32 : BitVec 32) := by decide
  rw [hsw0] at hP232
  have hP232c3 : Pin4 c3.σ.mem (vsp.toNat + 232) (0#32) :=
    Pin4_frame (fun k hk1 hk2 => (hag32 k (by omega) (by omega)).trans
      (hag21 k (by omega) (by omega))) hP232
  -- ============ stage 4: the sign iovec (Spec11) ============
  obtain ⟨c4, hs4, hG4, hpc4, h4x23, h4x2, hmem4eq, htk4, hmi4, h4x5, h4x12, hkeep4⟩ :=
    printEntryToSignIov_spec vsp (BitVec.ofNat 64 0x20) (0#64) (BitVec.ofNat 64 (p + 2))
      (vsp + sign_extend (m := 64) (0x160#12)) (0#64) (0#32) signByte c3
      hG3 hsl3 hfp3 hpc3 h3x2 h3x6 h3x28 h3x16 h3x23
      h0f0c3
      (by rw [hA232]; exact hP232c3.1) (by rw [hA232]; exact hP232c3.2.1)
      (by rw [hA232]; exact hP232c3.2.2.1) (by rw [hA232]; exact hP232c3.2.2.2)
      hsign3
      (by decide)
      (by rw [sub32_zero_ofNat_37 (p + 2) (by omega) (by omega)]
          exact lt0_sext32_negk_37 (p + 2) (by omega) (by omega))
      (by decide) (by decide)
      (by omega) (by omega) (by simp only [tohostAddr]; omega) hspal
      (by rw [hA352]; omega) (by rw [hA352]; omega)
      (by rw [hA352]; simp only [tohostAddr]; omega) (by rw [hA352]; omega) htk3
  -- normalize the Spec11 write addresses and derive the c4 ↔ c3 agreement
  rw [hA352, hA360, hA240, hA232] at hmem4eq
  have hag43 : ∀ a : Nat, ¬(vsp.toNat + 240 ≤ a ∧ a < vsp.toNat + 248) →
      ¬(vsp.toNat + 352 ≤ a ∧ a < vsp.toNat + 368) →
      ¬(vsp.toNat + 232 ≤ a ∧ a < vsp.toNat + 236) →
      c4.σ.mem[a]? = c3.σ.mem[a]? := by
    intro a hA hB hC
    rw [hmem4eq, getElem?_writeMap4_out _ _ _ _ (by omega),
      getElem?_writeMap8_out _ _ _ _ (by omega), getElem?_writeMap8_out _ _ _ _ (by omega),
      getElem?_writeMap8_out _ _ _ _ (by omega)]
  -- registers at c4
  have h4x6 : c4.σ.regs.get? Register.x6 = some (BitVec.ofNat 64 0x20) :=
    hkeep4 Register.x6 (by decide) _ h3x6
  have h4x8 : c4.σ.regs.get? Register.x8 = some va0 :=
    hkeep4 Register.x8 (by decide) _ h3x8
  have h4x16 : c4.σ.regs.get? Register.x16 = some (BitVec.ofNat 64 (p + 2)) :=
    hkeep4 Register.x16 (by decide) _ h3x16
  have h4x20 : c4.σ.regs.get? Register.x20 = some (0xffffffffffffffff#64) :=
    hkeep4 Register.x20 (by decide) _ h3x20
  have h4x22 : c4.σ.regs.get? Register.x22 = some (BitVec.ofNat 64 (p + 1)) :=
    hkeep4 Register.x22 (by decide) _ h3x22
  have h4x26 : c4.σ.regs.get? Register.x26
      = some (BitVec.ofNat 64 ((entryTop vsp).toNat - 1 - p)) :=
    hkeep4 Register.x26 (by decide) _ h3x26
  have h4x28 : c4.σ.regs.get? Register.x28 = some (0#64) :=
    hkeep4 Register.x28 (by decide) _ h3x28
  -- memory facts at c4
  have hload4 : SvfprintfSliceLoaded c4.σ.mem := by
    rw [hmem4eq]
    exact svfprintfSlice_writeMap4_pe _ _ _ (by omega)
      (svfprintfSlice_writeMap8_sn5 _ _ _ (by omega)
        (svfprintfSlice_writeMap8_sn5 _ _ _ (by omega)
          (svfprintfSlice_writeMap8_sn5 _ _ _ (by omega) hsl3)))
  have hfp4 : FlushPinsLoaded c4.σ.mem := by
    rw [hmem4eq]
    exact flushPins_writeMap4_pe _ _ _ (by omega)
      (flushPins_writeMap8_fl _ _ _ (by omega)
        (flushPins_writeMap8_fl _ _ _ (by omega)
          (flushPins_writeMap8_fl _ _ _ (by omega) hfp3)))
  have hsw1 : swData (sign_extend (m := 64)
      (Sail.BitVec.extractLsb ((sign_extend (m := 64) (0#32 : BitVec 32) : BitVec 64)
        + sign_extend (m := 64) (0x001#12)) 31 0)) = (1#32 : BitVec 32) := by decide
  have hcnt1c4 : Pin4 c4.σ.mem (vsp.toNat + 232) (1#32) := by
    rw [hmem4eq, ← hsw1]
    exact Pin4_writeMap4 _ _ _
  have htot4 : SlotHolds vsp 0x010 (0#64) c4.σ.mem :=
    slotHolds_of_agree_rt vsp 0x010 (0#64) (vsp.toNat + 16) _ _ hA16
      (fun a ha1 ha2 => hag43 a (by omega) (by omega) (by omega)) h010c3
  have hstr4 : SlotHolds vsp 0x008 vfile c4.σ.mem :=
    slotHolds_of_agree_rt vsp 0x008 vfile (vsp.toNat + 8) _ _ hA8
      (fun a ha1 ha2 => hag43 a (by omega) (by omega) (by omega)) h008c3
  -- ============ stage 5: the second iovec + call (Spec17) ============
  obtain ⟨c5, hs5, hG5, hpc5, h5x1, h5x10, h5x11, h5x12, h5x2, h5x5, h5x6, h5x8, h5x16,
      h5x20, h5x22, h5x23, h5x26, h5x28, hmem5eq, htk5, hmi5, hkeep5⟩ :=
    iov2ToSsprintCall_spec vsp (0#64) (BitVec.ofNat 64 0x20) va0
      ((0#64) + sign_extend (m := 64) (0x001#12)) (BitVec.ofNat 64 (p + 2))
      (0xffffffffffffffff#64) (BitVec.ofNat 64 (p + 1))
      ((vsp + sign_extend (m := 64) (0x160#12)) + sign_extend (m := 64) (0x010#12))
      (BitVec.ofNat 64 ((entryTop vsp).toNat - 1 - p)) (0#64) vfile (0#64) (1#32) c4
      hG4 hload4 hfp4 hpc4 h4x2 h4x5 h4x6 h4x8 h4x12 h4x16 h4x20 h4x22 h4x23 h4x26 h4x28
      (by rw [hA232]; exact hcnt1c4.1) (by rw [hA232]; exact hcnt1c4.2.1)
      (by rw [hA232]; exact hcnt1c4.2.2.1) (by rw [hA232]; exact hcnt1c4.2.2.2)
      htot4 hstr4
      (by decide)
      (by rw [sub32_neg1_ofNat_37 (p + 1) (by omega) (by omega)]
          exact lt0_sext32_negk_37 (p + 1 + 1) (by omega) (by omega))
      (by decide) (by decide) (by decide)
      (by simp only [bne_iff_ne, ne_eq]
          intro hz
          have hzt : (((0#64) + sign_extend (m := 64) (0x001#12))
              + BitVec.ofNat 64 (p + 1)).toNat = 0 := by rw [hz]; rfl
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
            show ((sign_extend (m := 64) (0x001#12) : BitVec 64)).toNat = 1 from by decide]
            at hzt
          omega)
      (by simp only [tohostAddr]; omega) (by omega) hspal
      (by rw [hA368]; omega) (by rw [hA368]; omega)
      (by rw [hA368]; simp only [tohostAddr]; omega) (by rw [hA368]; omega)
      (Or.inr (by rw [hA368]; omega)) htk4
  -- normalize the Spec17 write addresses and derive the c5 ↔ c4 agreement
  rw [hA240, hA368, hA376, hA232, hA16] at hmem5eq
  have hag54 : ∀ a : Nat, ¬(vsp.toNat + 240 ≤ a ∧ a < vsp.toNat + 248) →
      ¬(vsp.toNat + 368 ≤ a ∧ a < vsp.toNat + 384) →
      ¬(vsp.toNat + 232 ≤ a ∧ a < vsp.toNat + 236) →
      ¬(vsp.toNat + 16 ≤ a ∧ a < vsp.toNat + 24) →
      c5.σ.mem[a]? = c4.σ.mem[a]? := by
    intro a hA hB hC hD
    rw [hmem5eq, getElem?_writeMap8_out _ _ _ _ (by omega),
      getElem?_writeMap4_out _ _ _ _ (by omega), getElem?_writeMap8_out _ _ _ _ (by omega),
      getElem?_writeMap8_out _ _ _ _ (by omega), getElem?_writeMap8_out _ _ _ _ (by omega)]
  -- composed agreements
  have hag51 : ∀ a : Nat, ¬(vsp.toNat ≤ a ∧ a < vsp.toNat + 592) →
      c5.σ.mem[a]? = c1.σ.mem[a]? := by
    intro a h
    exact (hag54 a (by omega) (by omega) (by omega) (by omega)).trans
      ((hag43 a (by omega) (by omega) (by omega)).trans
        ((hag32 a (by omega) (by omega)).trans (hag21 a (by omega) (by omega))))
  have hagAll : ∀ a : Nat, ¬(vsp.toNat ≤ a ∧ a < vsp.toNat + 592) →
      c5.σ.mem[a]? = c.σ.mem[a]? :=
    fun a h => (hag51 a h).trans (hg1 a h)
  -- ============ mid-registers at c5 (values, killing `hmidregs`) ============
  have hkeepAll : KeepRegs midRegs5 c1.σ c5.σ :=
    keep_trans (keep_trans (keep_trans hkeep2 hkeep3) (keep_sub (by decide) hkeep4)) hkeep5
  have h5x3 : c5.σ.regs.get? Register.x3 = some (0x8001b510#64) :=
    hkeepAll Register.x3 (by decide) _ h1x3
  have h5x9 : c5.σ.regs.get? Register.x9 = some (0x8001b798#64) :=
    hkeepAll Register.x9 (by decide) _ h1x9
  have h5x18 : c5.σ.regs.get? Register.x18 = some (16#64) :=
    hkeepAll Register.x18 (by decide) _ h1x18
  have h5x19 : c5.σ.regs.get? Register.x19 = some (37#64) :=
    hkeepAll Register.x19 (by decide) _ h1x19
  have h5x21 : c5.σ.regs.get? Register.x21
      = some (vsp + sign_extend (m := 64) (0x160#12)) :=
    hkeepAll Register.x21 (by decide) _ h1x21
  -- ============ PreSr's fresh pins (from the Spec11/Spec17 writes) ============
  have hresv : ((0#64) + sign_extend (m := 64) (0x001#12)) + BitVec.ofNat 64 (p + 1)
      = BitVec.ofNat 64 (1 + (p + 1)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
      show ((0#64 : BitVec 64)).toNat = 0 from rfl,
      show ((sign_extend (m := 64) (0x001#12) : BitVec 64)).toNat = 1 from by decide]
    omega
  have hresid5 : Pin8 c5.σ.mem (vsp.toNat + 240) (BitVec.ofNat 64 (1 + (p + 1))) := by
    rw [hmem5eq, ← hresv]
    exact Pin8_frame (fun k hk1 hk2 => by
      rw [getElem?_writeMap8_out _ _ _ _ (by omega), getElem?_writeMap4_out _ _ _ _ (by omega),
        getElem?_writeMap8_out _ _ _ _ (by omega), getElem?_writeMap8_out _ _ _ _ (by omega)])
      (Pin8_writeMap8 _ _ _)
  have hsw2 : swData (sign_extend (m := 64)
      (Sail.BitVec.extractLsb ((sign_extend (m := 64) (1#32 : BitVec 32) : BitVec 64)
        + sign_extend (m := 64) (0x001#12)) 31 0)) = (2#32 : BitVec 32) := by decide
  have hcount5 : Pin4 c5.σ.mem (vsp.toNat + 232) (2#32) := by
    rw [hmem5eq, ← hsw2]
    exact Pin4_frame (fun k hk1 hk2 => by
      rw [getElem?_writeMap8_out _ _ _ _ (by omega)]) (Pin4_writeMap4 _ _ _)
  have hs2eq : BitVec.ofNat 64 ((entryTop vsp).toNat - 1 - p)
      = BitVec.ofNat 64 (vsp.toNat + 348 - (p + 1)) := by
    rw [htop_toNat]
    congr 1
    omega
  have hiov1b5 : Pin8 c5.σ.mem (vsp.toNat + 368) (BitVec.ofNat 64 (vsp.toNat + 348 - (p + 1))) := by
    rw [hmem5eq, ← hs2eq]
    exact Pin8_frame (fun k hk1 hk2 => by
      rw [getElem?_writeMap8_out _ _ _ _ (by omega), getElem?_writeMap4_out _ _ _ _ (by omega),
        getElem?_writeMap8_out _ _ _ _ (by omega)]) (Pin8_writeMap8 _ _ _)
  have hiov1l5 : Pin8 c5.σ.mem (vsp.toNat + 376) (BitVec.ofNat 64 (p + 1)) := by
    rw [hmem5eq]
    exact Pin8_frame (fun k hk1 hk2 => by
      rw [getElem?_writeMap8_out _ _ _ _ (by omega), getElem?_writeMap4_out _ _ _ _ (by omega)])
      (Pin8_writeMap8 _ _ _)
  -- the running total (the write selects `vlen` since `t3 = 0 <s len`)
  have hseltot : sign_extend (m := 64)
      (Sail.BitVec.extractLsb (if zopz0zKzJ_s (0#64) (BitVec.ofNat 64 (p + 2)) = true
          then (0#64) else BitVec.ofNat 64 (p + 2)) 31 0
        + Sail.BitVec.extractLsb (0#64) 31 0)
      = BitVec.ofNat 64 (1 + (p + 1)) := by
    rw [if_neg (by rw [ge0_ofNat_false_37 (p + 2) (by omega) (by omega)]; exact Bool.false_ne_true),
      show Sail.BitVec.extractLsb (0#64) 31 0 = (0#32 : BitVec 32) from by decide,
      extractLsb32_of_lt (BitVec.ofNat 64 (p + 2)) (by rw [BitVec.toNat_ofNat]; omega),
      BitVec.add_zero,
      show (BitVec.ofNat 64 (p + 2)).toNat = p + 2 from by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega),
      sext32_ofNat_small_37 (p + 2) (by omega)]
    congr 1
    omega
  have htotpin5 : Pin8 c5.σ.mem (vsp.toNat + 16) (BitVec.ofNat 64 (1 + (p + 1))) := by
    rw [hmem5eq, ← hseltot]
    exact Pin8_writeMap8 _ _ _
  have htotS5 : SlotHolds vsp 0x010 (BitVec.ofNat 64 (1 + (p + 1))) c5.σ.mem :=
    slotHolds_of_pin8_rt vsp 0x010 _ _ _ hA16 htotpin5
  -- the sign iovec entry (Spec11's writes, surviving Spec17's writes)
  have hiov0b5 : Pin8 c5.σ.mem (vsp.toNat + 352) (vsp + sign_extend (m := 64) (0x0a7#12)) := by
    have h4 : Pin8 c4.σ.mem (vsp.toNat + 352) (vsp + sign_extend (m := 64) (0x0a7#12)) := by
      rw [hmem4eq]
      exact Pin8_frame (fun k hk1 hk2 => by
        rw [getElem?_writeMap4_out _ _ _ _ (by omega),
          getElem?_writeMap8_out _ _ _ _ (by omega),
          getElem?_writeMap8_out _ _ _ _ (by omega)]) (Pin8_writeMap8 _ _ _)
    exact Pin8_frame (fun k hk1 hk2 =>
      hag54 k (by omega) (by omega) (by omega) (by omega)) h4
  have hiov0l5 : Pin8 c5.σ.mem (vsp.toNat + 360) (BitVec.ofNat 64 1) := by
    have h4 : Pin8 c4.σ.mem (vsp.toNat + 360) (BitVec.ofNat 64 1) := by
      rw [hmem4eq, show (0x1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl]
      exact Pin8_frame (fun k hk1 hk2 => by
        rw [getElem?_writeMap4_out _ _ _ _ (by omega),
          getElem?_writeMap8_out _ _ _ _ (by omega)]) (Pin8_writeMap8 _ _ _)
    exact Pin8_frame (fun k hk1 hk2 =>
      hag54 k (by omega) (by omega) (by omega) (by omega)) h4
  -- the source bytes: the '-' at sp+167 and the digits at sp+348−(p+1)
  have hbs1c5 : MvBytes c5.σ.mem (vsp + sign_extend (m := 64) (0x0a7#12)) 1
      (fun _ => signByte) := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    show c5.σ.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat + 0]? = some signByte
    rw [show (vsp + sign_extend (m := 64) (0x0a7#12)).toNat + 0
        = (vsp + sign_extend (m := 64) (0x0a7#12)).toNat from rfl, hA167]
    exact (hag54 _ (by omega) (by omega) (by omega) (by omega)).trans
      ((hag43 _ (by omega) (by omega) (by omega)).trans (by rw [← hA167]; exact hsign3))
  have hbs2c5 : MvBytes c5.σ.mem (BitVec.ofNat 64 (vsp.toNat + 348 - (p + 1))) (p + 1)
      (fun k => BitVec.ofNat 8
        (48 + (((0#64) - llArg a0 a1 a2 a3 a4b a5b a6 a7).toNat / 10 ^ (p - k)) % 10)) := by
    intro k hk
    have haddr : (BitVec.ofNat 64 (vsp.toNat + 348 - (p + 1))).toNat + k
        = (entryTop vsp).toNat - 1 - (p - k) := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), htop_toNat]
      omega
    rw [haddr]
    exact (hag54 _ (by rw [htop_toNat]; omega) (by rw [htop_toNat]; omega)
        (by rw [htop_toNat]; omega) (by rw [htop_toNat]; omega)).trans
      ((hag43 _ (by rw [htop_toNat]; omega) (by rw [htop_toNat]; omega)
          (by rw [htop_toNat]; omega)).trans
        (hbuf3 (p - k) (by omega)))
  -- ============ transported caller memory (sink / statics / slots) ============
  have hsinkcur5 : Pin8 c5.σ.mem vfile.toNat d :=
    Pin8_frame (fun k hk1 hk2 => hagAll k (by omega)) hsinkcur
  have hsinkcap5 : Pin4 c5.σ.mem (vfile.toNat + 12) cap32 :=
    Pin4_frame (fun k hk1 hk2 => hagAll k (by omega)) hsinkcap
  have hfl0c5 : c5.σ.mem[vfile.toNat + 16]? = some fl0 :=
    (hagAll _ (by omega)).trans hfl0B
  have hfl1c5 : c5.σ.mem[vfile.toNat + 17]? = some fl1 :=
    (hagAll _ (by omega)).trans hfl1B
  -- the locale statics (mbtowc fn-ptr slot + __mb_cur_max byte)
  have hfnslot0 : SlotHolds (0x8001b798#64) 0x0e8 (0x80012268#64) c.σ.mem := by
    unfold SlotHolds
    rw [show ((0x8001b798#64 : BitVec 64)
        + sign_extend (m := 64) (BitVec.ofNat 12 0x0e8)).toNat = 0x8001b880 from by decide]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [show (sdData_val (0x80012268#64)).extractLsb' 0 8 = (0x68#8 : BitVec 8) from by decide]
      exact hfn0
    · rw [show (sdData_val (0x80012268#64)).extractLsb' 8 8 = (0x22#8 : BitVec 8) from by decide]
      exact hfn1
    · rw [show (sdData_val (0x80012268#64)).extractLsb' 16 8 = (0x01#8 : BitVec 8) from by decide]
      exact hfn2
    · rw [show (sdData_val (0x80012268#64)).extractLsb' 24 8 = (0x80#8 : BitVec 8) from by decide]
      exact hfn3
    · rw [show (sdData_val (0x80012268#64)).extractLsb' 32 8 = (0x00#8 : BitVec 8) from by decide]
      exact hfn4
    · rw [show (sdData_val (0x80012268#64)).extractLsb' 40 8 = (0x00#8 : BitVec 8) from by decide]
      exact hfn5
    · rw [show (sdData_val (0x80012268#64)).extractLsb' 48 8 = (0x00#8 : BitVec 8) from by decide]
      exact hfn6
    · rw [show (sdData_val (0x80012268#64)).extractLsb' 56 8 = (0x00#8 : BitVec 8) from by decide]
      exact hfn7
  have hfnslot5 : SlotHolds (0x8001b798#64) 0x0e8 (0x80012268#64) c5.σ.mem :=
    slotHolds_of_agree_rt _ _ _ 0x8001b880 _ _ (by decide)
      (fun a ha1 ha2 => hagAll a (by omega)) hfnslot0
  have hmb5 : c5.σ.mem[(0x8001b8f8 : Nat)]? = some (0x01#8) :=
    (hagAll _ (by omega)).trans hmbB
  -- the fmt cursor slot (value = vfmt+4, pointing at the NUL)
  have hfmtval : ((((vfmt + sign_extend (m := 64) (0x001#12))
        + sign_extend (m := 64) (0x001#12)) + sign_extend (m := 64) (0x001#12))
        + sign_extend (m := 64) (0x001#12))
      = vfmt + sign_extend (m := 64) (0x004#12) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add,
      show ((sign_extend (m := 64) (0x001#12) : BitVec 64)).toNat = 1 from by decide,
      show ((sign_extend (m := 64) (0x004#12) : BitVec 64)).toNat = 4 from by decide]
    omega
  have hfmtN4 : (vfmt + sign_extend (m := 64) (0x004#12)).toNat = vfmt.toNat + 4 :=
    ptr_addoff vfmt _ 4 (by decide) (by omega)
  have hfmtS5 : SlotHolds vsp 0x000 (vfmt + sign_extend (m := 64) (0x004#12)) c5.σ.mem := by
    rw [← hfmtval]
    refine slotHolds_of_agree_rt vsp 0x000 _ (vsp.toNat + 0) _ _ hA0
      (fun a ha1 ha2 => ?_) hfmtS2
    exact (hag54 a (by omega) (by omega) (by omega) (by omega)).trans
      ((hag43 a (by omega) (by omega) (by omega)).trans (hag32 a (by omega) (by omega)))
  have hnul5 : c5.σ.mem[vfmt.toNat + 4]? = some (0x00#8) :=
    ((hag51 _ (by rcases hfstk with h | h <;> omega)).trans hfmt4c1)
  -- SlotHolds 0x008 / 0x020 at c5
  have hstr5 : SlotHolds vsp 0x008 vfile c5.σ.mem :=
    slotHolds_of_agree_rt vsp 0x008 vfile (vsp.toNat + 8) _ _ hA8
      (fun a ha1 ha2 => hag54 a (by omega) (by omega) (by omega) (by omega)) hstr4
  have hs020c5 : SlotHolds vsp 0x020 (0#64) c5.σ.mem := by
    refine slotHolds_of_agree_rt vsp 0x020 (0#64) (vsp.toNat + 32) _ _ hA32
      (fun a ha1 ha2 => ?_) hs020c3
    exact (hag54 a (by omega) (by omega) (by omega) (by omega)).trans
      (hag43 a (by omega) (by omega) (by omega))
  -- the 13 prologue spill slots at c5
  have hslotHi : ∀ (off : Nat) (v : BitVec 64) (A : Nat),
      (vsp + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat = A →
      (vsp.toNat + 488 ≤ A ∧ A + 8 ≤ vsp.toNat + 592) →
      SlotHolds vsp off v c1.σ.mem → SlotHolds vsp off v c5.σ.mem := by
    intro off v A hA hcond h
    refine slotHolds_of_agree_rt vsp off v A _ _ hA (fun a ha1 ha2 => ?_) h
    exact (hag54 a (by omega) (by omega) (by omega) (by omega)).trans
      ((hag43 a (by omega) (by omega) (by omega)).trans
        ((hag32 a (by omega) (by omega)).trans (hag21 a (by omega) (by omega))))
  have h1e8c5 := hslotHi 0x1e8 vS11o (vsp.toNat + 488)
    (ptr_addoff vsp _ 488 (by decide) (by omega)) (by omega) hS1e8
  have h1f0c5 := hslotHi 0x1f0 vS10o (vsp.toNat + 496)
    (ptr_addoff vsp _ 496 (by decide) (by omega)) (by omega) hS1f0
  have h1f8c5 := hslotHi 0x1f8 vS9o (vsp.toNat + 504)
    (ptr_addoff vsp _ 504 (by decide) (by omega)) (by omega) hS1f8
  have h200c5 := hslotHi 0x200 vS8o (vsp.toNat + 512)
    (ptr_addoff vsp _ 512 (by decide) (by omega)) (by omega) hS200
  have h208c5 := hslotHi 0x208 vS7o (vsp.toNat + 520)
    (ptr_addoff vsp _ 520 (by decide) (by omega)) (by omega) hS208
  have h210c5 := hslotHi 0x210 vS6o (vsp.toNat + 528)
    (ptr_addoff vsp _ 528 (by decide) (by omega)) (by omega) hS210
  have h218c5 := hslotHi 0x218 vS5o (vsp.toNat + 536)
    (ptr_addoff vsp _ 536 (by decide) (by omega)) (by omega) hS218
  have h220c5 := hslotHi 0x220 vS4o (vsp.toNat + 544)
    (ptr_addoff vsp _ 544 (by decide) (by omega)) (by omega) hS220
  have h228c5 := hslotHi 0x228 vS3o (vsp.toNat + 552)
    (ptr_addoff vsp _ 552 (by decide) (by omega)) (by omega) hS228
  have h230c5 := hslotHi 0x230 vS2o (vsp.toNat + 560)
    (ptr_addoff vsp _ 560 (by decide) (by omega)) (by omega) hS230
  have h238c5 := hslotHi 0x238 vS1o (vsp.toNat + 568)
    (ptr_addoff vsp _ 568 (by decide) (by omega)) (by omega) hS238
  have h240c5 := hslotHi 0x240 vS0o (vsp.toNat + 576)
    (ptr_addoff vsp _ 576 (by decide) (by omega)) (by omega) hS240
  have h248c5 := hslotHi 0x248 vra0 (vsp.toNat + 584)
    (ptr_addoff vsp _ 584 (by decide) (by omega)) (by omega) hS248
  -- the uio.uio_iov slot (base pointer) at c5, as the `Pin8` at `q`
  have hviovc5 : SlotHolds vsp 0x0e0 (vsp + sign_extend (m := 64) (0x160#12)) c5.σ.mem := by
    refine slotHolds_of_agree_rt vsp 0x0e0 _ (vsp.toNat + 224) _ _ hA224
      (fun a ha1 ha2 => ?_) h0e0c3
    exact (hag54 a (by omega) (by omega) (by omega) (by omega)).trans
      (hag43 a (by omega) (by omega) (by omega))
  -- code pins at c5 (for `PreSr`)
  have hsspL5 : __ssprint_rLoaded c5.σ.mem :=
    ssprint_frame_sr _ _ (fun a ha => hagAll a (by omega)) hsspL0
  have hsspuL5 : Vsa.Sim.Code.__ssputs_rLoaded c5.σ.mem :=
    ssputs_frame_ss _ _ (fun a ha => hagAll a (by omega)) hsspuL0
  have hmvL5 : MemmoveLoaded c5.σ.mem :=
    memmove_frame_sr _ _ (fun a ha => hagAll a (by omega)) hmvL0
  -- ============ PreSr ============
  have hRegions : SrRegions (vsp + sign_extend (m := 64) (0x0e0#12))
      (vsp + sign_extend (m := 64) (0x160#12)) vfile d
      (vsp + sign_extend (m := 64) (0x0a7#12))
      (BitVec.ofNat 64 (vsp.toNat + 348 - (p + 1))) vsp 1 (p + 1) := by
    have hs2N : (BitVec.ofNat 64 (vsp.toNat + 348 - (p + 1))).toNat
        = vsp.toNat + 348 - (p + 1) := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    constructor <;> omega
  have hPre : PreSr (fun R => c5.σ.regs.get? R) (0x80008688#64)
      (vsp + sign_extend (m := 64) (0x0e0#12))
      (vsp + sign_extend (m := 64) (0x160#12)) vfile d
      (vsp + sign_extend (m := 64) (0x0a7#12))
      (BitVec.ofNat 64 (vsp.toNat + 348 - (p + 1)))
      vsp va0 (0x8001b798#64) (16#64) (37#64)
      (sign_extend (m := 64)
        (Sail.BitVec.extractLsb (0xffffffffffffffff#64) 31 0
          - Sail.BitVec.extractLsb (BitVec.ofNat 64 (p + 1)) 31 0))
      (vsp + sign_extend (m := 64) (0x160#12)) va0
      1 (p + 1) cap32 c5.σ.mem (fun _ => signByte)
      (fun k => BitVec.ofNat 8
        (48 + (((0#64) - llArg a0 a1 a2 a3 a4b a5b a6 a7).toNat / 10 ^ (p - k)) % 10)) c5 :=
    { good := hG5, loaded := hsspL5, sloaded := hsspuL5, mvloaded := hmvL5,
      pc := hpc5, ra := h5x1, sp := h5x2, a0 := h5x10, a1 := h5x11, a2 := h5x12,
      cs0 := h5x8, cs1 := h5x9, cs2 := h5x18, cs3 := h5x19, cs4 := h5x20,
      cs5 := h5x21, minstret := hmi5, tick := htk5, regions := hRegions,
      hviov := pin8_of_slotHolds_i26 vsp 0x0e0 _
        ((vsp + sign_extend (m := 64) (0x0e0#12)).toNat) c5.σ.mem rfl hviovc5,
      hcount := by
        rw [show (vsp + sign_extend (m := 64) (0x0e0#12)).toNat + 8 = vsp.toNat + 232
          from by omega]
        exact hcount5,
      hresid := by
        rw [show (vsp + sign_extend (m := 64) (0x0e0#12)).toNat + 16 = vsp.toNat + 240
          from by omega]
        exact hresid5,
      hiov0b := by rw [hA352]; exact hiov0b5,
      hiov0l := by rw [hA352]; exact hiov0l5,
      hiov1b := by rw [hA352]; exact hiov1b5,
      hiov1l := by rw [hA352]; exact hiov1l5,
      hcursor := hsinkcur5, hcap := hsinkcap5, hbs1 := hbs1c5, hbs2 := hbs2c5,
      hcaplt := by omega, hcap31 := hcap31, memeq := rfl, hframe := fun R _ => rfl }
  -- ============ final assembly ============
  refine ⟨c5, ((hs1.trans hs2).trans ((hs3.trans hs4).trans hs5)), p + 1,
    (fun k => BitVec.ofNat 8
      (48 + (((0#64) - llArg a0 a1 a2 a3 a4b a5b a6 a7).toNat / 10 ^ (p - k)) % 10)),
    (sign_extend (m := 64)
      (Sail.BitVec.extractLsb (0xffffffffffffffff#64) 31 0
        - Sail.BitVec.extractLsb (BitVec.ofNat 64 (p + 1)) 31 0)),
    (by omega), (by omega), hexit,
    (by
      rcases hmin3 with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by rw [show p + 1 - 2 = p - 1 from by omega]; exact h)),
    (fun k hk => rfl), hPre,
    h5x3, hfnslot5, hmb5, hfmtS5, hfmtN4, hnul5, hstr5,
    (by rw [show (1 : Nat) + (p + 1) = 1 + (p + 1) from rfl]; exact htotS5),
    hs020c5,
    h1e8c5, h1f0c5, h1f8c5, h200c5, h208c5, h210c5, h218c5, h220c5, h228c5, h230c5,
    h238c5, h240c5, h248c5, hfl0c5, hfl1c5, hagAll⟩

end Vsa.Sim
