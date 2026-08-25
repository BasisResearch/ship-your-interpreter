import Vsa.Sim.SnprintfProCommon
import Vsa.Sim.SnprintfSitesWrap
import Vsa.Sim.SnprintfSpec20
import Vsa.Sim.SlotFrame
import Vsa.Sim.PinW
import Vsa.Sim.CodeRangeInsert
import Vsa.Sim.Code.LldFmt

/-!
# M3 Layer-3 — `SnprintfSpec40` : the snprintf wrapper PRE-CALL segment
## `0x80005c44` (snprintf ABI entry) → `0x80007654` (`jal _svfprintf_r` completed)

The WHILE interpreter's `stringify` int arm calls `snprintf(buf, 64, "%lld", v)`
(`0x800030d8`); newlib's `snprintf` (`0x80005c44`) builds the string-sink FILE
struct on its own 272-byte frame and calls `_svfprintf_r` directly (`jal` at
`0x80005cb8`).  This module verifies the 30-instruction pre-call body,
exporting exactly the wrapper-owned inputs of `svfprintf_lld_spec` (Spec38):
the FILE cursor/capacity/`_flags` pins, the spilled va-area value bytes, the
epilogue `SlotHolds`, and the single-window memory frame.

Also hosts the wrapper-shared value lemmas and the `of_agree` code-pin
transports Spec42 uses at the composition seams.

Emitted by `scripts/pro_emitter/gen_spec40.py` (SnprintfSpec27 house style).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Wrapper value lemmas -/

/-- `addi sp,sp,-272` from `vsp + 864` lands on `vsp + 592`. -/
theorem sp_dec272_wr (vsp : BitVec 64) :
    (vsp + (864#64)) + sign_extend (m := 64) (0xef0#12) = vsp + (592#64) := by
  rw [BitVec.add_assoc]
  congr 1

/-- `addi sp,sp,272` from `vsp + 592` restores `vsp + 864`. -/
theorem sp_inc272_wr (vsp : BitVec 64) :
    (vsp + (592#64)) + sign_extend (m := 64) (0x110#12) = vsp + (864#64) := by
  rw [BitVec.add_assoc]
  congr 1

/-- `lui t1,0x80000; not t1,t1` = `INT_MAX`. -/
theorem t1_notmask_wr :
    (sign_extend (m := 64) ((0x80000#20) +++ 0x000#12) : BitVec 64)
      ^^^ sign_extend (m := 64) (0xfff#12) = (0x7fffffff#64) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- `lui a6,0xffff0; addi a6,a6,520` = the `0xffff0208` flags image. -/
theorem a6_flags_wr :
    (sign_extend (m := 64) ((0xffff0#20) +++ 0x000#12) : BitVec 64)
      + sign_extend (m := 64) (0x208#12) = (0xffffffffffff0208#64) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- Introduction form of the `bltu` guard: `a < b` (as `toNat`) ⇒ taken. -/
theorem bltu_of_lt_wr (a b : BitVec 64) (h : a.toNat < b.toNat) :
    zopz0zI_u a b = true := by
  unfold zopz0zI_u; simp only [Sail.BitVec.toNatInt]
  exact decide_eq_true (Int.ofNat_lt.mpr h)

/-- Introduction form of the `bltu` NOT-taken guard: `b ≤ a` ⇒ not taken. -/
theorem bltu_false_of_ge_wr (a b : BitVec 64) (h : b.toNat ≤ a.toNat) :
    zopz0zI_u a b = false := by
  unfold zopz0zI_u; simp only [Sail.BitVec.toNatInt]
  exact decide_eq_false (fun hc => Nat.not_lt.mpr h (Int.ofNat_lt.mp hc))

/-- The `subw a4,a1,a4` capacity value: for `1 ≤ sz < 2^31` and `a4 = 1`,
the sign-extended 32-bit difference is `sz − 1`. -/
theorem subw_cap_wr (sz : BitVec 64) (h1 : 1 ≤ sz.toNat) (h2 : sz.toNat < 2 ^ 31) :
    (sign_extend (m := 64)
      ((Sail.BitVec.extractLsb sz 31 0) - (Sail.BitVec.extractLsb (1#64) 31 0)) : BitVec 64)
      = BitVec.ofNat 64 (sz.toNat - 1) := by
  have hesz : (Sail.BitVec.extractLsb sz 31 0).toNat = sz.toNat := by
    show (BitVec.ofNat (31 - 0 + 1) (sz.toNat >>> 0)).toNat = sz.toNat
    rw [Nat.shiftRight_zero, BitVec.toNat_ofNat]
    have := sz.isLt
    exact Nat.mod_eq_of_lt (by omega)
  rw [show (Sail.BitVec.extractLsb (1#64) 31 0) = (1#32) from by decide]
  have hz : ((Sail.BitVec.extractLsb sz 31 0) - (1#32)).toNat = sz.toNat - 1 := by
    rw [BitVec.toNat_sub, hesz, show ((1#32 : BitVec 32)).toNat = 1 from rfl]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [sext32_toNat_small _ (by omega), hz, BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (by omega)).symm

/-! ## `SnprintfLoaded` write-survival (CodeRangeInsert pattern) -/

theorem snprintf_insert_wr (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (b : BitVec 8)
    (hk : 0x80018000 ≤ k) (h : Vsa.Sim.Code.SnprintfLoaded mem) :
    Vsa.Sim.Code.SnprintfLoaded (mem.insert k b) := by
  unfold Vsa.Sim.Code.SnprintfLoaded at h ⊢
  simp only [Vsa.Sim.Code.snprintfChunk0, Vsa.Sim.Code.snprintfChunk1,
    Vsa.Sim.Code.snprintfChunk2, Vsa.Sim.Code.snprintfChunk3] at h ⊢
  simp (disch := omega) only
    [getElem?_insert_outside 0x80005c44 0x80005d18 mem k b (Or.inr (by omega))]
  exact h

theorem snprintf_w8_wr (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (dw : BitVec (8 * 8))
    (ha : 0x80018000 ≤ a) (h : Vsa.Sim.Code.SnprintfLoaded mem) :
    Vsa.Sim.Code.SnprintfLoaded (writeMap8 mem a dw) :=
  snprintf_insert_wr _ _ _ (by omega) (snprintf_insert_wr _ _ _ (by omega)
    (snprintf_insert_wr _ _ _ (by omega) (snprintf_insert_wr _ _ _ (by omega)
    (snprintf_insert_wr _ _ _ (by omega) (snprintf_insert_wr _ _ _ (by omega)
    (snprintf_insert_wr _ _ _ (by omega) (snprintf_insert_wr _ _ _ (by omega) h)))))))

theorem snprintf_w4_wr (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (dw : BitVec (8 * 4))
    (ha : 0x80018000 ≤ a) (h : Vsa.Sim.Code.SnprintfLoaded mem) :
    Vsa.Sim.Code.SnprintfLoaded (writeMap4 mem a dw) :=
  snprintf_insert_wr _ _ _ (by omega) (snprintf_insert_wr _ _ _ (by omega)
    (snprintf_insert_wr _ _ _ (by omega) (snprintf_insert_wr _ _ _ (by omega) h)))

/-! ## `of_agree` code-pin transports for the composition seams (Spec42)

All from ONE pointwise agreement below `0x8001c000`: every code/static pin the
wrapper chain consumes sits below it, and every memory write in the chain
(snprintf frame ≥ `vsp+592`, svfprintf frame ≥ `vsp−88`, destination ≥ `d`)
sits at/above it under the capstone's layout hypotheses. -/

theorem snprintf_of_agree_wr {m0 mem : Std.ExtHashMap Nat (BitVec 8)}
    (hag : ∀ a, a < 0x8001c000 → mem[a]? = m0[a]?)
    (h : Vsa.Sim.Code.SnprintfLoaded m0) : Vsa.Sim.Code.SnprintfLoaded mem := by
  unfold Vsa.Sim.Code.SnprintfLoaded at h ⊢
  simp only [Vsa.Sim.Code.snprintfChunk0, Vsa.Sim.Code.snprintfChunk1,
    Vsa.Sim.Code.snprintfChunk2, Vsa.Sim.Code.snprintfChunk3] at h ⊢
  simp (disch := omega) only [hag]
  exact h

theorem lldfmt_of_agree_wr {m0 mem : Std.ExtHashMap Nat (BitVec 8)}
    (hag : ∀ a, a < 0x8001c000 → mem[a]? = m0[a]?)
    (h : Vsa.Sim.Code.LldFmtLoaded m0) : Vsa.Sim.Code.LldFmtLoaded mem := by
  unfold Vsa.Sim.Code.LldFmtLoaded Vsa.Sim.Code.lldFmtChunk0 at h ⊢
  simp (disch := omega) only [hag]
  exact h

theorem localeconv_of_agree_wr {m0 mem : Std.ExtHashMap Nat (BitVec 8)}
    (hag : ∀ a, a < 0x8001c000 → mem[a]? = m0[a]?)
    (h : Vsa.Sim.Code._localeconv_rLoaded m0) : Vsa.Sim.Code._localeconv_rLoaded mem := by
  unfold Vsa.Sim.Code._localeconv_rLoaded at h ⊢
  simp only [Vsa.Sim.Code._localeconv_rChunk0] at h ⊢
  simp (disch := omega) only [hag]
  exact h

theorem strlen_of_agree_wr {m0 mem : Std.ExtHashMap Nat (BitVec 8)}
    (hag : ∀ a, a < 0x8001c000 → mem[a]? = m0[a]?)
    (h : Vsa.Sim.Code.StrlenLoaded m0) : Vsa.Sim.Code.StrlenLoaded mem := by
  unfold Vsa.Sim.Code.StrlenLoaded at h ⊢
  simp only [Vsa.Sim.Code.strlenChunk0, Vsa.Sim.Code.strlenChunk1,
    Vsa.Sim.Code.strlenChunk2, Vsa.Sim.Code.strlenChunk3] at h ⊢
  simp (disch := omega) only [hag]
  exact h

theorem memset_of_agree_wr {m0 mem : Std.ExtHashMap Nat (BitVec 8)}
    (hag : ∀ a, a < 0x8001c000 → mem[a]? = m0[a]?)
    (h : Vsa.Sim.Code.MemsetLoaded m0) : Vsa.Sim.Code.MemsetLoaded mem := by
  unfold Vsa.Sim.Code.MemsetLoaded at h ⊢
  simp only [Vsa.Sim.Code.memsetChunk0, Vsa.Sim.Code.memsetChunk1,
    Vsa.Sim.Code.memsetChunk2, Vsa.Sim.Code.memsetChunk3] at h ⊢
  simp (disch := omega) only [hag]
  exact h

theorem ssprint_of_agree_wr {m0 mem : Std.ExtHashMap Nat (BitVec 8)}
    (hag : ∀ a, a < 0x8001c000 → mem[a]? = m0[a]?)
    (h : Vsa.Sim.Code.__ssprint_rLoaded m0) : Vsa.Sim.Code.__ssprint_rLoaded mem := by
  unfold Vsa.Sim.Code.__ssprint_rLoaded at h ⊢
  simp only [Vsa.Sim.Code.__ssprint_rChunk0, Vsa.Sim.Code.__ssprint_rChunk1,
    Vsa.Sim.Code.__ssprint_rChunk2, Vsa.Sim.Code.__ssprint_rChunk3] at h ⊢
  simp (disch := omega) only [hag]
  exact h

theorem ssputs_of_agree_wr {m0 mem : Std.ExtHashMap Nat (BitVec 8)}
    (hag : ∀ a, a < 0x8001c000 → mem[a]? = m0[a]?)
    (h : Vsa.Sim.Code.__ssputs_rLoaded m0) : Vsa.Sim.Code.__ssputs_rLoaded mem := by
  unfold Vsa.Sim.Code.__ssputs_rLoaded at h ⊢
  simp only [Vsa.Sim.Code.__ssputs_rChunk0, Vsa.Sim.Code.__ssputs_rChunk1,
    Vsa.Sim.Code.__ssputs_rChunk2, Vsa.Sim.Code.__ssputs_rChunk3,
    Vsa.Sim.Code.__ssputs_rChunk4, Vsa.Sim.Code.__ssputs_rChunk5,
    Vsa.Sim.Code.__ssputs_rChunk6] at h ⊢
  simp (disch := omega) only [hag]
  exact h

theorem memmove_of_agree_wr {m0 mem : Std.ExtHashMap Nat (BitVec 8)}
    (hag : ∀ a, a < 0x8001c000 → mem[a]? = m0[a]?)
    (h : Vsa.Sim.Code.MemmoveLoaded m0) : Vsa.Sim.Code.MemmoveLoaded mem := by
  unfold Vsa.Sim.Code.MemmoveLoaded at h ⊢
  simp only [Vsa.Sim.Code.memmoveChunk0, Vsa.Sim.Code.memmoveChunk1,
    Vsa.Sim.Code.memmoveChunk2, Vsa.Sim.Code.memmoveChunk3,
    Vsa.Sim.Code.memmoveChunk4] at h ⊢
  simp (disch := omega) only [hag]
  exact h

/-- **The snprintf wrapper PRE-CALL segment**: `0x80005c44 → 0x80007654`.

From the `snprintf(d, sz, fmt, v)` ABI entry (`sp = vsp + 864`, `vsp` =
`_svfprintf_r`'s eventual frame base) through the 30-instruction wrapper body
to the completed `jal _svfprintf_r`: frame allocation, the seven va/save
spills, the `_impure_ptr` reent load, the `INT_MAX` size guard (not taken),
and the on-stack sink FILE struct construction — cursor := `d` (`Pin8`),
capacity := `sz − 1` (`Pin4`), `_flags` := `0x0208` (`__SWR|__SSTR`; bytes
`0x08`/`0x02` exported), the spilled `v` at the va area (`Pin8`), and the
three callee-save slots (`SlotHolds`) the return path reloads. -/
theorem snprintfPreCall_spec
    (vsp wra0 d sz vfmt v : BitVec 64)
    (va4o va5o va6o va7o : BitVec 64)
    (vS0o vS1o vS2o vS3o vS4o vS5o vS6o vS7o vS8o vS9o vS10o vS11o : BitVec 64)
    (c : Config)
    (hG : GoodState c.σ)
    (hsl0 : Vsa.Sim.Code.SnprintfLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x80005c44#64))
    (hx2 : c.σ.regs.get? Register.x2 = some (vsp + (864#64)))
    (hx1 : c.σ.regs.get? Register.x1 = some wra0)
    (hx3 : c.σ.regs.get? Register.x3 = some (0x8001b510#64))
    (hx10 : c.σ.regs.get? Register.x10 = some d)
    (hx11 : c.σ.regs.get? Register.x11 = some sz)
    (hx12 : c.σ.regs.get? Register.x12 = some vfmt)
    (hx13 : c.σ.regs.get? Register.x13 = some v)
    (hx14 : c.σ.regs.get? Register.x14 = some va4o)
    (hx15 : c.σ.regs.get? Register.x15 = some va5o)
    (hx16 : c.σ.regs.get? Register.x16 = some va6o)
    (hx17 : c.σ.regs.get? Register.x17 = some va7o)
    (hx8 : c.σ.regs.get? Register.x8 = some vS0o)
    (hx9 : c.σ.regs.get? Register.x9 = some vS1o)
    (hx18 : c.σ.regs.get? Register.x18 = some vS2o)
    (hx19 : c.σ.regs.get? Register.x19 = some vS3o)
    (hx20 : c.σ.regs.get? Register.x20 = some vS4o)
    (hx21 : c.σ.regs.get? Register.x21 = some vS5o)
    (hx22 : c.σ.regs.get? Register.x22 = some vS6o)
    (hx23 : c.σ.regs.get? Register.x23 = some vS7o)
    (hx24 : c.σ.regs.get? Register.x24 = some vS8o)
    (hx25 : c.σ.regs.get? Register.x25 = some vS9o)
    (hx26 : c.σ.regs.get? Register.x26 = some vS10o)
    (hx27 : c.σ.regs.get? Register.x27 = some vS11o)
    (himp0 : c.σ.mem[(0x8001b970 : Nat)]? = some (0x38#8))
    (himp1 : c.σ.mem[(0x8001b970 : Nat) + 1]? = some (0xb5#8))
    (himp2 : c.σ.mem[(0x8001b970 : Nat) + 2]? = some (0x01#8))
    (himp3 : c.σ.mem[(0x8001b970 : Nat) + 3]? = some (0x80#8))
    (himp4 : c.σ.mem[(0x8001b970 : Nat) + 4]? = some (0x00#8))
    (himp5 : c.σ.mem[(0x8001b970 : Nat) + 5]? = some (0x00#8))
    (himp6 : c.σ.mem[(0x8001b970 : Nat) + 6]? = some (0x00#8))
    (himp7 : c.σ.mem[(0x8001b970 : Nat) + 7]? = some (0x00#8))
    (hsz23 : 23 ≤ sz.toNat)
    (hszhi : sz.toNat < 2 ^ 31)
    (hsplo : 0x8001c100 ≤ vsp.toNat)
    (hsphi : vsp.toNat + 864 ≤ 0x100000000)
    (hspal : vsp.toNat % 8 = 0)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x80007654#64) ∧
      c'.σ.regs.get? Register.x1 = some (0x80005cbc#64) ∧
      c'.σ.regs.get? Register.x2 = some (vsp + (592#64)) ∧
      c'.σ.regs.get? Register.x3 = some (0x8001b510#64) ∧
      c'.σ.regs.get? Register.x8 = some sz ∧
      c'.σ.regs.get? Register.x9 = some (0x8001b538#64) ∧
      c'.σ.regs.get? Register.x10 = some (0x8001b538#64) ∧
      c'.σ.regs.get? Register.x11 = some ((vsp + (592#64)) + sign_extend (m := 64) (0x008#12)) ∧
      c'.σ.regs.get? Register.x12 = some vfmt ∧
      c'.σ.regs.get? Register.x13 = some ((vsp + (592#64)) + sign_extend (m := 64) (0x0e8#12)) ∧
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
      Pin8 c'.σ.mem (vsp.toNat + 600) d ∧
      Pin4 c'.σ.mem (vsp.toNat + 612) (BitVec.ofNat 32 (sz.toNat - 1)) ∧
      c'.σ.mem[vsp.toNat + 616]? = some (0x08#8) ∧
      c'.σ.mem[vsp.toNat + 617]? = some (0x02#8) ∧
      Pin8 c'.σ.mem (vsp.toNat + 824) v ∧
      SlotHolds (vsp + (592#64)) 0x0c8 vS1o c'.σ.mem ∧
      SlotHolds (vsp + (592#64)) 0x0d0 vS0o c'.σ.mem ∧
      SlotHolds (vsp + (592#64)) 0x0d8 wra0 c'.σ.mem ∧
      (∀ a : Nat, ¬(vsp.toNat + 592 ≤ a ∧ a < vsp.toNat + 864) →
        c'.σ.mem[a]? = c.σ.mem[a]?) ∧
      Vsa.Sim.Code.SnprintfLoaded c'.σ.mem ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
  have h592 : ((vsp + (592#64)) : BitVec 64).toNat = vsp.toNat + 592 := by
    rw [BitVec.toNat_add, show ((592#64 : BitVec 64)).toNat = 592 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  have hoff792 : ((vsp + (592#64)) + sign_extend (m := 64) (0x0c8#12)).toNat = vsp.toNat + 792 := by
    rw [ptr_addoff (vsp + (592#64)) _ 200 (by decide) (by rw [h592]; omega), h592]
  have hoff808 : ((vsp + (592#64)) + sign_extend (m := 64) (0x0d8#12)).toNat = vsp.toNat + 808 := by
    rw [ptr_addoff (vsp + (592#64)) _ 216 (by decide) (by rw [h592]; omega), h592]
  have hoff824 : ((vsp + (592#64)) + sign_extend (m := 64) (0x0e8#12)).toNat = vsp.toNat + 824 := by
    rw [ptr_addoff (vsp + (592#64)) _ 232 (by decide) (by rw [h592]; omega), h592]
  have hoff832 : ((vsp + (592#64)) + sign_extend (m := 64) (0x0f0#12)).toNat = vsp.toNat + 832 := by
    rw [ptr_addoff (vsp + (592#64)) _ 240 (by decide) (by rw [h592]; omega), h592]
  have hoff840 : ((vsp + (592#64)) + sign_extend (m := 64) (0x0f8#12)).toNat = vsp.toNat + 840 := by
    rw [ptr_addoff (vsp + (592#64)) _ 248 (by decide) (by rw [h592]; omega), h592]
  have hoff848 : ((vsp + (592#64)) + sign_extend (m := 64) (0x100#12)).toNat = vsp.toNat + 848 := by
    rw [ptr_addoff (vsp + (592#64)) _ 256 (by decide) (by rw [h592]; omega), h592]
  have hoff856 : ((vsp + (592#64)) + sign_extend (m := 64) (0x108#12)).toNat = vsp.toNat + 856 := by
    rw [ptr_addoff (vsp + (592#64)) _ 264 (by decide) (by rw [h592]; omega), h592]
  have hoff800 : ((vsp + (592#64)) + sign_extend (m := 64) (0x0d0#12)).toNat = vsp.toNat + 800 := by
    rw [ptr_addoff (vsp + (592#64)) _ 208 (by decide) (by rw [h592]; omega), h592]
  have hoff600 : ((vsp + (592#64)) + sign_extend (m := 64) (0x008#12)).toNat = vsp.toNat + 600 := by
    rw [ptr_addoff (vsp + (592#64)) _ 8 (by decide) (by rw [h592]; omega), h592]
  have hoff624 : ((vsp + (592#64)) + sign_extend (m := 64) (0x020#12)).toNat = vsp.toNat + 624 := by
    rw [ptr_addoff (vsp + (592#64)) _ 32 (by decide) (by rw [h592]; omega), h592]
  have hoff776 : ((vsp + (592#64)) + sign_extend (m := 64) (0x0b8#12)).toNat = vsp.toNat + 776 := by
    rw [ptr_addoff (vsp + (592#64)) _ 184 (by decide) (by rw [h592]; omega), h592]
  have hoff612 : ((vsp + (592#64)) + sign_extend (m := 64) (0x014#12)).toNat = vsp.toNat + 612 := by
    rw [ptr_addoff (vsp + (592#64)) _ 20 (by decide) (by rw [h592]; omega), h592]
  have hoff632 : ((vsp + (592#64)) + sign_extend (m := 64) (0x028#12)).toNat = vsp.toNat + 632 := by
    rw [ptr_addoff (vsp + (592#64)) _ 40 (by decide) (by rw [h592]; omega), h592]
  have hoff616 : ((vsp + (592#64)) + sign_extend (m := 64) (0x018#12)).toNat = vsp.toNat + 616 := by
    rw [ptr_addoff (vsp + (592#64)) _ 24 (by decide) (by rw [h592]; omega), h592]
  have hoff592 : ((vsp + (592#64)) + sign_extend (m := 64) (0x000#12)).toNat = vsp.toNat + 592 := by
    rw [ptr_addoff (vsp + (592#64)) _ 0 (by decide) (by rw [h592]; omega), h592]
  have hoffimp : ((0x8001b510#64 : BitVec 64) + sign_extend (m := 64) (0x460#12)).toNat = (0x8001b970 : Nat) := by decide
  have hp0 : PinsHold c.σ [⟨Register.x2, vsp + (864#64)⟩, ⟨Register.x1, wra0⟩, ⟨Register.x3, (0x8001b510#64)⟩, ⟨Register.x10, d⟩, ⟨Register.x11, sz⟩, ⟨Register.x12, vfmt⟩, ⟨Register.x13, v⟩, ⟨Register.x14, va4o⟩, ⟨Register.x15, va5o⟩, ⟨Register.x16, va6o⟩, ⟨Register.x17, va7o⟩, ⟨Register.x8, vS0o⟩, ⟨Register.x9, vS1o⟩, ⟨Register.x18, vS2o⟩, ⟨Register.x19, vS3o⟩, ⟨Register.x20, vS4o⟩, ⟨Register.x21, vS5o⟩, ⟨Register.x22, vS6o⟩, ⟨Register.x23, vS7o⟩, ⟨Register.x24, vS8o⟩, ⟨Register.x25, vS9o⟩, ⟨Register.x26, vS10o⟩, ⟨Register.x27, vS11o⟩] :=
    ⟨hx2, hx1, hx3, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17, hx8, hx9, hx18, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, trivial⟩
  -- === 0x80005c44: addi sp,sp,-272 ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80005c44_wp c.σ c.tick c.steps _ vmi0 (vsp + (864#64))
      hG hpc hmi0 hp0.1 hsl0 rfl htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1
  have hpc1 : σ1.regs.get? Register.PC = some (0x80005c48#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x80005c44#64) 4 = (0x80005c48#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hrd1 : σ1.regs.get? Register.x2 = some ((vsp + (592#64))) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sp_dec272_wr vsp] at this
  have hp1 := pins_cons_pro hrd1 (pins_alu hobs1 (by rfl) hp0.2)
  have hmE1 : σ1.mem = c.σ.mem := hmem1
  have hsl1 : Vsa.Sim.Code.SnprintfLoaded σ1.mem := by rw [hmem1]; exact hsl0

  -- === 0x80005c48: lui t1,0x80000 ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80005c48_wp σ1 i1 (c.steps + 1) _ vmi1
      hG1 hpc1 hmi1 hsl1 rfl hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 2⟩ := hs2
  have hpc2 : σ2.regs.get? Register.PC = some (0x80005c4c#64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x80005c48#64) 4 = (0x80005c4c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hrd2 : σ2.regs.get? Register.x6 = some ((sign_extend (m := 64) ((0x80000#20) +++ 0x000#12))) :=
    obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hp2 := pins_cons_pro hrd2 (pins_alu hobs2 (by rfl) hp1)
  have hmE2 : σ2.mem = c.σ.mem := hmem2.trans hmE1
  have hsl2 : Vsa.Sim.Code.SnprintfLoaded σ2.mem := by rw [hmem2]; exact hsl1

  -- === 0x80005c4c: sd -> sp+200 (= vsp+792) ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80005c4c_wp σ2 i2 (c.steps + 2) _ vmi2 (vsp + (592#64)) _
      hG2 hpc2 hmi2 hp2.2.1 hp2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hsl2 rfl (by rw [hoff792]; omega) (by rw [hoff792]; omega) (by rw [hoff792, htoh]; omega) (by rw [hoff792]; omega) hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 2⟩ ⟨σ3, i3, c.steps + 3⟩ := hs3
  have hpc3 : σ3.regs.get? Register.PC = some (0x80005c50#64) := by
    have := obs_store_pc hobs3
    rwa [show BitVec.addInt (0x80005c4c#64) 4 = (0x80005c50#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi3, hmi3⟩ := obs_store_minstret hobs3
  have hp3 := pins_store hobs3 (by rfl) hp2
  have hmE3 : σ3.mem = writeMap8 (c.σ.mem) (vsp.toNat + 792) (sdData_val vS1o) := by
    rw [hmem3, mem_afterNextPC, hmE2, hoff792]
  have hsl3 : Vsa.Sim.Code.SnprintfLoaded σ3.mem := by
    rw [hmem3, mem_afterNextPC]
    exact snprintf_w8_wr _ _ _ (by rw [hoff792]; omega) hsl2

  -- === 0x80005c50: sd -> sp+216 (= vsp+808) ===
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80005c50_wp σ3 i3 (c.steps + 3) _ vmi3 (vsp + (592#64)) _
      hG3 hpc3 hmi3 hp3.2.1 hp3.2.2.1 hsl3 rfl (by rw [hoff808]; omega) (by rw [hoff808]; omega) (by rw [hoff808, htoh]; omega) (by rw [hoff808]; omega) hi3
  have hstep4 : Step ⟨σ3, i3, c.steps + 3⟩ ⟨σ4, i4, c.steps + 4⟩ := hs4
  have hpc4 : σ4.regs.get? Register.PC = some (0x80005c54#64) := by
    have := obs_store_pc hobs4
    rwa [show BitVec.addInt (0x80005c50#64) 4 = (0x80005c54#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi4, hmi4⟩ := obs_store_minstret hobs4
  have hp4 := pins_store hobs4 (by rfl) hp3
  have hmE4 : σ4.mem = writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 792) (sdData_val vS1o)) (vsp.toNat + 808) (sdData_val wra0) := by
    rw [hmem4, mem_afterNextPC, hmE3, hoff808]
  have hsl4 : Vsa.Sim.Code.SnprintfLoaded σ4.mem := by
    rw [hmem4, mem_afterNextPC]
    exact snprintf_w8_wr _ _ _ (by rw [hoff808]; omega) hsl3

  -- === 0x80005c54: sd -> sp+232 (= vsp+824) ===
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80005c54_wp σ4 i4 (c.steps + 4) _ vmi4 (vsp + (592#64)) _
      hG4 hpc4 hmi4 hp4.2.1 hp4.2.2.2.2.2.2.2.1 hsl4 rfl (by rw [hoff824]; omega) (by rw [hoff824]; omega) (by rw [hoff824, htoh]; omega) (by rw [hoff824]; omega) hi4
  have hstep5 : Step ⟨σ4, i4, c.steps + 4⟩ ⟨σ5, i5, c.steps + 5⟩ := hs5
  have hpc5 : σ5.regs.get? Register.PC = some (0x80005c58#64) := by
    have := obs_store_pc hobs5
    rwa [show BitVec.addInt (0x80005c54#64) 4 = (0x80005c58#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi5, hmi5⟩ := obs_store_minstret hobs5
  have hp5 := pins_store hobs5 (by rfl) hp4
  have hmE5 : σ5.mem = writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 792) (sdData_val vS1o)) (vsp.toNat + 808) (sdData_val wra0)) (vsp.toNat + 824) (sdData_val v) := by
    rw [hmem5, mem_afterNextPC, hmE4, hoff824]
  have hsl5 : Vsa.Sim.Code.SnprintfLoaded σ5.mem := by
    rw [hmem5, mem_afterNextPC]
    exact snprintf_w8_wr _ _ _ (by rw [hoff824]; omega) hsl4

  -- === 0x80005c58: sd -> sp+240 (= vsp+832) ===
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_80005c58_wp σ5 i5 (c.steps + 5) _ vmi5 (vsp + (592#64)) _
      hG5 hpc5 hmi5 hp5.2.1 hp5.2.2.2.2.2.2.2.2.1 hsl5 rfl (by rw [hoff832]; omega) (by rw [hoff832]; omega) (by rw [hoff832, htoh]; omega) (by rw [hoff832]; omega) hi5
  have hstep6 : Step ⟨σ5, i5, c.steps + 5⟩ ⟨σ6, i6, c.steps + 6⟩ := hs6
  have hpc6 : σ6.regs.get? Register.PC = some (0x80005c5c#64) := by
    have := obs_store_pc hobs6
    rwa [show BitVec.addInt (0x80005c58#64) 4 = (0x80005c5c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi6, hmi6⟩ := obs_store_minstret hobs6
  have hp6 := pins_store hobs6 (by rfl) hp5
  have hmE6 : σ6.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 792) (sdData_val vS1o)) (vsp.toNat + 808) (sdData_val wra0)) (vsp.toNat + 824) (sdData_val v)) (vsp.toNat + 832) (sdData_val va4o) := by
    rw [hmem6, mem_afterNextPC, hmE5, hoff832]
  have hsl6 : Vsa.Sim.Code.SnprintfLoaded σ6.mem := by
    rw [hmem6, mem_afterNextPC]
    exact snprintf_w8_wr _ _ _ (by rw [hoff832]; omega) hsl5

  -- === 0x80005c5c: sd -> sp+248 (= vsp+840) ===
  obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
    site_80005c5c_wp σ6 i6 (c.steps + 6) _ vmi6 (vsp + (592#64)) _
      hG6 hpc6 hmi6 hp6.2.1 hp6.2.2.2.2.2.2.2.2.2.1 hsl6 rfl (by rw [hoff840]; omega) (by rw [hoff840]; omega) (by rw [hoff840, htoh]; omega) (by rw [hoff840]; omega) hi6
  have hstep7 : Step ⟨σ6, i6, c.steps + 6⟩ ⟨σ7, i7, c.steps + 7⟩ := hs7
  have hpc7 : σ7.regs.get? Register.PC = some (0x80005c60#64) := by
    have := obs_store_pc hobs7
    rwa [show BitVec.addInt (0x80005c5c#64) 4 = (0x80005c60#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi7, hmi7⟩ := obs_store_minstret hobs7
  have hp7 := pins_store hobs7 (by rfl) hp6
  have hmE7 : σ7.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 792) (sdData_val vS1o)) (vsp.toNat + 808) (sdData_val wra0)) (vsp.toNat + 824) (sdData_val v)) (vsp.toNat + 832) (sdData_val va4o)) (vsp.toNat + 840) (sdData_val va5o) := by
    rw [hmem7, mem_afterNextPC, hmE6, hoff840]
  have hsl7 : Vsa.Sim.Code.SnprintfLoaded σ7.mem := by
    rw [hmem7, mem_afterNextPC]
    exact snprintf_w8_wr _ _ _ (by rw [hoff840]; omega) hsl6

  -- === 0x80005c60: sd -> sp+256 (= vsp+848) ===
  obtain ⟨σ8, i8, hs8, hi8, hG8, hmem8, hobs8⟩ :=
    site_80005c60_wp σ7 i7 (c.steps + 7) _ vmi7 (vsp + (592#64)) _
      hG7 hpc7 hmi7 hp7.2.1 hp7.2.2.2.2.2.2.2.2.2.2.1 hsl7 rfl (by rw [hoff848]; omega) (by rw [hoff848]; omega) (by rw [hoff848, htoh]; omega) (by rw [hoff848]; omega) hi7
  have hstep8 : Step ⟨σ7, i7, c.steps + 7⟩ ⟨σ8, i8, c.steps + 8⟩ := hs8
  have hpc8 : σ8.regs.get? Register.PC = some (0x80005c64#64) := by
    have := obs_store_pc hobs8
    rwa [show BitVec.addInt (0x80005c60#64) 4 = (0x80005c64#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi8, hmi8⟩ := obs_store_minstret hobs8
  have hp8 := pins_store hobs8 (by rfl) hp7
  have hmE8 : σ8.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 792) (sdData_val vS1o)) (vsp.toNat + 808) (sdData_val wra0)) (vsp.toNat + 824) (sdData_val v)) (vsp.toNat + 832) (sdData_val va4o)) (vsp.toNat + 840) (sdData_val va5o)) (vsp.toNat + 848) (sdData_val va6o) := by
    rw [hmem8, mem_afterNextPC, hmE7, hoff848]
  have hsl8 : Vsa.Sim.Code.SnprintfLoaded σ8.mem := by
    rw [hmem8, mem_afterNextPC]
    exact snprintf_w8_wr _ _ _ (by rw [hoff848]; omega) hsl7

  -- === 0x80005c64: sd -> sp+264 (= vsp+856) ===
  obtain ⟨σ9, i9, hs9, hi9, hG9, hmem9, hobs9⟩ :=
    site_80005c64_wp σ8 i8 (c.steps + 8) _ vmi8 (vsp + (592#64)) _
      hG8 hpc8 hmi8 hp8.2.1 hp8.2.2.2.2.2.2.2.2.2.2.2.1 hsl8 rfl (by rw [hoff856]; omega) (by rw [hoff856]; omega) (by rw [hoff856, htoh]; omega) (by rw [hoff856]; omega) hi8
  have hstep9 : Step ⟨σ8, i8, c.steps + 8⟩ ⟨σ9, i9, c.steps + 9⟩ := hs9
  have hpc9 : σ9.regs.get? Register.PC = some (0x80005c68#64) := by
    have := obs_store_pc hobs9
    rwa [show BitVec.addInt (0x80005c64#64) 4 = (0x80005c68#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi9, hmi9⟩ := obs_store_minstret hobs9
  have hp9 := pins_store hobs9 (by rfl) hp8
  have hmE9 : σ9.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 792) (sdData_val vS1o)) (vsp.toNat + 808) (sdData_val wra0)) (vsp.toNat + 824) (sdData_val v)) (vsp.toNat + 832) (sdData_val va4o)) (vsp.toNat + 840) (sdData_val va5o)) (vsp.toNat + 848) (sdData_val va6o)) (vsp.toNat + 856) (sdData_val va7o) := by
    rw [hmem9, mem_afterNextPC, hmE8, hoff856]
  have hsl9 : Vsa.Sim.Code.SnprintfLoaded σ9.mem := by
    rw [hmem9, mem_afterNextPC]
    exact snprintf_w8_wr _ _ _ (by rw [hoff856]; omega) hsl8

  -- === 0x80005c68: not t1,t1 — t1 := INT_MAX ===
  obtain ⟨σ10, i10, hs10, hi10, hG10, hmem10, hobs10⟩ :=
    site_80005c68_wp σ9 i9 (c.steps + 9) _ vmi9 (sign_extend (m := 64) ((0x80000#20) +++ 0x000#12))
      hG9 hpc9 hmi9 hp9.1 hsl9 rfl hi9
  have hstep10 : Step ⟨σ9, i9, c.steps + 9⟩ ⟨σ10, i10, c.steps + 10⟩ := hs10
  have hpc10 : σ10.regs.get? Register.PC = some (0x80005c6c#64) := by
    have := obs_alu_pc hobs10
    rwa [show BitVec.addInt (0x80005c68#64) 4 = (0x80005c6c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi10, hmi10⟩ := obs_alu_minstret hobs10
  have hrd10 : σ10.regs.get? Register.x6 = some ((0x7fffffff#64)) := by
    have := obs_alu_rd hobs10 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [t1_notmask_wr] at this
  have hp10 := pins_cons_pro hrd10 (pins_alu hobs10 (by rfl) hp9.2)
  have hmE10 : σ10.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 792) (sdData_val vS1o)) (vsp.toNat + 808) (sdData_val wra0)) (vsp.toNat + 824) (sdData_val v)) (vsp.toNat + 832) (sdData_val va4o)) (vsp.toNat + 840) (sdData_val va5o)) (vsp.toNat + 848) (sdData_val va6o)) (vsp.toNat + 856) (sdData_val va7o) := hmem10.trans hmE9
  have hsl10 : Vsa.Sim.Code.SnprintfLoaded σ10.mem := by rw [hmem10]; exact hsl9

  -- agreement below the frame after the seven spills (all keys ≥ vsp+592)
  have hag10 : ∀ a : Nat, a < vsp.toNat + 592 → σ10.mem[a]? = c.σ.mem[a]? := by
    intro a ha
    rw [hmE10,
      getElem?_writeMap8_out _ (vsp.toNat + 856) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 848) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 840) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 832) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 824) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 808) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 792) _ a (by omega)]

  -- === 0x80005c6c: ld s1,1120(gp) — s1 := *_impure_ptr = 0x8001b538 ===
  obtain ⟨σ11, i11, hs11, hi11, hG11, hmem11, hobs11⟩ :=
    site_80005c6c_wp σ10 i10 (c.steps + 10) _ vmi10 (0x8001b510#64) (0x38#8) (0xb5#8) (0x01#8) (0x80#8) (0x00#8) (0x00#8) (0x00#8) (0x00#8)
      hG10 hpc10 hmi10 hp10.2.2.2.1 hsl10 rfl (by rw [hoffimp]; omega) (by rw [hoffimp]; omega) (by rw [hoffimp, htoh]; omega) (by rw [hoffimp]) (by rw [hoffimp]; exact (hag10 _ (by omega)).trans himp0) (by rw [hoffimp]; exact (hag10 _ (by omega)).trans himp1) (by rw [hoffimp]; exact (hag10 _ (by omega)).trans himp2) (by rw [hoffimp]; exact (hag10 _ (by omega)).trans himp3) (by rw [hoffimp]; exact (hag10 _ (by omega)).trans himp4) (by rw [hoffimp]; exact (hag10 _ (by omega)).trans himp5) (by rw [hoffimp]; exact (hag10 _ (by omega)).trans himp6) (by rw [hoffimp]; exact (hag10 _ (by omega)).trans himp7) hi10
  have hstep11 : Step ⟨σ10, i10, c.steps + 10⟩ ⟨σ11, i11, c.steps + 11⟩ := hs11
  have hpc11 : σ11.regs.get? Register.PC = some (0x80005c70#64) := by
    have := obs_alu_pc hobs11
    rwa [show BitVec.addInt (0x80005c6c#64) 4 = (0x80005c70#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi11, hmi11⟩ := obs_alu_minstret hobs11
  have hrd11 : σ11.regs.get? Register.x9 = some ((0x8001b538#64)) := by
    have := obs_alu_rd hobs11 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (sign_extend (m := 64) ((((((((0x00#8).append (0x00#8)).append (0x00#8)).append (0x00#8)).append (0x80#8)).append (0x01#8)).append (0xb5#8)).append (0x38#8) : BitVec (8 * 8)) : BitVec 64) = (0x8001b538#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp11 := pins_cons_pro hrd11 (pins_alu hobs11 (by rfl) (pins_drop14_pro hp10))
  have hmE11 : σ11.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 792) (sdData_val vS1o)) (vsp.toNat + 808) (sdData_val wra0)) (vsp.toNat + 824) (sdData_val v)) (vsp.toNat + 832) (sdData_val va4o)) (vsp.toNat + 840) (sdData_val va5o)) (vsp.toNat + 848) (sdData_val va6o)) (vsp.toNat + 856) (sdData_val va7o) := hmem11.trans hmE10
  have hsl11 : Vsa.Sim.Code.SnprintfLoaded σ11.mem := by rw [hmem11]; exact hsl10

  -- === 0x80005c70: bltu t1,a1 — NOT taken (sz ≤ INT_MAX) ===
  have hgu12 : zopz0zI_u (0x7fffffff#64) sz = false := bltu_false_of_ge_wr _ _ (by rw [show ((0x7fffffff#64 : BitVec 64)).toNat = 0x7fffffff from rfl]; omega)
  obtain ⟨σ12, i12, hs12, hi12, hG12, hmem12, hobs12⟩ :=
    site_80005c70_nottaken_wp σ11 i11 (c.steps + 11) _ vmi11 (0x7fffffff#64) sz
      hG11 hpc11 hmi11 hp11.2.1 hp11.2.2.2.2.2.2.1 hsl11 rfl hgu12 hi11
  have hstep12 : Step ⟨σ11, i11, c.steps + 11⟩ ⟨σ12, i12, c.steps + 12⟩ := hs12
  have hpc12 : σ12.regs.get? Register.PC = some (0x80005c74#64) := by
    have := obs_bnottaken_pc hobs12
    rwa [show BitVec.addInt (0x80005c70#64) 4 = (0x80005c74#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi12, hmi12⟩ := obs_bnottaken_minstret hobs12
  have hp12 := pins_bnottaken hobs12 (by rfl) hp11
  have hmE12 : σ12.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 792) (sdData_val vS1o)) (vsp.toNat + 808) (sdData_val wra0)) (vsp.toNat + 824) (sdData_val v)) (vsp.toNat + 832) (sdData_val va4o)) (vsp.toNat + 840) (sdData_val va5o)) (vsp.toNat + 848) (sdData_val va6o)) (vsp.toNat + 856) (sdData_val va7o) := hmem12.trans hmE11
  have hsl12 : Vsa.Sim.Code.SnprintfLoaded σ12.mem := by rw [hmem12]; exact hsl11

  -- === 0x80005c74: snez a4,a1 — a4 := 1 (sz ≠ 0) ===
  have hnz13 : zopz0zI_u (0#64) sz = true := bltu_of_lt_wr _ _ (by simp only [BitVec.toNat_ofNat]; omega)
  obtain ⟨σ13, i13, hs13, hi13, hG13, hmem13, hobs13⟩ :=
    site_80005c74_wp σ12 i12 (c.steps + 12) _ vmi12 sz
      hG12 hpc12 hmi12 hp12.2.2.2.2.2.2.1 hsl12 rfl hi12
  have hstep13 : Step ⟨σ12, i12, c.steps + 12⟩ ⟨σ13, i13, c.steps + 13⟩ := hs13
  have hpc13 : σ13.regs.get? Register.PC = some (0x80005c78#64) := by
    have := obs_alu_pc hobs13
    rwa [show BitVec.addInt (0x80005c74#64) 4 = (0x80005c78#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi13, hmi13⟩ := obs_alu_minstret hobs13
  have hrd13 : σ13.regs.get? Register.x14 = some ((1#64)) := by
    have := obs_alu_rd hobs13 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) sz)) = (1#64) from by rw [hnz13]; decide] at this
  have hp13 := pins_cons_pro hrd13 (pins_alu hobs13 (by rfl) (pins_drop10_pro hp12))
  have hmE13 : σ13.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 792) (sdData_val vS1o)) (vsp.toNat + 808) (sdData_val wra0)) (vsp.toNat + 824) (sdData_val v)) (vsp.toNat + 832) (sdData_val va4o)) (vsp.toNat + 840) (sdData_val va5o)) (vsp.toNat + 848) (sdData_val va6o)) (vsp.toNat + 856) (sdData_val va7o) := hmem13.trans hmE12
  have hsl13 : Vsa.Sim.Code.SnprintfLoaded σ13.mem := by rw [hmem13]; exact hsl12

  -- === 0x80005c78: lui a6,0xffff0 ===
  obtain ⟨σ14, i14, hs14, hi14, hG14, hmem14, hobs14⟩ :=
    site_80005c78_wp σ13 i13 (c.steps + 13) _ vmi13
      hG13 hpc13 hmi13 hsl13 rfl hi13
  have hstep14 : Step ⟨σ13, i13, c.steps + 13⟩ ⟨σ14, i14, c.steps + 14⟩ := hs14
  have hpc14 : σ14.regs.get? Register.PC = some (0x80005c7c#64) := by
    have := obs_alu_pc hobs14
    rwa [show BitVec.addInt (0x80005c78#64) 4 = (0x80005c7c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi14, hmi14⟩ := obs_alu_minstret hobs14
  have hrd14 : σ14.regs.get? Register.x16 = some ((sign_extend (m := 64) ((0xffff0#20) +++ 0x000#12))) :=
    obs_alu_rd hobs14 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hp14 := pins_cons_pro hrd14 (pins_alu hobs14 (by rfl) (pins_drop12_pro hp13))
  have hmE14 : σ14.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 792) (sdData_val vS1o)) (vsp.toNat + 808) (sdData_val wra0)) (vsp.toNat + 824) (sdData_val v)) (vsp.toNat + 832) (sdData_val va4o)) (vsp.toNat + 840) (sdData_val va5o)) (vsp.toNat + 848) (sdData_val va6o)) (vsp.toNat + 856) (sdData_val va7o) := hmem14.trans hmE13
  have hsl14 : Vsa.Sim.Code.SnprintfLoaded σ14.mem := by rw [hmem14]; exact hsl13

  -- === 0x80005c7c: mv a5,a0 — a5 := d ===
  obtain ⟨σ15, i15, hs15, hi15, hG15, hmem15, hobs15⟩ :=
    site_80005c7c_wp σ14 i14 (c.steps + 14) _ vmi14 d
      hG14 hpc14 hmi14 hp14.2.2.2.2.2.2.2.1 hsl14 rfl hi14
  have hstep15 : Step ⟨σ14, i14, c.steps + 14⟩ ⟨σ15, i15, c.steps + 15⟩ := hs15
  have hpc15 : σ15.regs.get? Register.PC = some (0x80005c80#64) := by
    have := obs_alu_pc hobs15
    rwa [show BitVec.addInt (0x80005c7c#64) 4 = (0x80005c80#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi15, hmi15⟩ := obs_alu_minstret hobs15
  have hrd15 : σ15.regs.get? Register.x15 = some (d) := by
    have := obs_alu_rd hobs15 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add_pro d] at this
  have hp15 := pins_cons_pro hrd15 (pins_alu hobs15 (by rfl) (pins_drop12_pro hp14))
  have hmE15 : σ15.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 792) (sdData_val vS1o)) (vsp.toNat + 808) (sdData_val wra0)) (vsp.toNat + 824) (sdData_val v)) (vsp.toNat + 832) (sdData_val va4o)) (vsp.toNat + 840) (sdData_val va5o)) (vsp.toNat + 848) (sdData_val va6o)) (vsp.toNat + 856) (sdData_val va7o) := hmem15.trans hmE14
  have hsl15 : Vsa.Sim.Code.SnprintfLoaded σ15.mem := by rw [hmem15]; exact hsl14

  -- === 0x80005c80: subw a4,a1,a4 — a4 := sz-1 ===
  obtain ⟨σ16, i16, hs16, hi16, hG16, hmem16, hobs16⟩ :=
    site_80005c80_wp σ15 i15 (c.steps + 15) _ vmi15 sz (1#64)
      hG15 hpc15 hmi15 hp15.2.2.2.2.2.2.2.2.2.1 hp15.2.2.1 hsl15 rfl hi15
  have hstep16 : Step ⟨σ15, i15, c.steps + 15⟩ ⟨σ16, i16, c.steps + 16⟩ := hs16
  have hpc16 : σ16.regs.get? Register.PC = some (0x80005c84#64) := by
    have := obs_alu_pc hobs16
    rwa [show BitVec.addInt (0x80005c80#64) 4 = (0x80005c84#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi16, hmi16⟩ := obs_alu_minstret hobs16
  have hrd16 : σ16.regs.get? Register.x14 = some ((BitVec.ofNat 64 (sz.toNat - 1))) := by
    have := obs_alu_rd hobs16 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [subw_cap_wr sz (by omega) hszhi] at this
  have hp16 := pins_cons_pro hrd16 (pins_alu hobs16 (by rfl) (pins_drop3_pro hp15))
  have hmE16 : σ16.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 792) (sdData_val vS1o)) (vsp.toNat + 808) (sdData_val wra0)) (vsp.toNat + 824) (sdData_val v)) (vsp.toNat + 832) (sdData_val va4o)) (vsp.toNat + 840) (sdData_val va5o)) (vsp.toNat + 848) (sdData_val va6o)) (vsp.toNat + 856) (sdData_val va7o) := hmem16.trans hmE15
  have hsl16 : Vsa.Sim.Code.SnprintfLoaded σ16.mem := by rw [hmem16]; exact hsl15

  -- === 0x80005c84: sd s0,208(sp) (= vsp+800) ===
  obtain ⟨σ17, i17, hs17, hi17, hG17, hmem17, hobs17⟩ :=
    site_80005c84_wp σ16 i16 (c.steps + 16) _ vmi16 (vsp + (592#64)) _
      hG16 hpc16 hmi16 hp16.2.2.2.2.2.1 hp16.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hsl16 rfl (by rw [hoff800]; omega) (by rw [hoff800]; omega) (by rw [hoff800, htoh]; omega) (by rw [hoff800]; omega) hi16
  have hstep17 : Step ⟨σ16, i16, c.steps + 16⟩ ⟨σ17, i17, c.steps + 17⟩ := hs17
  have hpc17 : σ17.regs.get? Register.PC = some (0x80005c88#64) := by
    have := obs_store_pc hobs17
    rwa [show BitVec.addInt (0x80005c84#64) 4 = (0x80005c88#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi17, hmi17⟩ := obs_store_minstret hobs17
  have hp17 := pins_store hobs17 (by rfl) hp16
  have hmE17 : σ17.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 792) (sdData_val vS1o)) (vsp.toNat + 808) (sdData_val wra0)) (vsp.toNat + 824) (sdData_val v)) (vsp.toNat + 832) (sdData_val va4o)) (vsp.toNat + 840) (sdData_val va5o)) (vsp.toNat + 848) (sdData_val va6o)) (vsp.toNat + 856) (sdData_val va7o)) (vsp.toNat + 800) (sdData_val vS0o) := by
    rw [hmem17, mem_afterNextPC, hmE16, hoff800]
  have hsl17 : Vsa.Sim.Code.SnprintfLoaded σ17.mem := by
    rw [hmem17, mem_afterNextPC]
    exact snprintf_w8_wr _ _ _ (by rw [hoff800]; omega) hsl16

  -- === 0x80005c88: addi a3,sp,232 — the va_list pointer ===
  obtain ⟨σ18, i18, hs18, hi18, hG18, hmem18, hobs18⟩ :=
    site_80005c88_wp σ17 i17 (c.steps + 17) _ vmi17 (vsp + (592#64))
      hG17 hpc17 hmi17 hp17.2.2.2.2.2.1 hsl17 rfl hi17
  have hstep18 : Step ⟨σ17, i17, c.steps + 17⟩ ⟨σ18, i18, c.steps + 18⟩ := hs18
  have hpc18 : σ18.regs.get? Register.PC = some (0x80005c8c#64) := by
    have := obs_alu_pc hobs18
    rwa [show BitVec.addInt (0x80005c88#64) 4 = (0x80005c8c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi18, hmi18⟩ := obs_alu_minstret hobs18
  have hrd18 : σ18.regs.get? Register.x13 = some (((vsp + (592#64)) + sign_extend (m := 64) (0x0e8#12))) :=
    obs_alu_rd hobs18 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hp18 := pins_cons_pro hrd18 (pins_alu hobs18 (by rfl) (pins_drop12_pro hp17))
  have hmE18 : σ18.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 792) (sdData_val vS1o)) (vsp.toNat + 808) (sdData_val wra0)) (vsp.toNat + 824) (sdData_val v)) (vsp.toNat + 832) (sdData_val va4o)) (vsp.toNat + 840) (sdData_val va5o)) (vsp.toNat + 848) (sdData_val va6o)) (vsp.toNat + 856) (sdData_val va7o)) (vsp.toNat + 800) (sdData_val vS0o) := hmem18.trans hmE17
  have hsl18 : Vsa.Sim.Code.SnprintfLoaded σ18.mem := by rw [hmem18]; exact hsl17

  -- === 0x80005c8c: addi a6,a6,520 — the __SWR|__SSTR flags image ===
  obtain ⟨σ19, i19, hs19, hi19, hG19, hmem19, hobs19⟩ :=
    site_80005c8c_wp σ18 i18 (c.steps + 18) _ vmi18 (sign_extend (m := 64) ((0xffff0#20) +++ 0x000#12))
      hG18 hpc18 hmi18 hp18.2.2.2.1 hsl18 rfl hi18
  have hstep19 : Step ⟨σ18, i18, c.steps + 18⟩ ⟨σ19, i19, c.steps + 19⟩ := hs19
  have hpc19 : σ19.regs.get? Register.PC = some (0x80005c90#64) := by
    have := obs_alu_pc hobs19
    rwa [show BitVec.addInt (0x80005c8c#64) 4 = (0x80005c90#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi19, hmi19⟩ := obs_alu_minstret hobs19
  have hrd19 : σ19.regs.get? Register.x16 = some ((0xffffffffffff0208#64)) := by
    have := obs_alu_rd hobs19 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [a6_flags_wr] at this
  have hp19 := pins_cons_pro hrd19 (pins_alu hobs19 (by rfl) (pins_drop4_pro hp18))
  have hmE19 : σ19.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 792) (sdData_val vS1o)) (vsp.toNat + 808) (sdData_val wra0)) (vsp.toNat + 824) (sdData_val v)) (vsp.toNat + 832) (sdData_val va4o)) (vsp.toNat + 840) (sdData_val va5o)) (vsp.toNat + 848) (sdData_val va6o)) (vsp.toNat + 856) (sdData_val va7o)) (vsp.toNat + 800) (sdData_val vS0o) := hmem19.trans hmE18
  have hsl19 : Vsa.Sim.Code.SnprintfLoaded σ19.mem := by rw [hmem19]; exact hsl18

  -- === 0x80005c90: mv s0,a1 — s0 := sz ===
  obtain ⟨σ20, i20, hs20, hi20, hG20, hmem20, hobs20⟩ :=
    site_80005c90_wp σ19 i19 (c.steps + 19) _ vmi19 sz
      hG19 hpc19 hmi19 hp19.2.2.2.2.2.2.2.2.2.2.1 hsl19 rfl hi19
  have hstep20 : Step ⟨σ19, i19, c.steps + 19⟩ ⟨σ20, i20, c.steps + 20⟩ := hs20
  have hpc20 : σ20.regs.get? Register.PC = some (0x80005c94#64) := by
    have := obs_alu_pc hobs20
    rwa [show BitVec.addInt (0x80005c90#64) 4 = (0x80005c94#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi20, hmi20⟩ := obs_alu_minstret hobs20
  have hrd20 : σ20.regs.get? Register.x8 = some (sz) := by
    have := obs_alu_rd hobs20 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add_pro sz] at this
  have hp20 := pins_cons_pro hrd20 (pins_alu hobs20 (by rfl) (pins_drop14_pro hp19))
  have hmE20 : σ20.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 792) (sdData_val vS1o)) (vsp.toNat + 808) (sdData_val wra0)) (vsp.toNat + 824) (sdData_val v)) (vsp.toNat + 832) (sdData_val va4o)) (vsp.toNat + 840) (sdData_val va5o)) (vsp.toNat + 848) (sdData_val va6o)) (vsp.toNat + 856) (sdData_val va7o)) (vsp.toNat + 800) (sdData_val vS0o) := hmem20.trans hmE19
  have hsl20 : Vsa.Sim.Code.SnprintfLoaded σ20.mem := by rw [hmem20]; exact hsl19

  -- === 0x80005c94: mv a0,s1 — a0 := the reent ===
  obtain ⟨σ21, i21, hs21, hi21, hG21, hmem21, hobs21⟩ :=
    site_80005c94_wp σ20 i20 (c.steps + 20) _ vmi20 (0x8001b538#64)
      hG20 hpc20 hmi20 hp20.2.2.2.2.2.1 hsl20 rfl hi20
  have hstep21 : Step ⟨σ20, i20, c.steps + 20⟩ ⟨σ21, i21, c.steps + 21⟩ := hs21
  have hpc21 : σ21.regs.get? Register.PC = some (0x80005c98#64) := by
    have := obs_alu_pc hobs21
    rwa [show BitVec.addInt (0x80005c94#64) 4 = (0x80005c98#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi21, hmi21⟩ := obs_alu_minstret hobs21
  have hrd21 : σ21.regs.get? Register.x10 = some ((0x8001b538#64)) := by
    have := obs_alu_rd hobs21 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add_pro (0x8001b538#64)] at this
  have hp21 := pins_cons_pro hrd21 (pins_alu hobs21 (by rfl) (pins_drop11_pro hp20))
  have hmE21 : σ21.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 792) (sdData_val vS1o)) (vsp.toNat + 808) (sdData_val wra0)) (vsp.toNat + 824) (sdData_val v)) (vsp.toNat + 832) (sdData_val va4o)) (vsp.toNat + 840) (sdData_val va5o)) (vsp.toNat + 848) (sdData_val va6o)) (vsp.toNat + 856) (sdData_val va7o)) (vsp.toNat + 800) (sdData_val vS0o) := hmem21.trans hmE20
  have hsl21 : Vsa.Sim.Code.SnprintfLoaded σ21.mem := by rw [hmem21]; exact hsl20

  -- === 0x80005c98: addi a1,sp,8 — the sink FILE pointer ===
  obtain ⟨σ22, i22, hs22, hi22, hG22, hmem22, hobs22⟩ :=
    site_80005c98_wp σ21 i21 (c.steps + 21) _ vmi21 (vsp + (592#64))
      hG21 hpc21 hmi21 hp21.2.2.2.2.2.2.2.2.1 hsl21 rfl hi21
  have hstep22 : Step ⟨σ21, i21, c.steps + 21⟩ ⟨σ22, i22, c.steps + 22⟩ := hs22
  have hpc22 : σ22.regs.get? Register.PC = some (0x80005c9c#64) := by
    have := obs_alu_pc hobs22
    rwa [show BitVec.addInt (0x80005c98#64) 4 = (0x80005c9c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi22, hmi22⟩ := obs_alu_minstret hobs22
  have hrd22 : σ22.regs.get? Register.x11 = some (((vsp + (592#64)) + sign_extend (m := 64) (0x008#12))) :=
    obs_alu_rd hobs22 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hp22 := pins_cons_pro hrd22 (pins_alu hobs22 (by rfl) (pins_drop12_pro hp21))
  have hmE22 : σ22.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 792) (sdData_val vS1o)) (vsp.toNat + 808) (sdData_val wra0)) (vsp.toNat + 824) (sdData_val v)) (vsp.toNat + 832) (sdData_val va4o)) (vsp.toNat + 840) (sdData_val va5o)) (vsp.toNat + 848) (sdData_val va6o)) (vsp.toNat + 856) (sdData_val va7o)) (vsp.toNat + 800) (sdData_val vS0o) := hmem22.trans hmE21
  have hsl22 : Vsa.Sim.Code.SnprintfLoaded σ22.mem := by rw [hmem22]; exact hsl21

  -- === 0x80005c9c: sd a5 -> sp+8: FILE cursor := d ===
  obtain ⟨σ23, i23, hs23, hi23, hG23, hmem23, hobs23⟩ :=
    site_80005c9c_wp σ22 i22 (c.steps + 22) _ vmi22 (vsp + (592#64)) _
      hG22 hpc22 hmi22 hp22.2.2.2.2.2.2.2.2.2.1 hp22.2.2.2.2.2.2.1 hsl22 rfl (by rw [hoff600]; omega) (by rw [hoff600]; omega) (by rw [hoff600, htoh]; omega) (by rw [hoff600]; omega) hi22
  have hstep23 : Step ⟨σ22, i22, c.steps + 22⟩ ⟨σ23, i23, c.steps + 23⟩ := hs23
  have hpc23 : σ23.regs.get? Register.PC = some (0x80005ca0#64) := by
    have := obs_store_pc hobs23
    rwa [show BitVec.addInt (0x80005c9c#64) 4 = (0x80005ca0#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi23, hmi23⟩ := obs_store_minstret hobs23
  have hp23 := pins_store hobs23 (by rfl) hp22
  have hmE23 : σ23.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 792) (sdData_val vS1o)) (vsp.toNat + 808) (sdData_val wra0)) (vsp.toNat + 824) (sdData_val v)) (vsp.toNat + 832) (sdData_val va4o)) (vsp.toNat + 840) (sdData_val va5o)) (vsp.toNat + 848) (sdData_val va6o)) (vsp.toNat + 856) (sdData_val va7o)) (vsp.toNat + 800) (sdData_val vS0o)) (vsp.toNat + 600) (sdData_val d) := by
    rw [hmem23, mem_afterNextPC, hmE22, hoff600]
  have hsl23 : Vsa.Sim.Code.SnprintfLoaded σ23.mem := by
    rw [hmem23, mem_afterNextPC]
    exact snprintf_w8_wr _ _ _ (by rw [hoff600]; omega) hsl22

  -- === 0x80005ca0: sd a5 -> sp+32: FILE _bf._base := d ===
  obtain ⟨σ24, i24, hs24, hi24, hG24, hmem24, hobs24⟩ :=
    site_80005ca0_wp σ23 i23 (c.steps + 23) _ vmi23 (vsp + (592#64)) _
      hG23 hpc23 hmi23 hp23.2.2.2.2.2.2.2.2.2.1 hp23.2.2.2.2.2.2.1 hsl23 rfl (by rw [hoff624]; omega) (by rw [hoff624]; omega) (by rw [hoff624, htoh]; omega) (by rw [hoff624]; omega) hi23
  have hstep24 : Step ⟨σ23, i23, c.steps + 23⟩ ⟨σ24, i24, c.steps + 24⟩ := hs24
  have hpc24 : σ24.regs.get? Register.PC = some (0x80005ca4#64) := by
    have := obs_store_pc hobs24
    rwa [show BitVec.addInt (0x80005ca0#64) 4 = (0x80005ca4#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi24, hmi24⟩ := obs_store_minstret hobs24
  have hp24 := pins_store hobs24 (by rfl) hp23
  have hmE24 : σ24.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 792) (sdData_val vS1o)) (vsp.toNat + 808) (sdData_val wra0)) (vsp.toNat + 824) (sdData_val v)) (vsp.toNat + 832) (sdData_val va4o)) (vsp.toNat + 840) (sdData_val va5o)) (vsp.toNat + 848) (sdData_val va6o)) (vsp.toNat + 856) (sdData_val va7o)) (vsp.toNat + 800) (sdData_val vS0o)) (vsp.toNat + 600) (sdData_val d)) (vsp.toNat + 624) (sdData_val d) := by
    rw [hmem24, mem_afterNextPC, hmE23, hoff624]
  have hsl24 : Vsa.Sim.Code.SnprintfLoaded σ24.mem := by
    rw [hmem24, mem_afterNextPC]
    exact snprintf_w8_wr _ _ _ (by rw [hoff624]; omega) hsl23

  -- === 0x80005ca4: sw zero,184(sp) ===
  obtain ⟨σ25, i25, hs25, hi25, hG25, hmem25, hobs25⟩ :=
    site_80005ca4_wp σ24 i24 (c.steps + 24) _ vmi24 (vsp + (592#64))
      hG24 hpc24 hmi24 hp24.2.2.2.2.2.2.2.2.2.1 hsl24 rfl (by rw [hoff776]; omega) (by rw [hoff776]; omega) (by rw [hoff776, htoh]; omega) (by rw [hoff776]; omega) hi24
  have hstep25 : Step ⟨σ24, i24, c.steps + 24⟩ ⟨σ25, i25, c.steps + 25⟩ := hs25
  have hpc25 : σ25.regs.get? Register.PC = some (0x80005ca8#64) := by
    have := obs_store_pc hobs25
    rwa [show BitVec.addInt (0x80005ca4#64) 4 = (0x80005ca8#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi25, hmi25⟩ := obs_store_minstret hobs25
  have hp25 := pins_store hobs25 (by rfl) hp24
  have hmE25 : σ25.mem = writeMap4 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 792) (sdData_val vS1o)) (vsp.toNat + 808) (sdData_val wra0)) (vsp.toNat + 824) (sdData_val v)) (vsp.toNat + 832) (sdData_val va4o)) (vsp.toNat + 840) (sdData_val va5o)) (vsp.toNat + 848) (sdData_val va6o)) (vsp.toNat + 856) (sdData_val va7o)) (vsp.toNat + 800) (sdData_val vS0o)) (vsp.toNat + 600) (sdData_val d)) (vsp.toNat + 624) (sdData_val d)) (vsp.toNat + 776) (swData (0#64)) := by
    rw [hmem25, mem_afterNextPC, hmE24, hoff776]
  have hsl25 : Vsa.Sim.Code.SnprintfLoaded σ25.mem := by
    rw [hmem25, mem_afterNextPC]
    exact snprintf_w4_wr _ _ _ (by rw [hoff776]; omega) hsl24

  -- === 0x80005ca8: sw a4 -> sp+20: FILE capacity := sz-1 ===
  obtain ⟨σ26, i26, hs26, hi26, hG26, hmem26, hobs26⟩ :=
    site_80005ca8_wp σ25 i25 (c.steps + 25) _ vmi25 (vsp + (592#64)) _
      hG25 hpc25 hmi25 hp25.2.2.2.2.2.2.2.2.2.1 hp25.2.2.2.2.2.1 hsl25 rfl (by rw [hoff612]; omega) (by rw [hoff612]; omega) (by rw [hoff612, htoh]; omega) (by rw [hoff612]; omega) hi25
  have hstep26 : Step ⟨σ25, i25, c.steps + 25⟩ ⟨σ26, i26, c.steps + 26⟩ := hs26
  have hpc26 : σ26.regs.get? Register.PC = some (0x80005cac#64) := by
    have := obs_store_pc hobs26
    rwa [show BitVec.addInt (0x80005ca8#64) 4 = (0x80005cac#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi26, hmi26⟩ := obs_store_minstret hobs26
  have hp26 := pins_store hobs26 (by rfl) hp25
  have hmE26 : σ26.mem = writeMap4 (writeMap4 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 792) (sdData_val vS1o)) (vsp.toNat + 808) (sdData_val wra0)) (vsp.toNat + 824) (sdData_val v)) (vsp.toNat + 832) (sdData_val va4o)) (vsp.toNat + 840) (sdData_val va5o)) (vsp.toNat + 848) (sdData_val va6o)) (vsp.toNat + 856) (sdData_val va7o)) (vsp.toNat + 800) (sdData_val vS0o)) (vsp.toNat + 600) (sdData_val d)) (vsp.toNat + 624) (sdData_val d)) (vsp.toNat + 776) (swData (0#64))) (vsp.toNat + 612) (swData (BitVec.ofNat 64 (sz.toNat - 1))) := by
    rw [hmem26, mem_afterNextPC, hmE25, hoff612]
  have hsl26 : Vsa.Sim.Code.SnprintfLoaded σ26.mem := by
    rw [hmem26, mem_afterNextPC]
    exact snprintf_w4_wr _ _ _ (by rw [hoff612]; omega) hsl25

  -- === 0x80005cac: sw a4 -> sp+40: FILE _bf._size := sz-1 ===
  obtain ⟨σ27, i27, hs27, hi27, hG27, hmem27, hobs27⟩ :=
    site_80005cac_wp σ26 i26 (c.steps + 26) _ vmi26 (vsp + (592#64)) _
      hG26 hpc26 hmi26 hp26.2.2.2.2.2.2.2.2.2.1 hp26.2.2.2.2.2.1 hsl26 rfl (by rw [hoff632]; omega) (by rw [hoff632]; omega) (by rw [hoff632, htoh]; omega) (by rw [hoff632]; omega) hi26
  have hstep27 : Step ⟨σ26, i26, c.steps + 26⟩ ⟨σ27, i27, c.steps + 27⟩ := hs27
  have hpc27 : σ27.regs.get? Register.PC = some (0x80005cb0#64) := by
    have := obs_store_pc hobs27
    rwa [show BitVec.addInt (0x80005cac#64) 4 = (0x80005cb0#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi27, hmi27⟩ := obs_store_minstret hobs27
  have hp27 := pins_store hobs27 (by rfl) hp26
  have hmE27 : σ27.mem = writeMap4 (writeMap4 (writeMap4 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 792) (sdData_val vS1o)) (vsp.toNat + 808) (sdData_val wra0)) (vsp.toNat + 824) (sdData_val v)) (vsp.toNat + 832) (sdData_val va4o)) (vsp.toNat + 840) (sdData_val va5o)) (vsp.toNat + 848) (sdData_val va6o)) (vsp.toNat + 856) (sdData_val va7o)) (vsp.toNat + 800) (sdData_val vS0o)) (vsp.toNat + 600) (sdData_val d)) (vsp.toNat + 624) (sdData_val d)) (vsp.toNat + 776) (swData (0#64))) (vsp.toNat + 612) (swData (BitVec.ofNat 64 (sz.toNat - 1)))) (vsp.toNat + 632) (swData (BitVec.ofNat 64 (sz.toNat - 1))) := by
    rw [hmem27, mem_afterNextPC, hmE26, hoff632]
  have hsl27 : Vsa.Sim.Code.SnprintfLoaded σ27.mem := by
    rw [hmem27, mem_afterNextPC]
    exact snprintf_w4_wr _ _ _ (by rw [hoff632]; omega) hsl26

  -- === 0x80005cb0: sw a6,24(sp) — _flags := 0x0208 (__SWR|__SSTR) ===
  obtain ⟨σ28, i28, hs28, hi28, hG28, hmem28, hobs28⟩ :=
    site_80005cb0_wp σ27 i27 (c.steps + 27) _ vmi27 (vsp + (592#64)) _
      hG27 hpc27 hmi27 hp27.2.2.2.2.2.2.2.2.2.1 hp27.2.2.2.1 hsl27 rfl (by rw [hoff616]; omega) (by rw [hoff616]; omega) (by rw [hoff616, htoh]; omega) (by rw [hoff616]; omega) hi27
  have hstep28 : Step ⟨σ27, i27, c.steps + 27⟩ ⟨σ28, i28, c.steps + 28⟩ := hs28
  have hpc28 : σ28.regs.get? Register.PC = some (0x80005cb4#64) := by
    have := obs_store_pc hobs28
    rwa [show BitVec.addInt (0x80005cb0#64) 4 = (0x80005cb4#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi28, hmi28⟩ := obs_store_minstret hobs28
  have hp28 := pins_store hobs28 (by rfl) hp27
  have hmE28 : σ28.mem = writeMap4 (writeMap4 (writeMap4 (writeMap4 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 792) (sdData_val vS1o)) (vsp.toNat + 808) (sdData_val wra0)) (vsp.toNat + 824) (sdData_val v)) (vsp.toNat + 832) (sdData_val va4o)) (vsp.toNat + 840) (sdData_val va5o)) (vsp.toNat + 848) (sdData_val va6o)) (vsp.toNat + 856) (sdData_val va7o)) (vsp.toNat + 800) (sdData_val vS0o)) (vsp.toNat + 600) (sdData_val d)) (vsp.toNat + 624) (sdData_val d)) (vsp.toNat + 776) (swData (0#64))) (vsp.toNat + 612) (swData (BitVec.ofNat 64 (sz.toNat - 1)))) (vsp.toNat + 632) (swData (BitVec.ofNat 64 (sz.toNat - 1)))) (vsp.toNat + 616) (swData (0xffffffffffff0208#64)) := by
    rw [hmem28, mem_afterNextPC, hmE27, hoff616]
  have hsl28 : Vsa.Sim.Code.SnprintfLoaded σ28.mem := by
    rw [hmem28, mem_afterNextPC]
    exact snprintf_w4_wr _ _ _ (by rw [hoff616]; omega) hsl27

  -- === 0x80005cb4: sd a3,0(sp) — va_list pointer copy ===
  obtain ⟨σ29, i29, hs29, hi29, hG29, hmem29, hobs29⟩ :=
    site_80005cb4_wp σ28 i28 (c.steps + 28) _ vmi28 (vsp + (592#64)) _
      hG28 hpc28 hmi28 hp28.2.2.2.2.2.2.2.2.2.1 hp28.2.2.2.2.1 hsl28 rfl (by rw [hoff592]; omega) (by rw [hoff592]; omega) (by rw [hoff592, htoh]; omega) (by rw [hoff592]; omega) hi28
  have hstep29 : Step ⟨σ28, i28, c.steps + 28⟩ ⟨σ29, i29, c.steps + 29⟩ := hs29
  have hpc29 : σ29.regs.get? Register.PC = some (0x80005cb8#64) := by
    have := obs_store_pc hobs29
    rwa [show BitVec.addInt (0x80005cb4#64) 4 = (0x80005cb8#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi29, hmi29⟩ := obs_store_minstret hobs29
  have hp29 := pins_store hobs29 (by rfl) hp28
  have hmE29 : σ29.mem = writeMap8 (writeMap4 (writeMap4 (writeMap4 (writeMap4 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 792) (sdData_val vS1o)) (vsp.toNat + 808) (sdData_val wra0)) (vsp.toNat + 824) (sdData_val v)) (vsp.toNat + 832) (sdData_val va4o)) (vsp.toNat + 840) (sdData_val va5o)) (vsp.toNat + 848) (sdData_val va6o)) (vsp.toNat + 856) (sdData_val va7o)) (vsp.toNat + 800) (sdData_val vS0o)) (vsp.toNat + 600) (sdData_val d)) (vsp.toNat + 624) (sdData_val d)) (vsp.toNat + 776) (swData (0#64))) (vsp.toNat + 612) (swData (BitVec.ofNat 64 (sz.toNat - 1)))) (vsp.toNat + 632) (swData (BitVec.ofNat 64 (sz.toNat - 1)))) (vsp.toNat + 616) (swData (0xffffffffffff0208#64))) (vsp.toNat + 592) (sdData_val ((vsp + (592#64)) + sign_extend (m := 64) (0x0e8#12))) := by
    rw [hmem29, mem_afterNextPC, hmE28, hoff592]
  have hsl29 : Vsa.Sim.Code.SnprintfLoaded σ29.mem := by
    rw [hmem29, mem_afterNextPC]
    exact snprintf_w8_wr _ _ _ (by rw [hoff592]; omega) hsl28

  -- === 0x80005cb8: jal ra,_svfprintf_r — the call ===
  obtain ⟨σ30, i30, hs30, hi30, hG30, hmem30, hobs30⟩ :=
    site_80005cb8_wp σ29 i29 (c.steps + 29) _ vmi29
      hG29 hpc29 hmi29 hsl29 rfl hi29
  have hstep30 : Step ⟨σ29, i29, c.steps + 29⟩ ⟨σ30, i30, c.steps + 30⟩ := hs30
  have hpc30 : σ30.regs.get? Register.PC = some (0x80007654#64) := by
    have := obs_jal_pc hobs30
    rwa [show (0x80005cb8#64 : BitVec 64) + sign_extend (m := 64) (0x00199c#21) = (0x80007654#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi30, hmi30⟩ := obs_jal_minstret hobs30
  have hrd30 : σ30.regs.get? Register.x1 = some ((0x80005cbc#64)) := by
    have := obs_jal_rd hobs30 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x80005cb8#64) 4 = (0x80005cbc#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp30 := pins_cons_pro hrd30 (pins_jal hobs30 (by rfl) (pins_drop11_pro hp29))
  have hmE30 : σ30.mem = writeMap8 (writeMap4 (writeMap4 (writeMap4 (writeMap4 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 792) (sdData_val vS1o)) (vsp.toNat + 808) (sdData_val wra0)) (vsp.toNat + 824) (sdData_val v)) (vsp.toNat + 832) (sdData_val va4o)) (vsp.toNat + 840) (sdData_val va5o)) (vsp.toNat + 848) (sdData_val va6o)) (vsp.toNat + 856) (sdData_val va7o)) (vsp.toNat + 800) (sdData_val vS0o)) (vsp.toNat + 600) (sdData_val d)) (vsp.toNat + 624) (sdData_val d)) (vsp.toNat + 776) (swData (0#64))) (vsp.toNat + 612) (swData (BitVec.ofNat 64 (sz.toNat - 1)))) (vsp.toNat + 632) (swData (BitVec.ofNat 64 (sz.toNat - 1)))) (vsp.toNat + 616) (swData (0xffffffffffff0208#64))) (vsp.toNat + 592) (sdData_val ((vsp + (592#64)) + sign_extend (m := 64) (0x0e8#12))) := hmem30.trans hmE29
  have hsl30 : Vsa.Sim.Code.SnprintfLoaded σ30.mem := by rw [hmem30]; exact hsl29

  have hPcur : Pin8 σ30.mem (vsp.toNat + 600) d := by
    rw [hmE30]
    refine pinw8_survives_writeMap8 _ _ (by omega) ?_
    refine pinw8_survives_writeMap4 _ _ (by omega) ?_
    refine pinw8_survives_writeMap4 _ _ (by omega) ?_
    refine pinw8_survives_writeMap4 _ _ (by omega) ?_
    refine pinw8_survives_writeMap4 _ _ (by omega) ?_
    refine pinw8_survives_writeMap8 _ _ (by omega) ?_
    exact Pin8_writeMap8 _ _ d
  have hPcap : Pin4 σ30.mem (vsp.toNat + 612) (BitVec.ofNat 32 (sz.toNat - 1)) := by
    rw [hmE30, show swData (BitVec.ofNat 64 (sz.toNat - 1)) = ((BitVec.ofNat 32 (sz.toNat - 1)) : BitVec (8 * 4)) from extract32_ofNat64 _]
    refine pinw4_survives_writeMap8 _ _ (by omega) ?_
    refine pinw4_survives_writeMap4 _ _ (by omega) ?_
    refine pinw4_survives_writeMap4 _ _ (by omega) ?_
    exact Pin4_writeMap4 _ _ _
  have hfl0N : σ30.mem[vsp.toNat + 616]? = some (0x08#8) := by
    rw [hmE30, getElem?_writeMap8_out _ (vsp.toNat + 592) _ _ (by omega)]
    rw [show ((0x08#8 : BitVec 8)) = (swData (0xffffffffffff0208#64)).extractLsb' 0 8 from by decide]
    exact getElem_writeMap4_0 _ _ _
  have hfl1N : σ30.mem[vsp.toNat + 617]? = some (0x02#8) := by
    rw [hmE30, getElem?_writeMap8_out _ (vsp.toNat + 592) _ _ (by omega)]
    rw [show ((0x02#8 : BitVec 8)) = (swData (0xffffffffffff0208#64)).extractLsb' 8 8 from by decide]
    exact getElem_writeMap4_1 _ _ _
  have hPva : Pin8 σ30.mem (vsp.toNat + 824) v := by
    rw [hmE30]
    refine pinw8_survives_writeMap8 _ _ (by omega) ?_
    refine pinw8_survives_writeMap4 _ _ (by omega) ?_
    refine pinw8_survives_writeMap4 _ _ (by omega) ?_
    refine pinw8_survives_writeMap4 _ _ (by omega) ?_
    refine pinw8_survives_writeMap4 _ _ (by omega) ?_
    refine pinw8_survives_writeMap8 _ _ (by omega) ?_
    refine pinw8_survives_writeMap8 _ _ (by omega) ?_
    refine pinw8_survives_writeMap8 _ _ (by omega) ?_
    refine pinw8_survives_writeMap8 _ _ (by omega) ?_
    refine pinw8_survives_writeMap8 _ _ (by omega) ?_
    refine pinw8_survives_writeMap8 _ _ (by omega) ?_
    refine pinw8_survives_writeMap8 _ _ (by omega) ?_
    exact Pin8_writeMap8 _ _ v
  have hS0c8 : SlotHolds (vsp + (592#64)) 0x0c8 vS1o σ30.mem := by
    rw [hmE30]
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff792]; omega) ?_
    refine slot_survives_writeMap4 _ _ _ _ _ _ (by rw [hoff792]; omega) ?_
    refine slot_survives_writeMap4 _ _ _ _ _ _ (by rw [hoff792]; omega) ?_
    refine slot_survives_writeMap4 _ _ _ _ _ _ (by rw [hoff792]; omega) ?_
    refine slot_survives_writeMap4 _ _ _ _ _ _ (by rw [hoff792]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff792]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff792]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff792]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff792]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff792]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff792]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff792]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff792]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff792]; omega) ?_
    exact slot_save (vsp + (592#64)) 0x0c8 vS1o _ _ _ hoff792 rfl
  have hS0d8 : SlotHolds (vsp + (592#64)) 0x0d8 wra0 σ30.mem := by
    rw [hmE30]
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff808]; omega) ?_
    refine slot_survives_writeMap4 _ _ _ _ _ _ (by rw [hoff808]; omega) ?_
    refine slot_survives_writeMap4 _ _ _ _ _ _ (by rw [hoff808]; omega) ?_
    refine slot_survives_writeMap4 _ _ _ _ _ _ (by rw [hoff808]; omega) ?_
    refine slot_survives_writeMap4 _ _ _ _ _ _ (by rw [hoff808]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff808]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff808]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff808]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff808]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff808]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff808]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff808]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff808]; omega) ?_
    exact slot_save (vsp + (592#64)) 0x0d8 wra0 _ _ _ hoff808 rfl
  have hS0d0 : SlotHolds (vsp + (592#64)) 0x0d0 vS0o σ30.mem := by
    rw [hmE30]
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff800]; omega) ?_
    refine slot_survives_writeMap4 _ _ _ _ _ _ (by rw [hoff800]; omega) ?_
    refine slot_survives_writeMap4 _ _ _ _ _ _ (by rw [hoff800]; omega) ?_
    refine slot_survives_writeMap4 _ _ _ _ _ _ (by rw [hoff800]; omega) ?_
    refine slot_survives_writeMap4 _ _ _ _ _ _ (by rw [hoff800]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff800]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff800]; omega) ?_
    exact slot_save (vsp + (592#64)) 0x0d0 vS0o _ _ _ hoff800 rfl
  have hagN : ∀ a : Nat, ¬(vsp.toNat + 592 ≤ a ∧ a < vsp.toNat + 864) →
      σ30.mem[a]? = c.σ.mem[a]? := by
    intro a hw
    rw [hmE30,
      getElem?_writeMap8_out _ (vsp.toNat + 592) _ a (by omega),
      getElem?_writeMap4_out_pro _ (vsp.toNat + 616) _ a (by omega),
      getElem?_writeMap4_out_pro _ (vsp.toNat + 632) _ a (by omega),
      getElem?_writeMap4_out_pro _ (vsp.toNat + 612) _ a (by omega),
      getElem?_writeMap4_out_pro _ (vsp.toNat + 776) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 624) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 600) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 800) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 856) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 848) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 840) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 832) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 824) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 808) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 792) _ a (by omega)]
  refine ⟨⟨σ30, i30, c.steps + 30⟩, ?_,
    hG30,
    hpc30,
    hp30.1,
    hp30.2.2.2.2.2.2.2.2.2.2.1,
    hp30.2.2.2.2.2.2.2.2.2.2.2.1,
    hp30.2.2.2.1,
    hp30.2.2.2.2.2.2.2.2.1,
    hp30.2.2.1,
    hp30.2.1,
    hp30.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp30.2.2.2.2.2.1,
    hp30.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp30.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp30.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp30.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp30.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp30.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp30.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp30.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp30.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp30.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hPcur,
    hPcap,
    hfl0N,
    hfl1N,
    hPva,
    hS0c8,
    hS0d0,
    hS0d8,
    hagN,
    hsl30,
    hi30,
    ⟨vmi30, hmi30⟩⟩
  exact (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans ((Steps.single hstep4).trans ((Steps.single hstep5).trans ((Steps.single hstep6).trans ((Steps.single hstep7).trans ((Steps.single hstep8).trans ((Steps.single hstep9).trans ((Steps.single hstep10).trans ((Steps.single hstep11).trans ((Steps.single hstep12).trans ((Steps.single hstep13).trans ((Steps.single hstep14).trans ((Steps.single hstep15).trans ((Steps.single hstep16).trans ((Steps.single hstep17).trans ((Steps.single hstep18).trans ((Steps.single hstep19).trans ((Steps.single hstep20).trans ((Steps.single hstep21).trans ((Steps.single hstep22).trans ((Steps.single hstep23).trans ((Steps.single hstep24).trans ((Steps.single hstep25).trans ((Steps.single hstep26).trans ((Steps.single hstep27).trans ((Steps.single hstep28).trans ((Steps.single hstep29).trans (Steps.single hstep30)))))))))))))))))))))))))))))

end Vsa.Sim
