import Vsa.Sim.SnprintfSpec39
import Vsa.Sim.SnprintfSpec41

/-!
# M3 Layer-3 — `SnprintfSpec42` : the `snprintf("%lld")` WRAPPER capstone
## `0x80005c44` (snprintf ABI entry) → snprintf's `ret`, byte-for-byte `intToString`

The composed chain

    snprintfPreCall_spec   (Spec40 : entry → the `jal _svfprintf_r`, FILE
                            struct + va area built on the wrapper frame)
  ≫ svfprintf_lld_spec     (Spec38 : the full verified svfprintf `%lld` body)
  ≫ snprintfPostCall_spec  (Spec41 : return checks, the NUL terminator,
                            epilogue, `ret`)

restated byte-for-byte through `svfprintf_buffer_eq_intToString` (Spec39):
from `snprintf(d, sz, "%lld", v)` — `a0 = d` the caller's buffer, `a1 = sz`
the size, `a2 = 0x800192c0` the static `"%lld"` (pinned by `LldFmtLoaded`),
`a3 = v` the (negative, multi-digit) long long — `Steps` to snprintf's `ret`
with

* `a0 = ofNat ubytes.length` where `ubytes = (intToString v.toInt).toUTF8`
  bytes (snprintf returns svfprintf's total unchanged);
* the caller buffer `[d, d + ubytes.length)` = `ubytes`, byte for byte,
  **plus the NUL terminator** at `d + ubytes.length` (the C-string contract);
* `sp`/`ra`/callee-saves restored, `PC = x1 = wra0`;
* a pointwise frame outside the wrapper+svfprintf stack `[vsp−88, vsp+864)`
  and the written buffer `[d, d + ubytes.length + 1)`.

## Residual hypotheses (honest ledger)

* value ghost `hneg` — `v` negative, ANY magnitude (the nonneg
  and single-digit fast-path arms are separate, unverified paths);
* the static-image pins: `.rodata`/`.data` constants (`decimal_point` string
  + pointer, locale fn pointer, `__mb_cur_max`, the `'d'` parse-table slot,
  `_impure_ptr`) and the code-range `*Loaded` predicates;
* layout: the svfprintf frame base `vsp` (`sp_entry = vsp + 864`) in stack
  RAM above `0x8001c100`, 8-aligned; the caller buffer `d` above
  `0x8001c000` with 22 writable bytes, disjoint from the stack frames;
* `23 ≤ sz < 2^31` (enough capacity for the up-to-21-byte rendering; the
  truncating arms are not on this path), and `wra0` 4-aligned.
-/

open Vsa Vsa.Sim Vsa.While
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Sim.Code (SvfprintfSliceLoaded SvfprintfSlice2Loaded FlushPinsLoaded MemmoveLoaded
  __ssprint_rLoaded __locale_mb_cur_maxLoaded __ascii_mbtowcLoaded __hidden___udivdi3Loaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- **The `snprintf("%lld")` wrapper capstone** — snprintf ABI entry to `ret`,
negative multi-digit argument: the caller buffer holds
`(intToString v.toInt).toUTF8 ++ [0]`, `a0` = the byte length.
See the module docstring for the residual-hypothesis ledger. -/
theorem snprintf_lld_spec
    (vsp wra0 d sz v : BitVec 64)
    (va4o va5o va6o va7o : BitVec 64)
    (vS0o vS1o vS2o vS3o vS4o vS5o vS6o vS7o vS8o vS9o vS10o vS11o : BitVec 64)
    (c : Config)
    (hG : GoodState c.σ)
    -- code / static-code pins at entry (link-time constants of the image)
    (hsnp0 : Vsa.Sim.Code.SnprintfLoaded c.σ.mem)
    (hfmtL0 : Vsa.Sim.Code.LldFmtLoaded c.σ.mem)
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
    -- ABI entry registers: snprintf(d, sz, "%lld", v)
    (hpc : c.σ.regs.get? Register.PC = some (0x80005c44#64))
    (hx1 : c.σ.regs.get? Register.x1 = some wra0)
    (hx2 : c.σ.regs.get? Register.x2 = some (vsp + (864#64)))
    (hx3 : c.σ.regs.get? Register.x3 = some (0x8001b510#64))
    (hx10 : c.σ.regs.get? Register.x10 = some d)
    (hx11 : c.σ.regs.get? Register.x11 = some sz)
    (hx12 : c.σ.regs.get? Register.x12 = some (0x800192c0#64))
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
    -- static data (link-time constants, as Spec38 + the _impure_ptr)
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
    (himp0 : c.σ.mem[(0x8001b970 : Nat)]? = some (0x38#8))
    (himp1 : c.σ.mem[(0x8001b970 : Nat) + 1]? = some (0xb5#8))
    (himp2 : c.σ.mem[(0x8001b970 : Nat) + 2]? = some (0x01#8))
    (himp3 : c.σ.mem[(0x8001b970 : Nat) + 3]? = some (0x80#8))
    (himp4 : c.σ.mem[(0x8001b970 : Nat) + 4]? = some (0x00#8))
    (himp5 : c.σ.mem[(0x8001b970 : Nat) + 5]? = some (0x00#8))
    (himp6 : c.σ.mem[(0x8001b970 : Nat) + 6]? = some (0x00#8))
    (himp7 : c.σ.mem[(0x8001b970 : Nat) + 7]? = some (0x00#8))
    -- size guards (no truncation on this path)
    (hsz23 : 23 ≤ sz.toNat)
    (hszhi : sz.toNat < 2 ^ 31)
    -- the argument-value ghosts: negative, magnitude > 9
    (hneg : zopz0zKzJ_s v (0#64) = false)
    -- layout
    (hsplo : 0x8001c100 ≤ vsp.toNat)
    (hsphi : vsp.toNat + 864 ≤ 0x100000000)
    (hspal : vsp.toNat % 8 = 0)
    (hdge : 0x8001c000 ≤ d.toNat)
    (hdhi : d.toNat + 22 ≤ 0x100000000)
    (hdstk : vsp.toNat + 864 ≤ d.toNat ∨ d.toNat + 22 ≤ vsp.toNat - 128)
    (hwra : wra0.toNat % 4 = 0)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
    -- the UTF-8 byte list of the mathematical rendering
    ∃ ubytes : List UInt8,
      ubytes = (intToString v.toInt).toUTF8.data.toList ∧
      -- return: PC = ra = the caller's return address, sp restored
      c'.σ.regs.get? Register.PC = some wra0 ∧
      c'.σ.regs.get? Register.x1 = some wra0 ∧
      c'.σ.regs.get? Register.x2 = some (vsp + (864#64)) ∧
      -- **a0 = the byte length (svfprintf's total, returned unchanged)**
      c'.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 ubytes.length) ∧
      -- callee-saves restored to the entry values
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
      -- **the NUL terminator** (the C-string contract)
      c'.σ.mem[d.toNat + ubytes.length]? = some (0x00#8) ∧
      -- pointwise frame back to the ABI-entry memory
      (∀ a : Nat, ¬(vsp.toNat - 88 ≤ a ∧ a < vsp.toNat + 864) →
        ¬(d.toNat ≤ a ∧ a < d.toNat + ubytes.length + 1) →
        c'.σ.mem[a]? = c.σ.mem[a]?) ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hvf : ((0x800192c0#64 : BitVec 64)).toNat = 0x800192c0 := rfl
  have h592 : ((vsp + (592#64)) : BitVec 64).toNat = vsp.toNat + 592 := by
    rw [BitVec.toNat_add, show ((592#64 : BitVec 64)).toNat = 592 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  have hoff600 : ((vsp + (592#64)) + sign_extend (m := 64) (0x008#12)).toNat
      = vsp.toNat + 600 := by
    rw [ptr_addoff (vsp + (592#64)) _ 8 (by decide) (by rw [h592]; omega), h592]
  have hoff824 : ((vsp + (592#64)) + sign_extend (m := 64) (0x0e8#12)).toNat
      = vsp.toNat + 824 := by
    rw [ptr_addoff (vsp + (592#64)) _ 232 (by decide) (by rw [h592]; omega), h592]
  have hoff792 : ((vsp + (592#64)) + sign_extend (m := 64) (0x0c8#12)).toNat
      = vsp.toNat + 792 := by
    rw [ptr_addoff (vsp + (592#64)) _ 200 (by decide) (by rw [h592]; omega), h592]
  have hoff800 : ((vsp + (592#64)) + sign_extend (m := 64) (0x0d0#12)).toNat
      = vsp.toNat + 800 := by
    rw [ptr_addoff (vsp + (592#64)) _ 208 (by decide) (by rw [h592]; omega), h592]
  have hoff808 : ((vsp + (592#64)) + sign_extend (m := 64) (0x0d8#12)).toNat
      = vsp.toNat + 808 := by
    rw [ptr_addoff (vsp + (592#64)) _ 216 (by decide) (by rw [h592]; omega), h592]
  -- ============ stage 1: the pre-call wrapper body (Spec40) ============
  obtain ⟨c1, hs1, hG1, hpc1, h1x1, h1x2, h1x3, h1x8, h1x9, h1x10, h1x11, h1x12, h1x13,
      h1x18, h1x19, h1x20, h1x21, h1x22, h1x23, h1x24, h1x25, h1x26, h1x27,
      hPcur, hPcap, hfl0N, hfl1N, hPva, hS0c8, hS0d0, hS0d8, hag1, hsl1, htk1, hmi1⟩ :=
    snprintfPreCall_spec vsp wra0 d sz (0x800192c0#64) v va4o va5o va6o va7o
      vS0o vS1o vS2o vS3o vS4o vS5o vS6o vS7o vS8o vS9o vS10o vS11o c hG hsnp0
      hpc hx2 hx1 hx3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx8 hx9
      hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27
      himp0 himp1 himp2 himp3 himp4 himp5 himp6 himp7
      hsz23 hszhi hsplo hsphi hspal htick
  -- agreement below the stack for the code/static transports
  have hagLow1 : ∀ a : Nat, a < 0x8001c000 → c1.σ.mem[a]? = c.σ.mem[a]? :=
    fun a ha => hag1 a (by omega)
  -- the fmt bytes at c1 (static .rodata, pinned by LldFmtLoaded)
  obtain ⟨hf0, hf1, hf2, hf3, hf4, _, _, _⟩ := Vsa.Sim.Code.lldFmt_bytes hfmtL0
  -- the spilled va-area value bytes (Pin8 unpacked)
  obtain ⟨hva0, hva1, hva2, hva3, hva4, hva5, hva6, hva7⟩ := hPva
  -- llArg of the spilled bytes IS v
  have hllv : llArg ((sdData_val v).extractLsb' 0 8) ((sdData_val v).extractLsb' 8 8)
      ((sdData_val v).extractLsb' 16 8) ((sdData_val v).extractLsb' 24 8)
      ((sdData_val v).extractLsb' 32 8) ((sdData_val v).extractLsb' 40 8)
      ((sdData_val v).extractLsb' 48 8) ((sdData_val v).extractLsb' 56 8) = v :=
    (pinw8_sext_reassemble (sdData_val v)).trans (sdData_val_id v)
  -- ============ stage 2: the full svfprintf %lld body (Spec38) ============
  obtain ⟨c2, hs2, hG2, n2, bs2, hn2a, hn2b, hub, hlb, hbs2f,
      hpc2, h2x1, h2x2, h2x10, h2x8, h2x9, h2x18, h2x19, h2x20, h2x21, h2x22, h2x23,
      h2x24, h2x25, h2x26, h2x27, hsignB, hdigB, hcurP, hcapP, hframe2, htk2, hmi2⟩ :=
    svfprintf_lld_spec vsp (0x80005cbc#64) (0x8001b538#64)
      ((vsp + (592#64)) + sign_extend (m := 64) (0x008#12))
      (0x800192c0#64)
      ((vsp + (592#64)) + sign_extend (m := 64) (0x0e8#12))
      d
      sz (0x8001b538#64) vS2o vS3o vS4o vS5o vS6o vS7o vS8o vS9o vS10o vS11o
      (0x08#8) (0x02#8) (BitVec.ofNat 32 (sz.toNat - 1))
      ((sdData_val v).extractLsb' 0 8) ((sdData_val v).extractLsb' 8 8)
      ((sdData_val v).extractLsb' 16 8) ((sdData_val v).extractLsb' 24 8)
      ((sdData_val v).extractLsb' 32 8) ((sdData_val v).extractLsb' 40 8)
      ((sdData_val v).extractLsb' 48 8) ((sdData_val v).extractLsb' 56 8)
      c1 hG1
      (svfSlice_of_agree_rt (fun a h1 h2 => hagLow1 a (by omega)) hsl0)
      (slice2_of_agree_37 (fun a h1 h2 => hagLow1 a (by omega)) hsl20)
      (localeconv_of_agree_wr hagLow1 hlc0)
      (strlen_of_agree_wr hagLow1 hstr0)
      (memset_of_agree_wr hagLow1 hms0)
      (locale_of_agree_rt (fun a h1 h2 => hagLow1 a (by omega)) hlm0)
      (amb_of_agree_rt (fun a h1 h2 => hagLow1 a (by omega)) hamb0)
      (umoddi3_of_agree_37 (fun a h => hagLow1 a (by omega)) hum0)
      (cudivdi3_of_agree_37 (fun a h => hagLow1 a (by omega)) hud0)
      (flushPins_of_agree_rt (fun a h1 h2 => hagLow1 a (by omega)) hfp0)
      (armPins_of_agree_43 (fun a h => hagLow1 a (by omega)) hap0)
      (parseSlot_of_agree_37 0x64 _ (by omega) hagLow1 hslot0)
      (ssprint_of_agree_wr hagLow1 hsspL0)
      (ssputs_of_agree_wr hagLow1 hsspuL0)
      (memmove_of_agree_wr hagLow1 hmvL0)
      hpc1 h1x2 h1x1 h1x3 h1x10 h1x11 h1x12 h1x13 h1x8 h1x9 h1x22 h1x18 h1x19
      h1x20 h1x21 h1x23 h1x24 h1x25 h1x26 h1x27
      ((hagLow1 _ (by omega)).trans hdp0) ((hagLow1 _ (by omega)).trans hdp1)
      ((hagLow1 _ (by omega)).trans hdp2) ((hagLow1 _ (by omega)).trans hdp3)
      ((hagLow1 _ (by omega)).trans hdp4) ((hagLow1 _ (by omega)).trans hdp5)
      ((hagLow1 _ (by omega)).trans hdp6) ((hagLow1 _ (by omega)).trans hdp7)
      ((hagLow1 _ (by omega)).trans hdb0) ((hagLow1 _ (by omega)).trans hdb1)
      ((hagLow1 _ (by omega)).trans hdb2) ((hagLow1 _ (by omega)).trans hdb3)
      ((hagLow1 _ (by omega)).trans hdb4) ((hagLow1 _ (by omega)).trans hdb5)
      ((hagLow1 _ (by omega)).trans hdb6) ((hagLow1 _ (by omega)).trans hdb7)
      ((hagLow1 _ (by omega)).trans hfn0) ((hagLow1 _ (by omega)).trans hfn1)
      ((hagLow1 _ (by omega)).trans hfn2) ((hagLow1 _ (by omega)).trans hfn3)
      ((hagLow1 _ (by omega)).trans hfn4) ((hagLow1 _ (by omega)).trans hfn5)
      ((hagLow1 _ (by omega)).trans hfn6) ((hagLow1 _ (by omega)).trans hfn7)
      ((hagLow1 _ (by omega)).trans hmbB)
      ((hagLow1 _ (by omega)).trans htb0) ((hagLow1 _ (by omega)).trans htb1)
      ((hagLow1 _ (by omega)).trans htb2) ((hagLow1 _ (by omega)).trans htb3)
      (by rw [hvf]; exact (hagLow1 _ (by omega)).trans hf0)
      (by rw [hvf]; exact (hagLow1 _ (by omega)).trans hf1)
      (by rw [hvf]; exact (hagLow1 _ (by omega)).trans hf2)
      (by rw [hvf]; exact (hagLow1 _ (by omega)).trans hf3)
      (by rw [hvf]; exact (hagLow1 _ (by omega)).trans hf4)
      (by rw [hoff600]; exact hfl0N) (by rw [hoff600]; exact hfl1N)
      (by decide) (by decide)
      (by rw [hoff600]; exact hPcur)
      (by rw [hoff600]; exact hPcap)
      (by rw [BitVec.toNat_ofNat]; omega) (by rw [BitVec.toNat_ofNat]; omega)
      (by rw [hoff824]; exact hva0) (by rw [hoff824]; exact hva1)
      (by rw [hoff824]; exact hva2) (by rw [hoff824]; exact hva3)
      (by rw [hoff824]; exact hva4) (by rw [hoff824]; exact hva5)
      (by rw [hoff824]; exact hva6) (by rw [hoff824]; exact hva7)
      (by rw [hoff824]; omega) (by rw [hoff824]; omega)
      (Or.inr (by rw [hoff824, htoh]; omega))
      (by rw [hoff824]; omega)
      (Or.inr (by rw [hoff824]; omega))
      (by rw [hllv]; exact hneg)
      (by rw [hoff600]; omega) (by rw [hoff600]; omega) (by rw [hoff600]; omega)
      (by rw [hvf]; omega) (by rw [hvf]; omega)
      (Or.inl (by rw [hvf, htoh]; omega))
      (Or.inl (by rw [hvf]; omega))
      (Or.inl (by rw [hvf]; omega))
      (Or.inl (by rw [hvf, hoff600]; omega))
      (by omega) (by omega) hspal
      (by omega) (by omega)
      (hdstk.elim (fun h => Or.inl (by omega)) (fun h => Or.inr (by omega)))
      (hdstk.elim (fun h => Or.inl (by rw [hoff600]; omega))
                  (fun h => Or.inr (by rw [hoff600]; omega)))
      (by decide) htk1
  -- rewrite the value ghosts of the conclusion in terms of v
  rw [hllv] at hub hlb hbs2f
  -- ============ stage 3: the post-call return path (Spec41) ============
  -- agreement below the stack across the svfprintf body
  have hagLow2 : ∀ a : Nat, a < 0x8001c000 → c2.σ.mem[a]? = c1.σ.mem[a]? :=
    fun a ha => hframe2 a (by omega) (by omega)
      (by rw [hoff600]; omega) (by rw [hoff600]; omega)
  have hsnp2 : Vsa.Sim.Code.SnprintfLoaded c2.σ.mem :=
    snprintf_of_agree_wr hagLow2 hsl1
  -- the updated cursor value and its bounds
  have hvcN : (d + BitVec.ofNat 64 (1 + n2)).toNat = d.toNat + 1 + n2 := by
    have hdlt := d.isLt
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  -- the three save slots survive the svfprintf body (outside all four windows)
  have hS0c8₂ : SlotHolds (vsp + (592#64)) 0x0c8 vS1o c2.σ.mem :=
    slotHolds_of_agree_rt _ _ _ (vsp.toNat + 792) _ _ hoff792
      (fun a h1 h2 => hframe2 a (by omega)
        (hdstk.elim (fun h => by omega) (fun h => by omega))
        (by rw [hoff600]; omega) (by rw [hoff600]; omega)) hS0c8
  have hS0d0₂ : SlotHolds (vsp + (592#64)) 0x0d0 vS0o c2.σ.mem :=
    slotHolds_of_agree_rt _ _ _ (vsp.toNat + 800) _ _ hoff800
      (fun a h1 h2 => hframe2 a (by omega)
        (hdstk.elim (fun h => by omega) (fun h => by omega))
        (by rw [hoff600]; omega) (by rw [hoff600]; omega)) hS0d0
  have hS0d8₂ : SlotHolds (vsp + (592#64)) 0x0d8 wra0 c2.σ.mem :=
    slotHolds_of_agree_rt _ _ _ (vsp.toNat + 808) _ _ hoff808
      (fun a h1 h2 => hframe2 a (by omega)
        (hdstk.elim (fun h => by omega) (fun h => by omega))
        (by rw [hoff600]; omega) (by rw [hoff600]; omega)) hS0d8
  rw [hoff600] at hcurP
  obtain ⟨c3, hs3, hG3, hpc3, h3x1, h3x2, h3x10, h3x8, h3x9,
      h3x18, h3x19, h3x20, h3x21, h3x22, h3x23, h3x24, h3x25, h3x26, h3x27,
      hmem3, hsl3, htk3, hmi3⟩ :=
    snprintfPostCall_spec vsp wra0 (d + BitVec.ofNat 64 (1 + n2)) sz
      (BitVec.ofNat 64 (1 + n2))
      vS0o vS1o vS2o vS3o vS4o vS5o vS6o vS7o vS8o vS9o vS10o vS11o c2 hG2 hsnp2
      hpc2 h2x2 h2x10 h2x8
      h2x18 h2x19 h2x20 h2x21 h2x22 h2x23 h2x24 h2x25 h2x26 h2x27
      hcurP hS0c8₂ hS0d0₂ hS0d8₂
      (by rw [BitVec.toNat_ofNat]; omega)
      (by omega)
      (by rw [hvcN]; omega)
      (by rw [hvcN]; omega)
      (hdstk.elim (fun h => Or.inr (by rw [hvcN]; omega))
                  (fun h => Or.inl (by rw [hvcN]; omega)))
      hwra hsplo hsphi hspal htk2
  -- ============ final assembly: byte-for-byte intToString ============
  have hbytes : signByte :: (List.range n2).map bs2
      = (intToString v.toInt).toUTF8.data.toList.map (fun u => u.toBitVec) :=
    svfprintf_buffer_eq_intToString v n2 bs2 hneg hn2a hbs2f hub hlb
  have hlen : (intToString v.toInt).toUTF8.data.toList.length = 1 + n2 := by
    have h := congrArg List.length hbytes
    rw [List.length_cons, List.length_map, List.length_range, List.length_map] at h
    omega
  -- reads at c3 away from the NUL byte fall through to c2
  have hins : ∀ a : Nat, a ≠ d.toNat + 1 + n2 → c3.σ.mem[a]? = c2.σ.mem[a]? := by
    intro a hne
    rw [hmem3, Std.ExtHashMap.getElem?_insert,
      if_neg (by simp only [beq_iff_eq]; rw [hvcN]; exact fun h => hne h.symm)]
  -- the NUL byte itself
  have hnulB : c3.σ.mem[d.toNat + (1 + n2)]? = some (0x00#8) := by
    rw [show d.toNat + (1 + n2) = d.toNat + 1 + n2 from by omega]
    rw [hmem3, Std.ExtHashMap.getElem?_insert,
      if_pos (by simp only [beq_iff_eq]; rw [hvcN]),
      show stData 1 (0#64) = (0x00#8) from by decide]
  refine ⟨c3, (hs1.trans hs2).trans hs3, hG3,
    (intToString v.toInt).toUTF8.data.toList, rfl,
    hpc3, h3x1, h3x2, (by rw [hlen]; exact h3x10),
    h3x8, h3x9, h3x18, h3x19, h3x20, h3x21, h3x22, h3x23, h3x24, h3x25, h3x26, h3x27,
    ?_, (by rw [hlen]; exact hnulB), ?_, htk3, hmi3⟩
  · -- byte-for-byte in the caller buffer
    intro k hk
    have hk' : k < 1 + n2 := by rwa [hlen] at hk
    have hget : (intToString v.toInt).toUTF8.data.toList[k].toBitVec
        = (signByte :: (List.range n2).map bs2)[k]'(by
            rw [List.length_cons, List.length_map, List.length_range]; omega) := by
      have hmapg : ((intToString v.toInt).toUTF8.data.toList.map
          (fun u => u.toBitVec))[k]'(by rw [List.length_map, hlen]; omega)
          = (intToString v.toInt).toUTF8.data.toList[k].toBitVec :=
        List.getElem_map _
      rw [← hmapg]
      exact List.getElem_of_eq hbytes.symm _
    rw [hget]
    cases k with
    | zero =>
      rw [hins _ (by omega)]
      simpa using hsignB
    | succ j =>
      have hj : j < n2 := by omega
      have hcons : (signByte :: (List.range n2).map bs2)[j + 1]'(by simp; omega)
          = bs2 j := by
        simp [List.getElem_map, List.getElem_range]
      rw [hcons, show d.toNat + (j + 1) = d.toNat + 1 + j from by omega,
        hins _ (by omega)]
      exact hdigB j hj
  · -- the pointwise frame back to the ABI-entry memory
    intro a hW1 hW2
    rw [hlen] at hW2
    rw [hins a (by omega)]
    exact ((hframe2 a (by omega) (by omega) (by rw [hoff600]; omega)
        (by rw [hoff600]; omega)).trans (hag1 a (by omega)))

end Vsa.Sim
